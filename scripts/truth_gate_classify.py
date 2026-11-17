#!/usr/bin/env python3
# Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Benjamin Stanley Frohman
#
# Truth Gate failure classifier (see TRUTH_GATE.md, section "Failure classes").
#
# The gate must never describe a lock-wording problem as a proof failure. This script
# sorts every Truth Gate failure into exactly one class and explains it:
#
#   KERNEL/PROOF  lake build fails, sorry/admit/native_decide/axiom in the sources, nonstandard
#                 axioms, a missing or ill-typed locked declaration, or intended_correspondence
#                 fails to check. This is the ONLY class ever described as a proof failure.
#   LOCK-FORM     the lock is written wrongly (repository Props or definitions inside paper_claim
#                 instead of an independent transcription, a vacuous alias, an rfl correspondence,
#                 a partial lock, an edited locked statement, missing quote/section fields).
#                 Printed as "lock wording/form problem, not a math failure".
#   PAPER-HASH    the paper file changed after the lock was written. Prints which lines changed
#                 (for example copyright only) and the exact hash update that is required.
#   STALE-BASE    a pull request was evaluated against an older main than the current one, and
#                 main has since changed the lock, a Semantics file, a paper, or the gate scripts.
#
# Subcommands
#   lint                 static lock-form lint of paper_claim (no Lean needed; runs on every PR)
#   paper-diff           diff summary for every paper whose sha256 no longer matches its lock
#   stale-base           PR context check; re-merges the PR head onto the current base if stale
#   report               read truth-gate-report/*, print the classified verdict, set exit code
#
# Exit codes: 0 pass, 1 fail (the verdict lists the classes), 3 usage error.
import argparse, difflib, hashlib, json, os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.environ.get("TRUTH_GATE_ROOT") or os.path.dirname(HERE)
REPORT = os.path.join(ROOT, "truth-gate-report")
LOCK_NAMES = ["TRUTH_GATE.lock"]
VOCAB_FILE = "TRUTH_GATE.vocabulary.json"

NOT_MATH = "lock wording/form problem, not a math failure"

# ----------------------------------------------------------------------------- helpers

def sha256_file(p):
    with open(p, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()

def sha256_bytes(b):
    return hashlib.sha256(b).hexdigest()

def read(p):
    with open(p, encoding="utf-8", errors="replace") as f:
        return f.read()

def git(*args, cwd=None, check=False):
    r = subprocess.run(["git", *args], cwd=cwd or ROOT, capture_output=True, text=True)
    if check and r.returncode != 0:
        raise RuntimeError(f"git {' '.join(args)}: {r.stderr.strip()}")
    return r

def git_top():
    r = git("rev-parse", "--show-toplevel")
    return r.stdout.strip() if r.returncode == 0 else ROOT

def load_lock():
    for n in LOCK_NAMES:
        p = os.path.join(ROOT, n)
        if os.path.isfile(p):
            return n, json.load(open(p, encoding="utf-8"))
    return None, None

def mask_comments_strings(src):
    """Replace comments and string literals by spaces, keeping offsets and newlines."""
    out, i, n, depth = list(src), 0, len(src), 0
    def blank(a, b):
        for k in range(a, min(b, n)):
            if out[k] != "\n":
                out[k] = " "
    while i < n:
        if src.startswith("/-", i):
            j, depth = i + 2, 1
            while j < n and depth:
                if src.startswith("/-", j): depth += 1; j += 2; continue
                if src.startswith("-/", j): depth -= 1; j += 2; continue
                j += 1
            blank(i, j); i = j; continue
        if src.startswith("--", i):
            j = src.find("\n", i); j = n if j < 0 else j
            blank(i, j); i = j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            blank(i + 1, j); i = j + 1; continue
        i += 1
    return "".join(out)

def line_of(src, off):
    return src.count("\n", 0, off) + 1

IDENT = re.compile(r"«[^»]+»|[A-Za-z_\u0370-\u03ff\u1f00-\u1fff\u2100-\u214f\U0001d400-\U0001d7ff]"
                   r"[\w'!?\u0370-\u03ff\u1f00-\u1fff\u2080-\u209c\u2100-\u214f\U0001d400-\U0001d7ff]*"
                   r"(?:\.(?:«[^»]+»|[A-Za-z_\u0370-\u03ff][\w'!?\u0370-\u03ff\u2080-\u209c]*))*")
DECL = re.compile(r"^[ \t]*(?:@\[[^\]]*\][ \t\n]*)?(?:(?:private|protected|noncomputable|partial|unsafe|"
                  r"nonrec|public)[ \t]+)*(def|abbrev|theorem|lemma|structure|class|inductive|instance|"
                  r"opaque|axiom|irreducible_def)[ \t]+(«[^»]+»|[^\s:({\[⦃]+)", re.M)
KEYWORDS = set("""fun λ let have show from by at with match if then else do return Type Sort Prop
                  forall exists in this where deriving open namespace end section variable""".split())

def lean_files(paths, drafts=()):
    out = []
    for r in paths:
        base = os.path.join(ROOT, r)
        if os.path.isfile(base):
            out.append(base); continue
        for dp, dn, fs in os.walk(base):
            dn[:] = [d for d in dn if d not in (".lake", "lake-packages", ".git")]
            for f in fs:
                if f.endswith(".lean"):
                    out.append(os.path.join(dp, f))
    return sorted(set(out))

CORE_PACKAGES = {"mathlib", "batteries", "std", "aesop", "qq", "proofwidgets", "importgraph",
                 "leansearchclient", "plausible", "cli", "lean4-cli"}

def author_dependency_dirs(fetch=False):
    """Source dirs of the non-Mathlib Lake dependencies (the author's own packages). Their
    definitions count as repository definitions for the lint. Uses .lake/packages when present;
    with fetch=True, shallow-fetches the exact manifest revision into truth-gate-report/deps."""
    mp = os.path.join(ROOT, "lake-manifest.json")
    if not os.path.isfile(mp):
        return []
    out = []
    for pk in json.load(open(mp)).get("packages", []):
        name = pk.get("name", "")
        if name.lower() in CORE_PACKAGES:
            continue
        local = os.path.join(ROOT, ".lake", "packages", name)
        if pk.get("type") == "path" and pk.get("dir"):
            local = os.path.normpath(os.path.join(ROOT, pk["dir"]))
        if os.path.isdir(local):
            out.append((name, local)); continue
        if fetch and pk.get("url") and pk.get("rev"):
            dest = os.path.join(REPORT, "deps", name)
            if not os.path.isdir(os.path.join(dest, ".git")):
                os.makedirs(dest, exist_ok=True)
                for cmd in (["init", "-q"], ["remote", "add", "origin", pk["url"]],
                            ["fetch", "-q", "--depth", "1", "origin", pk["rev"]], ["checkout", "-q", "FETCH_HEAD"]):
                    git(*cmd, cwd=dest)
            if os.path.isdir(dest):
                out.append((name, dest))
        else:
            print(f"TRUTH GATE LINT NOTE: dependency {name} is not available locally; its definitions are "
                  "not checked (run with --fetch-deps or after `lake exe cache get`)")
    return out

FETCH_DEPS = False

def repo_declarations(lock):
    """short name -> list of (full name, file, line, kind, is_prop_valued)."""
    roots = list(lock.get("lean_roots", []))
    sems = [lock.get("semantics_file")] + [x.get("semantics_file") for x in lock.get("additional_locks", [])]
    decls = {}
    files = [(p, os.path.relpath(p, ROOT)) for p in lean_files(roots + [s for s in sems if s])]
    for name, d in author_dependency_dirs(FETCH_DEPS):
        for dp, dn, fs in os.walk(d):
            dn[:] = [x for x in dn if x not in (".lake", ".git", "lake-packages")]
            for f in fs:
                if f.endswith(".lean"):
                    files.append((os.path.join(dp, f), f"{name}:" + os.path.relpath(os.path.join(dp, f), d)))
    for p, rel in files:
        src = read(p); code = mask_comments_strings(src)
        ns_stack = []
        events = [(m.start(), "ns", m) for m in re.finditer(r"^[ \t]*(namespace|end)[ \t]+([^\s]+)", code, re.M)]
        events += [(m.start(), "decl", m) for m in DECL.finditer(code)]
        for off, kind, m in sorted(events, key=lambda e: e[0]):
            if kind == "ns":
                if m.group(1) == "namespace":
                    ns_stack.append(m.group(2))
                elif ns_stack and ns_stack[-1].split(".")[-1] == m.group(2).split(".")[-1]:
                    ns_stack.pop()
                continue
            name = m.group(2)
            if name.startswith("_root_."):
                full = name[len("_root_."):]
            else:
                full = ".".join(ns_stack + [name]) if ns_stack else name
            head = code[m.end(): m.end() + 600]
            sig = head.split(":=")[0]
            prop_valued = bool(re.search(r":\s*(?:[^:]*→\s*)?Prop\s*$", sig.strip()))
            short = full.split(".")[-1]
            decls.setdefault(short, []).append((full, rel, line_of(src, off), m.group(1), prop_valued))
    return decls

def decl_body(code, name):
    """(start offset, body) of `def name ... :=` up to the next top-level declaration."""
    m = re.search(rf"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(?:def|abbrev)\s+{re.escape(name)}\b[^\n]*?(?::=|$)", code, re.M)
    if not m:
        return None, None
    start = code.find(":=", m.start())
    if start < 0:
        return None, None
    nxt = re.compile(r"^(?:/--|@\[|theorem\b|lemma\b|def\b|abbrev\b|noncomputable\b|instance\b|"
                     r"structure\b|inductive\b|end\b|namespace\b|section\b|--\s*TRUTH-GATE)", re.M)
    mm = nxt.search(code, start + 2)
    end = mm.start() if mm else len(code)
    return start + 2, code[start + 2:end]

BINDER = re.compile(r"(?:∀|∃!?|fun|λ|Σ|Π|⨆|⨅|∑|∏)\s*([^,=↦:]*?)(?:[,:]|=>|↦)")
GROUP = re.compile(r"[(\[{⦃]\s*([^():\[\]{}]+?)\s*:")

def bound_names(body):
    out = set()
    for m in BINDER.finditer(body):
        for t in re.findall(r"[^\s()\[\]{}⦃⦄,]+", m.group(1)):
            out.add(t)
    for m in GROUP.finditer(body):
        for t in m.group(1).split():
            out.add(t)
    return out

def tokens_with_offsets(body):
    for m in IDENT.finditer(body):
        yield m.start(), m.group(0)

def strip_outer(s):
    s = s.strip()
    while s.startswith("(") and s.endswith(")"):
        depth = 0
        for i, c in enumerate(s):
            depth += c in "([{⦃"; depth -= c in ")]}⦄"
            if depth == 0 and i < len(s) - 1:
                return s
        s = s[1:-1].strip()
    return s

def split_top(s, seps):
    parts, depth, cur, i = [], 0, [], 0
    while i < len(s):
        c = s[i]
        if c in "([{⦃⟨": depth += 1
        elif c in ")]}⦄⟩": depth -= 1
        hit = next((sep for sep in seps if depth == 0 and s.startswith(sep, i)), None)
        if hit:
            parts.append("".join(cur)); cur = []; i += len(hit); continue
        cur.append(c); i += 1
    parts.append("".join(cur))
    return parts

def named_props(expr, decls, depth=0):
    """Repository names that occur as a whole hypothesis or conclusion of formal_claim
    (the 'named Prop' pattern: `(∀ ν > 0, SomeRepoProp ν) → ... → SomeRepoConclusion`)."""
    out = set()
    if depth > 12:
        return out
    e = strip_outer(expr)
    m = re.match(r"^(?:∀|∃!?)\s", e)
    if m:
        parts = split_top(e, [","])
        if len(parts) > 1:
            return named_props(",".join(parts[1:]), decls, depth + 1)
    pieces = split_top(e, ["→", "∧", "↔", "∨"])
    if len(pieces) > 1:
        for p in pieces:
            out |= named_props(p, decls, depth + 1)
        return out
    toks = [t for _, t in tokens_with_offsets(e)]
    if re.search(r"[=≠≤<≥>∈∉⊆⊂∣≃≅]|:=", e):
        return out
    if toks:
        head = toks[0]
        short = head.split(".")[-1]
        if short in decls and not e.lstrip().startswith(("∀", "∃", "fun", "λ")):
            out.add(short)
    return out

def _as_vocab(v):
    if isinstance(v, list):
        return {(x["name"] if isinstance(x, dict) else x): (x.get("why", "") if isinstance(x, dict) else "") for x in v}
    return dict(v or {})

def vocab_file_entry(tag):
    """Lint configuration kept beside the lock (TRUTH_GATE.vocabulary.json), keyed by lock name
    ("main lock" or the additional lock's name). It cannot change the locked claim: the lock region
    hash still pins paper_claim; it only lists the basic repository notions the approved paper_claim
    may use, and extra names that the paper side must never use."""
    p = os.path.join(ROOT, VOCAB_FILE)
    if not os.path.isfile(p):
        return {}
    return json.load(open(p, encoding="utf-8")).get("locks", {}).get(tag, {})

def vocab_of(entry, tag="main lock"):
    v = _as_vocab(entry.get("paper_vocabulary"))
    v.update(_as_vocab(vocab_file_entry(tag).get("paper_vocabulary")))
    return v

def forbidden_of(entry, tag="main lock"):
    return set(entry.get("paper_forbidden_names", [])) | set(vocab_file_entry(tag).get("paper_forbidden_names", []))

# ----------------------------------------------------------------------------- lint

def lint_lock_entry(lock, entry, tag, decls, findings):
    semf = entry.get("semantics_file")
    if not semf or not os.path.isfile(os.path.join(ROOT, semf)):
        return
    src = read(os.path.join(ROOT, semf)); code = mask_comments_strings(src)
    claims = entry.get("claims") or [None]
    vocab = vocab_of(entry, tag)
    forbidden = forbidden_of(entry, tag)
    helpers_seen = set()
    for cid in claims:
        sfx = f"_{cid}" if cid else ""
        fname, pname = f"formal_claim{sfx}", f"paper_claim{sfx}"
        fstart, fbody = decl_body(code, fname)
        pstart, pbody = decl_body(code, pname)
        if pbody is None:
            findings.append(dict(cls="LOCK-FORM", kind="missing-paper-claim", lock=tag, file=semf, line=1,
                                 ident=pname, msg=f"{pname} not found in {semf}"))
            continue
        hyp = named_props(fbody, decls) if fbody else set()
        queue = [(pname, pstart, pbody)]
        while queue:
            dname, dstart, dbody = queue.pop()
            bound = bound_names(dbody)
            for off, tok in tokens_with_offsets(dbody):
                if tok in KEYWORDS or tok in bound:
                    continue
                short = tok.split(".")[-1]
                ln = line_of(src, dstart + off)
                if re.fullmatch(r"(?:TruthGate\.)?formal_claim\w*", tok):
                    findings.append(dict(cls="LOCK-FORM", kind="alias", lock=tag, file=semf, line=ln, ident=tok,
                                         msg=f"{dname} mentions {tok} (vacuous alias)"))
                    continue
                if short in helpers_seen:
                    continue
                if short not in hyp and short not in (pname, fname) and any(d[1] == semf for d in decls.get(short, [])):
                    hs, hb = decl_body(code, short)
                    if hb is not None:
                        # a paper-side helper written in the Semantics file itself: lint its body too
                        helpers_seen.add(short); queue.append((short, hs, hb)); continue
                if short in forbidden or tok in forbidden:
                    findings.append(dict(cls="LOCK-FORM", kind="forbidden-name", lock=tag, file=semf, line=ln,
                                         ident=short, msg=f"{dname} names the repository Prop {short}, which the lock "
                                         "lists in paper_forbidden_names"))
                    continue
                if short not in decls or short in (pname, fname) or short.startswith("intended_correspondence"):
                    continue
                d = decls[short][0]
                if short in hyp:
                    findings.append(dict(cls="LOCK-FORM", kind="named-hypothesis", lock=tag, file=semf, line=ln,
                                         ident=short, decl=f"{d[1]}:{d[2]}",
                                         msg=f"{dname} reuses {short} ({d[0]}, declared at {d[1]}:{d[2]}), which "
                                         f"is a whole hypothesis or conclusion of {fname}. The paper side must "
                                         f"write that condition out from the paper's own definition"))
                    continue
                if short not in vocab:
                    findings.append(dict(cls="LOCK-FORM", kind="unlisted-repo-name", lock=tag, file=semf, line=ln,
                                         ident=short, decl=f"{d[1]}:{d[2]}",
                                         msg=f"{dname} uses the repository {'Prop' if d[4] else d[3]} {short} "
                                         f"({d[0]}, declared at {d[1]}:{d[2]}), which is not in this lock's "
                                         "paper_vocabulary (TRUTH_GATE.vocabulary.json)"))
    for name in sorted(set(vocab) & forbidden):
        findings.append(dict(cls="LOCK-FORM", kind="vocab-forbidden", lock=tag, file=os.path.basename(LOCK_NAMES[0]),
                             line=1, ident=name, msg=f"paper_vocabulary lists {name}, which is also in paper_forbidden_names"))

REQUIRED = ("Required: write the paper side as an independent transcription of the paper's own "
            "definition (quote it in PAPER_QUOTE_BEGIN/END, use the paper's symbols), using only Mathlib and "
            "basic repository vocabulary listed with a reason in TRUTH_GATE.vocabulary.json. Never reuse a "
            "Prop that is a hypothesis or the conclusion of formal_claim. Then prove intended_correspondence "
            "with real reasoning (no sorry, no rfl) and get the author's sign-off on the new lock.")

def cmd_lint(args):
    global FETCH_DEPS
    FETCH_DEPS = bool(getattr(args, "fetch_deps", False))
    lname, lock = load_lock()
    if lock is None:
        print("TRUTH GATE LINT: no TRUTH_GATE.lock here; nothing to lint"); return 0
    decls = repo_declarations(lock)
    findings = []
    lint_lock_entry(lock, lock, "main lock", decls, findings)
    for ex in lock.get("additional_locks", []):
        lint_lock_entry(lock, ex, ex.get("name", ex.get("semantics_file", "?")), decls, findings)
    seen, uniq = {}, []
    for f in findings:
        k = (f["lock"], f["kind"], f["ident"])
        if k in seen:
            seen[k]["also_lines"] = seen[k].get("also_lines", []) + [f["line"]]; continue
        seen[k] = f; uniq.append(f)
    findings = uniq
    os.makedirs(REPORT, exist_ok=True)
    json.dump(findings, open(os.path.join(REPORT, "lint.json"), "w"), indent=1, ensure_ascii=False)
    if not findings:
        print("TRUTH GATE LINT PASS: paper_claim uses no repository name outside paper_vocabulary "
              "and no hypothesis or conclusion Prop of formal_claim")
        return 0
    print(f"TRUTH GATE LINT FAIL [LOCK-FORM] ({NOT_MATH}): {len(findings)} finding(s)")
    for f in findings:
        more = f" (also lines {', '.join(map(str, f['also_lines']))})" if f.get("also_lines") else ""
        print(f"  {f['file']}:{f['line']}: [{f['lock']}] `{f['ident']}`: {f['msg']}{more}")
        if os.environ.get("GITHUB_ACTIONS"):
            rel = os.path.relpath(os.path.join(ROOT, f["file"]), git_top())
            print(f"::error file={rel},line={f['line']},title=Truth Gate LOCK-FORM ({NOT_MATH})::{f['msg']}")
    print("  " + REQUIRED)
    return 1

# ----------------------------------------------------------------------------- paper diff

COPYRIGHT = re.compile(r"copyright|\\copyright|©|\(c\)|all rights reserved|licen[cs]e|apache|cc[ -]?by|"
                       r"creative ?commons|orcid|notice|spdx|attribution|\\thanks|cite this", re.I)

def paper_entries(lock):
    out = [("main lock", lock)] if lock.get("paper_path") else []
    out += [(x.get("name", x.get("semantics_file", "?")), x) for x in lock.get("additional_locks", []) if x.get("paper_path")]
    return out

def find_locked_version(paper_rel_top, want, top):
    r = git("log", "--format=%H", "-n", "400", "--", paper_rel_top, cwd=top)
    for c in r.stdout.split():
        b = subprocess.run(["git", "show", f"{c}:{paper_rel_top}"], cwd=top, capture_output=True)
        if b.returncode == 0 and sha256_bytes(b.stdout) == want:
            return c, b.stdout.decode("utf-8", "replace")
    return None, None

def paper_diff_text(lock, quotes_by_tag=None):
    top = git_top(); lines = []; drift = []
    for tag, e in paper_entries(lock):
        pp = os.path.normpath(os.path.join(ROOT, e["paper_path"]))
        if not os.path.isfile(pp):
            continue
        have = sha256_file(pp)
        if have == e.get("paper_sha256"):
            continue
        rel_top = os.path.relpath(pp, top)
        c, old = find_locked_version(rel_top, e.get("paper_sha256", ""), top)
        new = read(pp)
        item = dict(lock=tag, paper=e["paper_path"], locked=e.get("paper_sha256"), now=have, base_commit=c)
        lines.append(f"[PAPER-HASH] {tag}: {e['paper_path']} sha256 is now {have}, the lock records {e.get('paper_sha256')}")
        if old is None:
            lines.append("  No commit in this history has the locked bytes, so no line diff can be shown. Compare by hand.")
            item["only_copyright"] = None
        else:
            ol, nl = old.splitlines(), new.splitlines()
            changed = [l for l in difflib.unified_diff(ol, nl, lineterm="", n=0)
                       if (l.startswith(("+", "-")) and not l.startswith(("+++", "---")))]
            body = [l[1:] for l in changed]
            only_c = bool(body) and all(COPYRIGHT.search(b) or not b.strip() for b in body)
            item["changed_lines"] = len(changed); item["only_copyright"] = only_c
            lines.append(f"  Locked bytes match commit {c[:12]}. {len(changed)} line(s) changed since then"
                         + (" (copyright/license/attribution lines only)." if only_c else ":"))
            for l in changed[:40]:
                lines.append("    " + l[:160])
            if len(changed) > 40:
                lines.append(f"    ... {len(changed) - 40} more")
            touched_quote = False
            for q in re.findall(r"PAPER_QUOTE_BEGIN\n(.*?)\nPAPER_QUOTE_END", read(os.path.join(ROOT, e["semantics_file"])), re.S) if e.get("semantics_file") else []:
                if re.sub(r"\s+", " ", q).strip() not in re.sub(r"\s+", " ", new):
                    touched_quote = True
            item["quote_changed"] = touched_quote
            if touched_quote:
                lines.append("  The locked quote is no longer verbatim in the paper. That is a statement change and needs "
                             "the author's sign-off on a new lock.")
        lines.append(f"  Required: if the change is intended, set paper_sha256 to {have} for {tag} in TRUTH_GATE.lock, "
                     "and update the PAPER_SHA256 line in the Semantics file and the paper hash in TRUTH_GATE.md "
                     "in the same commit. Nothing else in the lock changes.")
        drift.append(item)
    return lines, drift

def cmd_paper_diff(args):
    _, lock = load_lock()
    if lock is None:
        return 0
    lines, drift = paper_diff_text(lock)
    os.makedirs(REPORT, exist_ok=True)
    json.dump(drift, open(os.path.join(REPORT, "paper-diff.json"), "w"), indent=1)
    print("\n".join(lines) if lines else "paper hashes match the lock")
    return 1 if drift else 0

# ----------------------------------------------------------------------------- stale base

def claim_files(lock):
    """The files that define what is claimed: the lock, the vocabulary, Semantics files, papers."""
    top = git_top(); fs = []
    for e in [lock] + list(lock.get("additional_locks", [])):
        for k in ("semantics_file", "paper_path"):
            if e.get(k):
                fs.append(os.path.relpath(os.path.normpath(os.path.join(ROOT, e[k])), top))
    for n in LOCK_NAMES + [VOCAB_FILE]:
        fs.append(os.path.relpath(os.path.join(ROOT, n), top))
    return sorted(set(fs))

def gate_files(lock):
    top = git_top(); fs = []
    for e in [lock] + list(lock.get("additional_locks", [])):
        for k in ("semantics_file", "paper_path", "audit_file"):
            if e.get(k):
                fs.append(os.path.relpath(os.path.normpath(os.path.join(ROOT, e[k])), top))
    for n in LOCK_NAMES + [VOCAB_FILE, "TRUTH_GATE.md", "scripts/truth_gate_check.py", "scripts/verify-lock.sh",
                           "scripts/TruthGateAudit.lean", "scripts/truth_gate_classify.py"]:
        fs.append(os.path.relpath(os.path.join(ROOT, n), top))
    return sorted(set(fs))

def cmd_stale_base(args):
    _, lock = load_lock()
    ctx = dict(event=os.environ.get("GITHUB_EVENT_NAME", "local"), stale=False, remerged=False)
    os.makedirs(REPORT, exist_ok=True)
    out = os.path.join(REPORT, "context.json")
    head = git("rev-parse", "HEAD").stdout.strip()
    ctx["evaluated"] = head
    parents = git("rev-list", "--parents", "-n", "1", "HEAD").stdout.split()[1:]
    if not args.base_ref or len(parents) != 2 or lock is None:
        ctx["note"] = "not a pull-request merge commit; nothing to compare"
        json.dump(ctx, open(out, "w"), indent=1); print("stale-base: " + ctx["note"]); return 0
    base_used, pr_head = parents
    if args.head and args.head != pr_head:
        ctx["note"] = f"merge parent {pr_head[:12]} differs from the PR head {args.head[:12]}"
        pr_head = args.head
    if args.fetch:
        git("fetch", "--no-tags", "origin", f"+refs/heads/{args.base_ref}:refs/remotes/origin/{args.base_ref}")
    tip = git("rev-parse", f"refs/remotes/origin/{args.base_ref}").stdout.strip()
    files = gate_files(lock)
    ctx.update(base_used=base_used, base_tip=tip, pr_head=pr_head)
    ctx["pr_touches_gate"] = [f for f in git("diff", "--name-only", f"{base_used}...{pr_head}", "--", *files).stdout.split() if f]
    ctx["pr_touches_claim"] = [f for f in git("diff", "--name-only", f"{base_used}...{pr_head}", "--", *claim_files(lock)).stdout.split() if f]
    if tip and tip != base_used:
        moved = [f for f in git("diff", "--name-only", base_used, tip, "--", *files).stdout.split() if f]
        ctx["main_changed_gate_files"] = moved
        if moved:
            ctx["stale"] = True
            print(f"STALE-BASE: this run's merge ref was built on {args.base_ref} {base_used[:12]}, but "
                  f"{args.base_ref} is now {tip[:12]} and has changed: {', '.join(moved)}")
            if args.remerge:
                git("-c", "user.email=truth-gate@localhost", "-c", "user.name=truth-gate", "checkout", "-q", "--detach", pr_head)
                r = git("-c", "user.email=truth-gate@localhost", "-c", "user.name=truth-gate", "merge", "--no-edit",
                        "--no-ff", "-q", tip)
                if r.returncode != 0:
                    git("merge", "--abort")
                    ctx["remerge_conflict"] = True
                    json.dump(ctx, open(out, "w"), indent=1)
                    print(f"STALE-BASE: the branch does not merge cleanly with {args.base_ref} {tip[:12]}. "
                          "Branch is behind main's lock; update the branch. This is not a math failure.")
                    return 1
                ctx["remerged"] = True; ctx["evaluated"] = git("rev-parse", "HEAD").stdout.strip()
                print(f"STALE-BASE: re-merged the PR head {pr_head[:12]} onto current {args.base_ref} {tip[:12]}; "
                      f"the gate now evaluates {ctx['evaluated'][:12]}, which is what would actually land.")
            else:
                print("Branch is behind main's lock; update branch.")
    if not ctx.get("stale"):
        print(f"stale-base: merge ref is built on the current {args.base_ref} tip {tip[:12]} (or main has not "
              "changed any lock, Semantics, paper or gate file since)")
    json.dump(ctx, open(out, "w"), indent=1)
    return 0

# ----------------------------------------------------------------------------- report

AUDIT_FORM = re.compile(r"in terms of formal_claim|syntactically equal|definitionally equal|not transported|"
                        r"does not use main theorem|main theorem statement is not formal_claim")
STATIC_RULES = [
    (re.compile(r"forbidden token"), "KERNEL/PROOF"),
    (re.compile(r"paper sha256 \S+ != locked"), "PAPER-HASH"),
    (re.compile(r"lock region sha256 \S+ != locked"), "LOCK-FORM"),
    (re.compile(r"NOT certifying"), "LOCK-FORM"),
    (re.compile(r"names the repository Prop|mentions (a )?formal_claim|vacuous alias|proved trivially|"
                r"essentially\) rfl|lock region lacks|cannot parse|lock region markers|PAPER_QUOTE|quoted paper text|"
                r"does not record|PAPER_SECTION|TRUTH_GATE\.md|lacks key|missing|lean_roots|draft"), "LOCK-FORM"),
]

def reopened_subclass(reason):
    r = (reason or "").lower()
    if "partial" in r:
        return ("partial lock", "The lock covers only part of the paper's stated theorem. The locked part may well be "
                "kernel-checked; the rest of the theorem has to be formalized and locked too (no partial locks).")
    if "tautolog" in r or "restates" in r or "vacuous" in r:
        return ("vacuous claim", "The locked theorem restates its own hypothesis, so nothing false was found but "
                "nothing beyond the definition is certified. Either prove a real statement or align the paper "
                "to exactly what the kernel proves.")
    return ("not independently transcribed", "paper_claim reuses repository definitions where the paper gives its own "
            "definition. Rewrite paper_claim from the paper's words and symbols.")

def phase_rcs():
    p = os.path.join(REPORT, "phases.tsv"); rc = {}
    if os.path.isfile(p):
        for l in read(p).splitlines():
            if "\t" in l:
                k, v = l.split("\t", 1); rc[k] = int(v.strip() or 0)
    return rc

def cmd_report(args):
    _, lock = load_lock(); lock = lock or {}
    rc = phase_rcs()
    get = lambda n: read(os.path.join(REPORT, n)) if os.path.isfile(os.path.join(REPORT, n)) else ""
    items = []  # (class, text)
    # kernel / proof phases
    kernel_phases = [k for k in rc if k.startswith(("build", "sorry", "audit"))]
    for k in kernel_phases:
        if rc[k] == 0:
            continue
        if k.startswith("audit"):
            log = get(k + ".txt")
            form, hard = [], []
            for l in log.splitlines():
                l = l.strip()
                if "TRUTH GATE FAIL:" in l:
                    (form if AUDIT_FORM.search(l) else hard).append(l)
                elif ("error:" in l and "TRUTH GATE FAIL" not in l) or "sorryAx" in l:
                    hard.append(l)
            for l in form:
                items.append(("LOCK-FORM", f"kernel audit: {l} (the lock's statements are wired wrongly; {NOT_MATH})"))
            for l in hard[:20]:
                items.append(("KERNEL/PROOF", f"kernel audit ({k}): {l}"))
            if not form and not hard:
                items.append(("KERNEL/PROOF", f"kernel audit ({k}) did not print TRUTH GATE AUDIT PASS (exit {rc[k]})"))
        elif k.startswith("sorry"):
            for l in get(k + ".txt").splitlines():
                if l.strip():
                    items.append(("KERNEL/PROOF", l.strip()))
        else:
            errs = [l.strip() for l in get(k + ".log").splitlines() if re.search(r"error:|error\b.*\.lean", l)]
            items.append(("KERNEL/PROOF", f"`{k}` failed (exit {rc[k]})" + (": " + " | ".join(errs[:5]) if errs else "")))
    # static checks
    for l in get("static.txt").splitlines():
        if not l.startswith("TRUTH GATE FAIL: "):
            continue
        msg = l[len("TRUTH GATE FAIL: "):]
        cls = next((c for rx, c in STATIC_RULES if rx.search(msg)), "UNCLASSIFIED")
        if "NOT certifying" in msg:
            sub, expl = reopened_subclass(msg)
            msg = f"the lock is marked non-certifying ({sub}). {expl} Recorded reason: {msg.split(': ', 1)[-1]}"
        items.append((cls, msg))
    if rc.get("static", 0) != 0 and not any(l.startswith("TRUTH GATE FAIL: ") for l in get("static.txt").splitlines()):
        items.append(("UNCLASSIFIED", f"scripts/truth_gate_check.py exited {rc['static']} without a TRUTH GATE FAIL line: "
                      + " | ".join(get("static.txt").strip().splitlines()[-3:])))
    if rc.get("lint", 0) not in (0, 1):
        items.append(("UNCLASSIFIED", f"lock-form lint crashed (exit {rc['lint']}): "
                      + " | ".join(get("lint.txt").strip().splitlines()[-3:])))
    # lint
    for f in json.load(open(os.path.join(REPORT, "lint.json"))) if os.path.isfile(os.path.join(REPORT, "lint.json")) else []:
        items.append(("LOCK-FORM", f"{f['file']}:{f['line']}: `{f['ident']}`: {f['msg']}"))
    # paper drift detail
    pd_lines, drift = paper_diff_text(lock) if lock else ([], [])
    # context
    ctx = json.load(open(os.path.join(REPORT, "context.json"))) if os.path.isfile(os.path.join(REPORT, "context.json")) else {}
    if ctx.get("remerge_conflict"):
        items.append(("STALE-BASE", "branch is behind main's lock and does not merge cleanly; update branch"))
    classes = []
    for c, _ in items:
        if c not in classes:
            classes.append(c)
    kernel_ok = bool(kernel_phases) and all(rc[k] == 0 for k in kernel_phases) and "KERNEL/PROOF" not in classes
    out = []
    out.append("=" * 72)
    out.append("TRUTH GATE VERDICT")
    if ctx:
        ev = ctx.get("evaluated", "")[:12]
        if ctx.get("remerged"):
            out.append(f"Evaluated {ev}: PR head {ctx['pr_head'][:12]} merged onto the CURRENT base {ctx['base_tip'][:12]} "
                       f"(GitHub's merge ref was built on the older {ctx['base_used'][:12]}).")
        elif ctx.get("base_used"):
            out.append(f"Evaluated {ev}: PR merge ref on base {ctx['base_used'][:12]} (current base tip {ctx.get('base_tip','')[:12]}).")
    if not kernel_phases:
        out.append("Kernel/proof checks: not run in this invocation.")
    elif kernel_ok:
        out.append("Kernel/proof checks: PASS (lake build, no sorry outside draft dirs, kernel audit: standard axioms only).")
    else:
        out.append("Kernel/proof checks: FAIL. This is a proof failure (see KERNEL/PROOF below).")
    labels = {
        "KERNEL/PROOF": "KERNEL/PROOF FAILURE (a proof does not check)",
        "LOCK-FORM": f"LOCK-FORM: {NOT_MATH}",
        "PAPER-HASH": "PAPER-HASH: the paper changed after the lock (not a math failure)",
        "STALE-BASE": "STALE-BASE: branch is behind main's lock; update branch (not a math failure)",
        "UNCLASSIFIED": "UNCLASSIFIED (read the message; not presumed to be a math failure)",
    }
    for c in classes:
        out.append("")
        out.append("[" + labels[c] + "]")
        for cc, t in items:
            if cc == c:
                out.append("  - " + t)
        if c == "LOCK-FORM" and any(cc == "LOCK-FORM" and not re.search(r"\((partial lock|vacuous claim)\)", t)
                                    for cc, t in items):
            out.append("  " + REQUIRED)
        if c == "PAPER-HASH":
            out += ["  " + l for l in pd_lines]
    if ctx.get("stale") and ctx.get("remerged"):
        out.append("")
        out.append("[STALE-BASE note] main changed " + ", ".join(ctx.get("main_changed_gate_files", [])) +
                   " after this PR's merge ref was built; the verdict above is for the fresh merge.")
    lock_classes = {"LOCK-FORM", "PAPER-HASH"}
    if ctx.get("base_used") and not ctx.get("pr_touches_claim", ctx.get("pr_touches_gate")) and set(classes) & lock_classes:
        out.append("")
        out.append("[INHERITED] This PR changes no lock, vocabulary, Semantics or paper file. The failure above comes from "
                   f"the base branch ({ctx.get('base_tip','')[:12]}); fix it there, then update this branch.")
    out.append("")
    if not classes:
        out.append("VERDICT: PASS")
    else:
        extra = " Kernel checks passed: no math was found false." if kernel_ok and "KERNEL/PROOF" not in classes else ""
        out.append(f"VERDICT: FAIL ({', '.join(classes)}).{extra}")
    out.append("=" * 72)
    text = "\n".join(out)
    print(text)
    json.dump(dict(classes=classes, kernel_ok=kernel_ok, items=items, context=ctx, paper_drift=drift),
              open(os.path.join(REPORT, "classification.json"), "w"), indent=1, ensure_ascii=False)
    if os.environ.get("GITHUB_STEP_SUMMARY"):
        with open(os.environ["GITHUB_STEP_SUMMARY"], "a", encoding="utf-8") as f:
            f.write("```\n" + text + "\n```\n")
    if os.environ.get("GITHUB_ACTIONS"):
        for c in classes:
            print(f"::error title=Truth Gate {labels[c]}::see the TRUTH GATE VERDICT block in this log")
    return 1 if classes else 0

def main():
    ap = argparse.ArgumentParser(description="Truth Gate failure classifier")
    sp = ap.add_subparsers(dest="cmd")
    l = sp.add_parser("lint")
    l.add_argument("--fetch-deps", action="store_true", help="shallow-fetch the author's Lake dependencies")
    sp.add_parser("paper-diff"); sp.add_parser("report")
    s = sp.add_parser("stale-base")
    s.add_argument("--base-ref", default=os.environ.get("GITHUB_BASE_REF", ""))
    s.add_argument("--head", default="")
    s.add_argument("--fetch", action="store_true")
    s.add_argument("--remerge", action="store_true")
    a = ap.parse_args()
    fn = {"lint": cmd_lint, "paper-diff": cmd_paper_diff, "report": cmd_report, "stale-base": cmd_stale_base}.get(a.cmd)
    if not fn:
        ap.print_help(); return 3
    return fn(a)

if __name__ == "__main__":
    sys.exit(main())
