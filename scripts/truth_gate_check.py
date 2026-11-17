#!/usr/bin/env python3
# Author: Benjamin Stanley Frohman
# Truth Gate static checks (see TRUTH_GATE.md). Exit code 0 only if every check passes.
#  0. A lock marked `"certifying": false` (re-audit) fails.
#  1. TRUTH_GATE.lock parses and names existing files.
#  2. Semantics.lean declares formal_claim, paper_claim, intended_correspondence (inside the lock region).
#  3. The paper file hash equals the recorded hash, and the quoted paper text occurs verbatim
#     (whitespace-normalised) in the paper file.
#  4. The sha256 of the lock region of Semantics.lean equals the recorded hash (the claim is fixed).
#  5. No sorry / admit / native_decide / `axiom` declaration in any .lean file outside a draft directory
#     (comments and string literals excluded).
import hashlib, json, os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FAIL = []

def fail(msg):
    FAIL.append(msg)
    print("TRUTH GATE FAIL: " + msg)

def sha256_file(p):
    with open(p, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()

def norm(s):
    return re.sub(r"\s+", " ", s).strip()

def strip_comments_strings(src):
    out, i, n, depth = [], 0, len(src), 0
    while i < n:
        if depth > 0:
            if src.startswith("/-", i): depth += 1; i += 2; continue
            if src.startswith("-/", i): depth -= 1; i += 2; continue
            i += 1; continue
        if src.startswith("/-", i): depth = 1; i += 2; continue
        if src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j; continue
        if src[i] == '"':
            j = i + 1
            while j < n and src[j] != '"':
                j += 2 if src[j] == "\\" else 1
            out.append('""'); i = j + 1; continue
        out.append(src[i]); i += 1
    return "".join(out)

lock_path = os.path.join(ROOT, "TRUTH_GATE.lock")
if not os.path.isfile(lock_path):
    fail("TRUTH_GATE.lock missing"); sys.exit(1)
lock = json.load(open(lock_path))
for k in ["semantics_file", "semantics_module", "paper_path", "paper_sha256",
          "main_theorems", "lock_region_sha256", "draft_dirs", "lean_roots"]:
    if k not in lock: fail(f"TRUTH_GATE.lock lacks key {k}")
if FAIL: sys.exit(1)

# 0. Re-audit status: a lock marked non-certifying keeps the gate red (see TRUTH_GATE.md).
if lock.get("certifying", True) is not True:
    fail("this lock is NOT certifying (reopened by the re-audit of 2026-11-16): "
         + str(lock.get("reopened_reason", "see TRUTH_GATE.md")))

sem = os.path.join(ROOT, lock["semantics_file"])
if not os.path.isfile(sem):
    fail(f"{lock['semantics_file']} missing"); sys.exit(1)
src = open(sem, encoding="utf-8").read()

# 2. lock region and required declarations
m = re.search(r"^-- TRUTH-GATE LOCK BEGIN\n(.*?)^-- TRUTH-GATE LOCK END\n", src, re.S | re.M)
if not m:
    fail("lock region markers missing in Semantics.lean")
else:
    region = m.group(1)
    for decl in [r"def\s+formal_claim\s*:\s*Prop", r"def\s+paper_claim\s*:\s*Prop",
                 r"theorem\s+intended_correspondence\s*:\s*formal_claim\s*↔\s*paper_claim"]:
        if not re.search(decl, strip_comments_strings(region)):
            fail(f"lock region lacks `{decl}`")
    code_region = strip_comments_strings(region)
    # 2b. paper_claim must not mention formal_claim (no aliasing).
    pm = re.search(r"def\s+paper_claim\s*:\s*Prop\s*:=(.*?)(?=^\s*(?:/--|theorem|def|lemma)\b|\Z)", code_region, re.S | re.M)
    if not pm:
        fail("cannot parse the body of paper_claim")
    elif re.search(r"(?<![\w.'])(TruthGate\.)?formal_claim(?![\w'])", pm.group(1)):
        fail("paper_claim's definition mentions formal_claim (vacuous alias)")
    # 2c. intended_correspondence must have a substantive proof, not rfl / Iff.rfl.
    cm = re.search(r"theorem\s+intended_correspondence\s*:\s*formal_claim\s*↔\s*paper_claim\s*:=(.*)", code_region, re.S)
    if cm:
        body = re.sub(r"\s+", " ", cm.group(1)).strip()
        trivial = {"Iff.rfl", "rfl", "by rfl", "by exact Iff.rfl", "by exact rfl", "by apply Iff.rfl",
                   "by constructor <;> exact id", "⟨id, id⟩", "Iff.intro id id", "by exact ⟨id, id⟩",
                   "by simp", "by simp only [formal_claim, paper_claim]", "by unfold formal_claim paper_claim; rfl",
                   "by unfold formal_claim paper_claim; exact Iff.rfl", "by decide", "by trivial", "by tauto"}
        if body in trivial or re.fullmatch(r"(by\s+)?(exact\s+)?(Iff\.)?rfl", body):
            fail(f"intended_correspondence is proved trivially (`{body}`); a substantive proof is required")
        if re.search(r"(?<![\w.'])(Iff\.rfl|rfl)(?![\w'])", body) and len(body) < 40:
            fail(f"intended_correspondence proof `{body}` is (essentially) rfl")
    got = hashlib.sha256(region.encode("utf-8")).hexdigest()
    if got != lock["lock_region_sha256"]:
        fail(f"lock region sha256 {got} != locked {lock['lock_region_sha256']} "
             "(the locked claim was edited; changing it needs the owner's explicit sign-off and a new lock)")

# 3. paper hash and verbatim quote
pp = os.path.join(ROOT, lock["paper_path"])
if not os.path.isfile(pp):
    fail(f"paper file {lock['paper_path']} missing")
else:
    h = sha256_file(pp)
    if h != lock["paper_sha256"]:
        fail(f"paper sha256 {h} != locked {lock['paper_sha256']}")
    if f"PAPER_SHA256: {lock['paper_sha256']}" not in src:
        fail("Semantics.lean docstring does not record the locked PAPER_SHA256")
    if f"PAPER_PATH: {lock['paper_path']}" not in src:
        fail("Semantics.lean docstring does not record PAPER_PATH")
    if not re.search(r"^PAPER_SECTION: \S", src, re.M):
        fail("Semantics.lean docstring lacks a PAPER_SECTION: field")
    tg = open(os.path.join(ROOT, "TRUTH_GATE.md"), encoding="utf-8").read() if os.path.isfile(os.path.join(ROOT, "TRUTH_GATE.md")) else ""
    if not tg:
        fail("TRUTH_GATE.md missing")
    elif lock["paper_sha256"] not in tg or lock["paper_path"] not in tg:
        fail("TRUTH_GATE.md does not record the locked paper path and sha256")
    quotes = re.findall(r"PAPER_QUOTE_BEGIN\n(.*?)\nPAPER_QUOTE_END", src, re.S)
    if not quotes:
        fail("no PAPER_QUOTE_BEGIN/END block in Semantics.lean")
    paper = norm(open(pp, encoding="utf-8", errors="replace").read())
    for q in quotes:
        if norm(q) not in paper:
            fail("quoted paper text not found verbatim in the paper file: " + norm(q)[:120])
        if tg and norm(q) not in norm(tg):
            fail("TRUTH_GATE.md does not carry the verbatim paper quote")

# 5. forbidden tokens outside draft directories
drafts = [d.strip("/") for d in lock["draft_dirs"]]
tok = re.compile(r"(?<![\w.'])(sorry|admit|native_decide)(?![\w'])|^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|public\s+)*axiom\s", re.M)
bad = 0
for r in lock["lean_roots"]:
    base = os.path.join(ROOT, r)
    paths = [base] if os.path.isfile(base) else [
        os.path.join(dp, f) for dp, dn, fs in os.walk(base) if ".lake" not in dp for f in fs if f.endswith(".lean")]
    for p in sorted(paths):
        rel = os.path.relpath(p, ROOT)
        if any(rel == d or rel.startswith(d + "/") for d in drafts):
            continue
        code = strip_comments_strings(open(p, encoding="utf-8").read())
        for mm in tok.finditer(code):
            line = code.count("\n", 0, mm.start()) + 1
            fail(f"forbidden token `{(mm.group(1) or 'axiom')}` at {rel}:{line}"); bad += 1
print(f"TRUTH GATE STATIC: scanned roots {lock['lean_roots']} (draft dirs exempt: {drafts}); {bad} forbidden tokens")

if FAIL:
    print(f"TRUTH GATE STATIC FAIL ({len(FAIL)} problems)"); sys.exit(1)
print("TRUTH GATE STATIC PASS")
