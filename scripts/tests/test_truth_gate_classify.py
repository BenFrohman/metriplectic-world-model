# Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Benjamin Stanley Frohman
#
# Fixtures for every Truth Gate failure class (see TRUTH_GATE.md, "Failure classes").
# Run: python3 -m unittest discover -s scripts/tests -p 'test_truth_gate_classify.py' -v
# Each test builds a tiny throw-away repository in a temp dir; no Lean toolchain is needed.
import hashlib, json, os, subprocess, sys, tempfile, textwrap, unittest

SCRIPT = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "truth_gate_classify.py")

REPO_DEFS = textwrap.dedent("""\
    namespace Demo
    /-- a basic object -/
    abbrev Field := Nat → Nat
    /-- the hard hypothesis -/
    def HardBound (ν : Nat) : Prop := ∀ f : Field, f ν ≤ ν
    /-- the conclusion -/
    def Regular : Prop := True
    end Demo
""")

PAPER = "Theorem. If every field obeys the bound then the flow is regular.\nCopyright (c) 2026 Benjamin Stanley Frohman.\n"

def semantics(paper_body, sha):
    return textwrap.dedent(f"""\
        import Demo.Defs
        /-!
        PAPER_PATH: paper.tex
        PAPER_SHA256: {sha}
        PAPER_SECTION: Theorem
        PAPER_QUOTE_BEGIN
        Theorem. If every field obeys the bound then the flow is regular.
        PAPER_QUOTE_END
        -/
        namespace TruthGate
        open Demo
        -- TRUTH-GATE LOCK BEGIN
        /-- formal -/
        def formal_claim : Prop :=
          (∀ ν : Nat, HardBound ν) → Regular

        /-- paper -/
        def paper_claim : Prop :=
        {paper_body}

        theorem intended_correspondence : formal_claim ↔ paper_claim := by
          constructor <;> intro h <;> exact h
        -- TRUTH-GATE LOCK END
        end TruthGate
    """)

GOOD_BODY = "  (∀ ν : Nat, ∀ f : Field, f ν ≤ ν) → True"
BAD_BODY = "  (∀ ν : Nat, HardBound ν) → True"

def put(path, text, mode="w"):
    with open(path, mode, encoding="utf-8") as f:
        f.write(text)

def load(path):
    with open(path, encoding="utf-8") as f:
        return json.load(f)

def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()

def run(root, *args, env=None):
    e = dict(os.environ, TRUTH_GATE_ROOT=root); e.pop("GITHUB_ACTIONS", None); e.pop("GITHUB_STEP_SUMMARY", None)
    e.update(env or {})
    return subprocess.run([sys.executable, SCRIPT, *args], cwd=root, capture_output=True, text=True, env=e)

def git(root, *args):
    r = subprocess.run(["git", "-c", "user.email=t@t", "-c", "user.name=t", "-c", "commit.gpgsign=false", *args],
                       cwd=root, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    return r.stdout.strip()

def make_repo(root, body=GOOD_BODY, vocab=None, paper=PAPER):
    os.makedirs(os.path.join(root, "Demo"), exist_ok=True)
    put(os.path.join(root, "Demo", "Defs.lean"), REPO_DEFS)
    put(os.path.join(root, "paper.tex"), paper)
    put(os.path.join(root, "Demo", "Semantics.lean"), semantics(body, sha(paper)))
    lock = dict(semantics_file="Demo/Semantics.lean", semantics_module="Demo.Semantics", paper_path="paper.tex",
                paper_sha256=sha(paper), main_theorems=["Demo.main"], lock_region_sha256="x",
                draft_dirs=["Demo/Draft"], lean_roots=["Demo"])
    lock["paper_vocabulary"] = vocab if vocab is not None else {"Field": "the paper's 'field': a map ℕ → ℕ"}
    put(os.path.join(root, "TRUTH_GATE.lock"), json.dumps(lock, indent=1))
    os.makedirs(os.path.join(root, "truth-gate-report"), exist_ok=True)

def phases(root, **rc):
    with open(os.path.join(root, "truth-gate-report", "phases.tsv"), "w") as f:
        for k, v in rc.items():
            f.write(f"{k.replace('_', '-')}\t{v}\n")

def write(root, name, text):
    put(os.path.join(root, "truth-gate-report", name), text)

class LockFormLint(unittest.TestCase):
    def test_named_hypothesis_is_rejected_with_file_and_line(self):
        with tempfile.TemporaryDirectory() as d:
            make_repo(d, body=BAD_BODY)
            r = run(d, "lint")
            self.assertEqual(r.returncode, 1, r.stdout)
            self.assertIn("lock wording/form problem, not a math failure", r.stdout)
            self.assertIn("`HardBound`", r.stdout)
            self.assertIn("whole hypothesis or conclusion of formal_claim", r.stdout)
            self.assertRegex(r.stdout, r"Demo/Semantics\.lean:\d+: \[main lock\] `HardBound`")
            self.assertIn("Demo/Defs.lean:5", r.stdout)

    def test_unlisted_repository_name_is_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            make_repo(d, vocab={})
            r = run(d, "lint")
            self.assertEqual(r.returncode, 1, r.stdout)
            self.assertIn("paper_vocabulary (TRUTH_GATE.vocabulary.json)", r.stdout)
            self.assertIn("`Field`", r.stdout)

    def test_independent_transcription_passes(self):
        with tempfile.TemporaryDirectory() as d:
            make_repo(d)
            r = run(d, "lint")
            self.assertEqual(r.returncode, 0, r.stdout)
            self.assertIn("TRUTH GATE LINT PASS", r.stdout)

    def test_vocabulary_file_lists_basic_notions(self):
        with tempfile.TemporaryDirectory() as d:
            make_repo(d, vocab={})
            put(os.path.join(d, "TRUTH_GATE.vocabulary.json"),
                json.dumps({"locks": {"main lock": {"paper_vocabulary": {"Field": "a map ℕ → ℕ"}}}}))
            self.assertEqual(run(d, "lint").returncode, 0)
            put(os.path.join(d, "TRUTH_GATE.vocabulary.json"),
                json.dumps({"locks": {"main lock": {"paper_vocabulary": {"Field": "x"},
                                                    "paper_forbidden_names": ["Field"]}}}))
            r = run(d, "lint")
            self.assertEqual(r.returncode, 1)
            self.assertIn("paper_forbidden_names", r.stdout)

    def test_alias_of_formal_claim_is_rejected(self):
        with tempfile.TemporaryDirectory() as d:
            make_repo(d, body="  formal_claim")
            r = run(d, "lint")
            self.assertEqual(r.returncode, 1)
            self.assertIn("vacuous alias", r.stdout)

class Report(unittest.TestCase):
    def test_kernel_failure_is_the_only_proof_failure(self):
        with tempfile.TemporaryDirectory() as d:
            make_repo(d)
            phases(d, static=0, lint=0, build=1, sorry=0, audit=1)
            write(d, "static.txt", "TRUTH GATE STATIC PASS\n")
            write(d, "build.log", "error: Demo/Main.lean:3:2: unknown identifier 'foo'\n")
            write(d, "audit.txt", "Demo/Main.lean:1:0: error: unknown constant\n")
            r = run(d, "report")
            self.assertEqual(r.returncode, 1)
            self.assertIn("KERNEL/PROOF FAILURE", r.stdout)
            self.assertIn("This is a proof failure", r.stdout)
            self.assertNotIn("LOCK-FORM", r.stdout)

    def test_sorry_and_nonstandard_axioms_are_kernel_failures(self):
        with tempfile.TemporaryDirectory() as d:
            make_repo(d)
            phases(d, static=1, lint=0, build=0, sorry=1, audit=1)
            write(d, "static.txt", "TRUTH GATE FAIL: forbidden token `sorry` at Demo/Main.lean:9\nTRUTH GATE STATIC FAIL (1 problems)\n")
            write(d, "sorry.txt", "sorry in build outside draft dirs: warning: Demo/Main.lean:9:0: declaration uses 'sorry'\n")
            write(d, "audit.txt", "info: TRUTH GATE FAIL: Demo.main uses nonstandard axioms [Demo.bad]\n")
            out = run(d, "report").stdout
            self.assertIn("KERNEL/PROOF FAILURE", out)
            self.assertIn("forbidden token `sorry`", out)
            self.assertIn("nonstandard axioms", out)

    def test_lock_form_failure_never_reads_as_math(self):
        with tempfile.TemporaryDirectory() as d:
            make_repo(d, body=BAD_BODY)
            run(d, "lint")
            phases(d, static=1, lint=1, build=0, build_semantics=0, sorry=0, audit=0)
            write(d, "static.txt", "TRUTH GATE FAIL: this lock is NOT certifying (reopened by the re-audit of 2026-11-16): "
                  "The hypotheses are not independently transcribed. `paper_claim` keeps the repository Prop `HardBound`.\n"
                  "TRUTH GATE STATIC FAIL (1 problems)\n")
            write(d, "audit.txt", "info: TRUTH GATE AUDIT PASS: main theorems [Demo.main]\n")
            r = run(d, "report")
            self.assertEqual(r.returncode, 1)
            out = r.stdout
            self.assertIn("LOCK-FORM: lock wording/form problem, not a math failure", out)
            self.assertIn("Kernel/proof checks: PASS", out)
            self.assertIn("no math was found false", out)
            self.assertIn("not independently transcribed", out)
            self.assertIn("`HardBound`", out)
            self.assertNotIn("This is a proof failure", out)
            self.assertNotIn("KERNEL/PROOF FAILURE", out)

    def test_partial_and_vacuous_locks_are_named(self):
        for reason, word in [("Partial lock. Only conjunct (P4) is locked.", "partial lock"),
                             ("Tautology, not a step. It restates its own hypothesis.", "vacuous claim")]:
            with tempfile.TemporaryDirectory() as d:
                make_repo(d)
                phases(d, static=1, lint=0, build=0, sorry=0, audit=0)
                write(d, "static.txt", f"TRUTH GATE FAIL: this lock is NOT certifying (reopened): {reason}\n")
                write(d, "audit.txt", "TRUTH GATE AUDIT PASS\n")
                out = run(d, "report").stdout
                self.assertIn(word, out)
                self.assertIn("not a math failure", out)
                self.assertNotIn("This is a proof failure", out)

    def test_paper_hash_drift_shows_copyright_only_diff(self):
        with tempfile.TemporaryDirectory() as d:
            make_repo(d)
            git(d, "init", "-q"); git(d, "add", "-A"); git(d, "commit", "-qm", "lock")
            new = PAPER.replace("Copyright (c) 2026 Benjamin Stanley Frohman.",
                                "Copyright (c) 2026 Benjamin Stanley Frohman. Licensed under CC BY 4.0.")
            put(os.path.join(d, "paper.tex"), new)
            git(d, "commit", "-qam", "copyright line")
            phases(d, static=1, lint=0, build=0, sorry=0, audit=0)
            write(d, "static.txt", f"TRUTH GATE FAIL: paper sha256 {sha(new)} != locked {sha(PAPER)}\n")
            write(d, "audit.txt", "TRUTH GATE AUDIT PASS\n")
            r = run(d, "report")
            self.assertEqual(r.returncode, 1)
            self.assertIn("PAPER-HASH", r.stdout)
            self.assertIn("copyright/license/attribution lines only", r.stdout)
            self.assertIn("+Copyright (c) 2026 Benjamin Stanley Frohman. Licensed under CC BY 4.0.", r.stdout)
            self.assertIn(f"set paper_sha256 to {sha(new)}", r.stdout)
            self.assertNotIn("This is a proof failure", r.stdout)

    def test_paper_hash_drift_that_edits_the_quote_needs_sign_off(self):
        with tempfile.TemporaryDirectory() as d:
            make_repo(d)
            git(d, "init", "-q"); git(d, "add", "-A"); git(d, "commit", "-qm", "lock")
            new = PAPER.replace("then the flow is regular", "then the flow is smooth")
            put(os.path.join(d, "paper.tex"), new)
            git(d, "commit", "-qam", "edit")
            r = run(d, "paper-diff")
            self.assertEqual(r.returncode, 1)
            self.assertIn("statement change", r.stdout)
            self.assertNotIn("lines only", r.stdout)

class StaleBase(unittest.TestCase):
    def _scenario(self, d, conflict=False):
        make_repo(d, body=BAD_BODY)
        git(d, "init", "-q", "-b", "main"); git(d, "add", "-A"); git(d, "commit", "-qm", "old lock")
        base = git(d, "rev-parse", "HEAD")
        git(d, "checkout", "-qb", "pr")
        os.makedirs(os.path.join(d, ".github"), exist_ok=True)
        put(os.path.join(d, ".github", "ci.yml"), "ci change\n")
        if conflict:
            put(os.path.join(d, "Demo", "Semantics.lean"), "-- pr edit\n", "a")
        git(d, "add", "-A"); git(d, "commit", "-qm", "ci only")
        pr = git(d, "rev-parse", "HEAD")
        git(d, "checkout", "-q", "main")
        make_repo(d, body=GOOD_BODY)
        if conflict:
            put(os.path.join(d, "Demo", "Semantics.lean"), "-- main edit\n", "a")
        git(d, "commit", "-qam", "fix lock form on main")
        tip = git(d, "rev-parse", "HEAD")
        git(d, "update-ref", "refs/remotes/origin/main", tip)
        git(d, "checkout", "-q", "--detach", base)
        git(d, "merge", "-q", "--no-ff", "--no-edit", pr)  # GitHub's stale refs/pull/N/merge
        return base, pr, tip

    def test_stale_merge_ref_is_remerged_on_current_main(self):
        with tempfile.TemporaryDirectory() as d:
            base, pr, tip = self._scenario(d)
            r = run(d, "stale-base", "--base-ref", "main", "--head", pr, "--remerge")
            self.assertEqual(r.returncode, 0, r.stdout + r.stderr)
            self.assertIn("STALE-BASE", r.stdout)
            ctx = load(os.path.join(d, "truth-gate-report", "context.json"))
            self.assertTrue(ctx["stale"]); self.assertTrue(ctx["remerged"])
            self.assertEqual(ctx["pr_touches_gate"], [])
            parents = git(d, "rev-list", "--parents", "-n", "1", "HEAD").split()[1:]
            self.assertEqual(set(parents), {pr, tip})
            self.assertEqual(run(d, "lint").returncode, 0)  # the fresh merge carries main's fixed lock

    def test_stale_branch_with_conflict_says_update_branch(self):
        with tempfile.TemporaryDirectory() as d:
            base, pr, tip = self._scenario(d, conflict=True)
            r = run(d, "stale-base", "--base-ref", "main", "--head", pr, "--remerge")
            self.assertEqual(r.returncode, 1)
            self.assertIn("update the branch", r.stdout)
            self.assertIn("not a math failure", r.stdout)

    def test_inherited_failure_is_labelled(self):
        with tempfile.TemporaryDirectory() as d:
            base, pr, tip = self._scenario(d)
            run(d, "stale-base", "--base-ref", "main", "--head", pr)  # report only, no re-merge
            run(d, "lint")
            phases(d, static=0, lint=1, build=0, sorry=0, audit=0)
            write(d, "static.txt", "TRUTH GATE STATIC PASS\n"); write(d, "audit.txt", "TRUTH GATE AUDIT PASS\n")
            out = run(d, "report").stdout
            self.assertIn("[INHERITED]", out)
            self.assertIn("changes no lock, Semantics, paper or gate file", out)

if __name__ == "__main__":
    unittest.main()
