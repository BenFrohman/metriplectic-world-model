# TRUTH GATE — the GOD gate. Read this first.

Author: Benjamin Stanley Frohman. This file is the root instruction for every person and every
automated agent (every bot) that touches this repository. Load it before any other file.

**Only truth and honest, kernel-proved theorems pass this gate. Nothing from this repository is
published, released, deposited on Zenodo, cited or claimed unless the `truth-gate` check is green
on the exact commit being cited.** That is why it is the GOD gate: it sits above every other
check, and no other green check can stand in for it.

## The issue this gate fixes

A paper states its claim in English. Lean can only prove `formal_claim ↔ paper_claim` once
`paper_claim` is itself written in Lean. If `paper_claim` were simply *defined to be*
`formal_claim` (or an alias of it, or something that unfolds to it), the theorem
`intended_correspondence` would be `Iff.rfl`: it would be empty and prove nothing about the
paper. A green certificate could then "certify" a statement different from the one the paper
makes (drift), whether by accident or by an injected instruction.

## The fix rule (binding, permanent)

1. `paper_claim` is an **independent Lean transcription of the paper's exact claim**, written in
   the paper's own terms, with every hypothesis the paper states. The verbatim English quote,
   the paper path, its sha256 and the section are recorded in the doc comment of
   `Semantics.lean` **and** in this file (below).
2. `paper_claim` must **not** be defined as, reference, or trivially alias `formal_claim`.
3. `intended_correspondence : formal_claim ↔ paper_claim` must have a **substantive proof**. It
   may not be `Iff.rfl`, `rfl`, `exact Iff.rfl` or similar, and it may not use the main theorem
   (it is a statement-level equivalence, not "both sides happen to be provable").
4. `formal_claim` is exactly the statement of the repository's main theorem, and
   `paper_claim_holds` is the main theorem transported across the correspondence.
5. Only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, `admit`, `native_decide` or
   new `axiom` anywhere outside the draft directories in `TRUTH_GATE.lock`.
6. If the paper's English claim cannot be faithfully transcribed, or is not what Lean proves,
   the gate stays **red** and the mismatch is reported. Never patch over it: never weaken
   `paper_claim`, drop a hypothesis, or redefine it to match the formal side. If the
   formalization drifted, rewrite the formalization so it transports across the lock again.
7. Open problems stay hypotheses. No Millennium Prize problem is claimed solved; the gate only
   ensures the certificate proves precisely the locked claim and nothing else.
8. The locked region of `Semantics.lean`, the quote and `TRUTH_GATE.lock` change only with the
   author's explicit sign-off, as a PR that says "new lock" in its title.
9. Commits are authored by Benjamin Stanley Frohman only, with no AI co-author trailers. No
   force-push and no history rewriting.

## What `scripts/verify-lock.sh` checks mechanically

* `lake build` succeeds, with no `sorry` warning outside the draft directories;
* no `sorry` / `admit` / `native_decide` / `axiom` token outside the draft directories
  (comments and strings excluded);
* `Semantics.lean` has `PAPER_PATH`, `PAPER_SHA256`, `PAPER_SECTION` and a verbatim
  `PAPER_QUOTE`; the hash matches the paper file and the quote occurs in it; this file carries
  the same path, hash and quote;
* the lock region hash matches `TRUTH_GATE.lock`;
* `paper_claim`'s body does not mention `formal_claim`; the correspondence is not proved by
  `Iff.rfl`/`rfl`;
* in Lean: the bodies of `formal_claim` and `paper_claim` differ, the two are not
  definitionally equal, the correspondence proof does not reach the main theorem, the main
  theorem's statement is `formal_claim`, `paper_claim_holds` goes through the correspondence,
  and `#print axioms` shows only the three standard axioms.

What it cannot check: whether the transcription is the right reading of the English. That
reading is fixed once, in writing, below and in `Semantics.lean`, and is the author's sign-off.

## Running the gate locally

```
lake exe cache get
bash scripts/verify-lock.sh
```

Reports are written to `truth-gate-report/`.

## The locked claim of this repository

* Paper: `paper/metriplectic-world-model.tex`
* sha256: `c9ec8a5318183d43b11e4c7054f765ea42c2cf6633d28d1c6531f53ce9629c13`
* Section: Section "Ceiling and stretching" (sec:ceiling), the whole theorem `uniform_ceiling` (uniform ceiling, absorbing set, antitone in κ, no ceiling at κ = 0)
* Main theorem(s): `MetriplecticWorldModel.uniform_ceiling_full`
* Lock file: `TRUTH_GATE.lock`; semantics: `MetriplecticWorldModel/Semantics.lean`

Verbatim quote:

```
\begin{theorem}\lean{uniform_ceiling}\coined: if $M'\le CM^2-\kappa M^3$ and $\kappa>0$, then
\begin{equation}\label{eq:ceiling}M(t)\le\max\bigl(M(0),\max(C/\kappa,0)\bigr)\qquad(t\ge0).\end{equation} Also \lean{absorbing}, \lean{ceiling_antitone_kappa}, \lean{kappa_zero_no_ceiling}\coined{} (at $\kappa=0$, $1/(1-t)$ satisfies $M'\le M^2$ and blows up). Explicitly, for $\kappa>0$ and $C\ge0$: if $M(0)\le C/\kappa$, then $M(t)\le C/\kappa$ for all $t\ge0$ (\lean{absorbing}); and for any $M_0$ and $0<\kappa_1\le\kappa_2$, $\max\bigl(M_0,\max(C/\kappa_2,0)\bigr)\le\max\bigl(M_0,\max(C/\kappa_1,0)\bigr)$ (\lean{ceiling_antitone_kappa}). At $\kappa=0$, $M(t)=1/(1-t)$ satisfies $M'(t)\le M(t)^2$ for $t<1$ and is unbounded on $[0,1)$ (\lean{kappa_zero_no_ceiling}). The four statements together are \lean{uniform_ceiling_full}.\end{theorem}
```

```lean
def formal_claim : Prop :=
  (∀ (C κ : ℝ), 0 < κ → ∀ (M M' : ℝ → ℝ),
      (∀ t, 0 ≤ t → HasDerivAt M (M' t) t) →
      (∀ t, 0 ≤ t → M' t ≤ C * M t ^ 2 - κ * M t ^ 3) →
      ∀ t, 0 ≤ t → M t ≤ MetriplecticWorldModel.ceiling (M 0) C κ) ∧
    (∀ (C κ : ℝ), 0 < κ → 0 ≤ C → ∀ (M M' : ℝ → ℝ),
      (∀ t, 0 ≤ t → HasDerivAt M (M' t) t) →
      (∀ t, 0 ≤ t → M' t ≤ C * M t ^ 2 - κ * M t ^ 3) → M 0 ≤ C / κ →
      ∀ t, 0 ≤ t → M t ≤ C / κ) ∧
    (∀ (M0 C : ℝ), 0 ≤ C → ∀ (κ₁ κ₂ : ℝ), 0 < κ₁ → κ₁ ≤ κ₂ →
      MetriplecticWorldModel.ceiling M0 C κ₂ ≤ MetriplecticWorldModel.ceiling M0 C κ₁) ∧
    ((∀ t : ℝ, t < 1 → ∃ d : ℝ, HasDerivAt (fun s : ℝ => (1 - s)⁻¹) d t ∧
        d ≤ 1 * ((1 - t)⁻¹) ^ 2 - 0 * ((1 - t)⁻¹) ^ 3) ∧
      ¬ ∃ B, ∀ t ∈ Set.Ico (0:ℝ) 1, (1 - t)⁻¹ ≤ B)

def paper_claim : Prop :=
  (∀ (C κ : ℝ) (M : ℝ → ℝ),
      (∀ t : ℝ, 0 ≤ t → DifferentiableAt ℝ M t) →
      (∀ t : ℝ, 0 ≤ t → deriv M t ≤ C * M t ^ 2 - κ * M t ^ 3) →
      0 < κ →
      ∀ t : ℝ, 0 ≤ t → M t ≤ max (M 0) (max (C / κ) 0)) ∧
    (∀ (C κ : ℝ) (M : ℝ → ℝ),
      (∀ t : ℝ, 0 ≤ t → DifferentiableAt ℝ M t) →
      (∀ t : ℝ, 0 ≤ t → deriv M t ≤ C * M t ^ 2 - κ * M t ^ 3) →
      0 < κ → 0 ≤ C → M 0 ≤ C / κ →
      ∀ t : ℝ, 0 ≤ t → M t ≤ C / κ) ∧
    (∀ (M₀ C κ₁ κ₂ : ℝ), 0 ≤ C → 0 < κ₁ → κ₁ ≤ κ₂ →
      max M₀ (max (C / κ₂) 0) ≤ max M₀ (max (C / κ₁) 0)) ∧
    ((∀ t : ℝ, t < 1 → DifferentiableAt ℝ (fun s : ℝ => 1 / (1 - s)) t ∧
        deriv (fun s : ℝ => 1 / (1 - s)) t ≤ (1 / (1 - t)) ^ 2) ∧
      ¬ ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t → t < 1 → 1 / (1 - t) ≤ B)
```

See the doc comment of `MetriplecticWorldModel/Semantics.lean` for the fixed reading of the paper's terms, the scope and the non-vacuity witness.

## Re-audit (2026-11-16): the earlier lock was NOT certifying (superseded by the re-lock below)

Status at the re-audit: **REOPENED. The gate was red on purpose.** `TRUTH_GATE.lock` carries `"certifying": false`, and
`scripts/truth_gate_check.py` fails while it does. Nothing was deleted: `Semantics.lean`, the quotes,
the hashes and the history are unchanged.

Rule applied (Benjamin Stanley Frohman, 2026-11-16):
* There are no partial locks. A lock certifies only a step on the correct path to the full theorem
  that is kernel-proved as the actual true answer, so that the next step can build on it.
* Drifted, dummy, placeholder or stand-in types, names or categories are rejected.
* Cross-ontology connections are not rejected for looking unrelated. The kernel check, and whether
  the piece genuinely helps reach the full structured proof, decide.
* `paper_claim` is an independent transcription of the verbatim paper quote, never an alias of
  `formal_claim`, and the correspondence is never `rfl`/`Iff.rfl`.

Locked claim under review: uniform_ceiling (theorem uniform_ceiling, first sentence only)

Why it is reopened:
* Partial lock. Only the first sentence of theorem `uniform_ceiling` is locked. The same theorem also states `absorbing`, `ceiling_antitone_kappa` and `kappa_zero_no_ceiling`, and those are not locked.
* The comparison inequality M′ ≤ CM² − κM³ is a hypothesis. The paper relabels the results that use `StretchingCZ` as model-only ("false as a sup-norm bound for Navier–Stokes"), so this lock does not certify a step on a Navier–Stokes path by itself.

What would re-certify it: A lock needs the complete theorem as stated, independently transcribed. Its role on the paper's path (tethered model versus Navier–Stokes) also has to be stated.

## Re-lock (2026-11-16): full lock, certifying

With Benjamin Stanley Frohman's approval of 2026-11-16, the lock was replaced by a full lock:
the whole theorem `uniform_ceiling` of Section "Ceiling and stretching": uniform ceiling, absorbing set, antitone in κ, and no ceiling at κ = 0 (new main theorem `uniform_ceiling_full`, the conjunction of `uniform_ceiling`, `absorbing`, `ceiling_antitone_kappa`, `kappa_zero_no_ceiling`). The paper's theorem gained one sentence ("Explicitly, …") stating the `absorbing` and `ceiling_antitone_kappa` clauses in English, which the paper previously cited by Lean name only; the paper sha256 changed from 02172077… to c9ec8a53…. That sentence needs the author's sign-off.

Previous main theorem(s): `MetriplecticWorldModel.uniform_ceiling`. New main theorem(s): `MetriplecticWorldModel.uniform_ceiling_full`. `TRUTH_GATE.lock` is back to `"certifying": true`; the reopen record is kept under `reaudit_history`.
All rules still apply: no `sorry`/`admit`/`native_decide`/new axioms; only `propext`, `Classical.choice`, `Quot.sound`;
`paper_claim` is an independent transcription of the verbatim quote; the correspondence is substantive (not `rfl`/`Iff.rfl`)
and does not use the main theorems; a non-vacuity witness is proved in `MetriplecticWorldModel/Semantics.lean`.
