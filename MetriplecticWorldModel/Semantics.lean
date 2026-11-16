/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import MetriplecticWorldModel.Ceiling

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/metriplectic-world-model.tex
PAPER_SECTION: Section "Ceiling and stretching" (sec:ceiling), theorem `uniform_ceiling`, first sentence
PAPER_SHA256: 02172077e81762a98db095e55a59a1cf1945cbe68cb26ecd26d0bd1fd1da68c5

Locked paper claim, quoted verbatim:

PAPER_QUOTE_BEGIN
\begin{theorem}\lean{uniform_ceiling}\coined: if $M'\le CM^2-\kappa M^3$ and $\kappa>0$, then
\begin{equation}\label{eq:ceiling}M(t)\le\max\bigl(M(0),\max(C/\kappa,0)\bigr)\qquad(t\ge0).\end{equation}
PAPER_QUOTE_END

Reading of the paper's terms: `M : ℝ → ℝ` is differentiable at every `t ≥ 0` and `M'` is its
derivative (`deriv M`); the differential inequality and the conclusion are asserted for
`t ≥ 0`; `C` is any real number.

`formal_claim` is the statement of `MetriplecticWorldModel.uniform_ceiling`, which takes the
derivative as a separate function `M'` with `HasDerivAt M (M' t) t`. The correspondence
identifies `M'` with `deriv M` (`HasDerivAt.deriv`); it is not definitional.

Scope: a scalar comparison-ODE fact inside the tethered model. It says nothing about the
unmodified Navier-Stokes system and makes no claim about the Clay Millennium problem.
-/

namespace TruthGate

-- TRUTH-GATE LOCK BEGIN
/-- The repository's statement (`MetriplecticWorldModel.uniform_ceiling`). -/
def formal_claim : Prop :=
  ∀ (C κ : ℝ), 0 < κ → ∀ (M M' : ℝ → ℝ),
    (∀ t, 0 ≤ t → HasDerivAt M (M' t) t) →
    (∀ t, 0 ≤ t → M' t ≤ C * M t ^ 2 - κ * M t ^ 3) →
    ∀ t, 0 ≤ t → M t ≤ MetriplecticWorldModel.ceiling (M 0) C κ

/-- Paper: if `M' ≤ C M² - κ M³` and `κ > 0`, then
`M(t) ≤ max(M(0), max(C/κ, 0))` for `t ≥ 0`. -/
def paper_claim : Prop :=
  ∀ (C κ : ℝ) (M : ℝ → ℝ),
    (∀ t : ℝ, 0 ≤ t → DifferentiableAt ℝ M t) →
    (∀ t : ℝ, 0 ≤ t → deriv M t ≤ C * M t ^ 2 - κ * M t ^ 3) →
    0 < κ →
    ∀ t : ℝ, 0 ≤ t → M t ≤ max (M 0) (max (C / κ) 0)

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro h C κ M hd hle hκ t ht
    have key := h C κ hκ M (deriv M) (fun s hs => (hd s hs).hasDerivAt) hle t ht
    simpa [MetriplecticWorldModel.ceiling] using key
  · intro h C κ hκ M M' hM hle t ht
    have hd : ∀ s : ℝ, 0 ≤ s → DifferentiableAt ℝ M s :=
      fun s hs => (hM s hs).differentiableAt
    have hle' : ∀ s : ℝ, 0 ≤ s → deriv M s ≤ C * M s ^ 2 - κ * M s ^ 3 := by
      intro s hs
      rw [(hM s hs).deriv]
      exact hle s hs
    have key := h C κ M hd hle' hκ t ht
    simpa [MetriplecticWorldModel.ceiling] using key
-- TRUTH-GATE LOCK END

/-- The repository's theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim := by
  intro C κ hκ M M' hM hle t ht
  exact MetriplecticWorldModel.uniform_ceiling C κ hκ M M' hM hle t ht

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
