/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import MetriplecticWorldModel.CeilingFull

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/metriplectic-world-model.tex
PAPER_SECTION: Section "Ceiling and stretching" (sec:ceiling), the whole theorem `uniform_ceiling` (uniform ceiling, absorbing set, antitone in κ, no ceiling at κ = 0)
PAPER_SHA256: c9ec8a5318183d43b11e4c7054f765ea42c2cf6633d28d1c6531f53ce9629c13

Locked paper claim, quoted verbatim (the whole theorem):

PAPER_QUOTE_BEGIN
\begin{theorem}\lean{uniform_ceiling}\coined: if $M'\le CM^2-\kappa M^3$ and $\kappa>0$, then
\begin{equation}\label{eq:ceiling}M(t)\le\max\bigl(M(0),\max(C/\kappa,0)\bigr)\qquad(t\ge0).\end{equation} Also \lean{absorbing}, \lean{ceiling_antitone_kappa}, \lean{kappa_zero_no_ceiling}\coined{} (at $\kappa=0$, $1/(1-t)$ satisfies $M'\le M^2$ and blows up). Explicitly, for $\kappa>0$ and $C\ge0$: if $M(0)\le C/\kappa$, then $M(t)\le C/\kappa$ for all $t\ge0$ (\lean{absorbing}); and for any $M_0$ and $0<\kappa_1\le\kappa_2$, $\max\bigl(M_0,\max(C/\kappa_2,0)\bigr)\le\max\bigl(M_0,\max(C/\kappa_1,0)\bigr)$ (\lean{ceiling_antitone_kappa}). At $\kappa=0$, $M(t)=1/(1-t)$ satisfies $M'(t)\le M(t)^2$ for $t<1$ and is unbounded on $[0,1)$ (\lean{kappa_zero_no_ceiling}). The four statements together are \lean{uniform_ceiling_full}.\end{theorem}
PAPER_QUOTE_END

Reading of the paper's terms: `M : ℝ → ℝ` is differentiable at every `t ≥ 0` and `M'` is its
derivative (`deriv M`); the differential inequality `M' ≤ C M² - κ M³` and the conclusions are
asserted for `t ≥ 0`; `C` is any real number unless `C ≥ 0` is stated. In the absorbing clause the
differential inequality of the theorem's first sentence is in force. At `κ = 0`, `M(t) = 1/(1-t)`
on `t < 1`, `M'(t)` is its derivative (which exists there), and "unbounded on `[0,1)`" means no
real `B` bounds it on `0 ≤ t < 1`.

Provenance note (2026-11-16): the sentence beginning "Explicitly," was added to the paper in the
re-lock PR so that the `absorbing` and `ceiling_antitone_kappa` clauses, previously cited by Lean
name only, have English statements to transcribe. It needs the author's sign-off.

`formal_claim` is the statement of `MetriplecticWorldModel.uniform_ceiling_full`, the conjunction
of `uniform_ceiling`, `absorbing`, `ceiling_antitone_kappa` and the existential form of
`kappa_zero_no_ceiling`, which take the derivative as a separate function / value with
`HasDerivAt` and use the repository's `ceiling` and `(1 - t)⁻¹`. The correspondence identifies
the derivative with `deriv` (`HasDerivAt.deriv`), unfolds `ceiling`, and rewrites `1/(1-t)`; it
is not definitional.

Non-vacuity: `nonvacuity_witness` below gives `C = 1`, `κ = 1`, `M ≡ 1/2`, which satisfies the
hypotheses of the ceiling and absorbing clauses (`M' = 0 ≤ 1/4 - 1/8`, `M(0) = 1/2 ≤ 1 = C/κ`).

Scope: a scalar comparison-ODE fact inside the tethered model. It says nothing about the
unmodified Navier-Stokes system and makes no claim about the Clay Millennium problem.
-/

namespace TruthGate

-- TRUTH-GATE LOCK BEGIN
/-- The repository's statement (`MetriplecticWorldModel.uniform_ceiling_full`). -/
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

/-- Paper, theorem `uniform_ceiling` in full: (i) if `M' ≤ C M² - κ M³` and `κ > 0`, then
`M(t) ≤ max(M(0), max(C/κ, 0))` for `t ≥ 0`; (ii) if also `C ≥ 0` and `M(0) ≤ C/κ`, then
`M(t) ≤ C/κ` for `t ≥ 0`; (iii) for `C ≥ 0`, `0 < κ₁ ≤ κ₂` and any `M₀`,
`max(M₀, max(C/κ₂, 0)) ≤ max(M₀, max(C/κ₁, 0))`; (iv) at `κ = 0`, `M(t) = 1/(1-t)` satisfies
`M'(t) ≤ M(t)²` for `t < 1` and is unbounded on `[0, 1)`. -/
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

theorem one_div_fun : (fun s : ℝ => 1 / (1 - s)) = fun s : ℝ => (1 - s)⁻¹ := by
  funext s; exact one_div _

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · rintro ⟨h1, h2, h3, h4a, h4b⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro C κ M hd hle hκ t ht
      have key := h1 C κ hκ M (deriv M) (fun s hs => (hd s hs).hasDerivAt) hle t ht
      simpa [MetriplecticWorldModel.ceiling] using key
    · intro C κ M hd hle hκ hC h0 t ht
      exact h2 C κ hκ hC M (deriv M) (fun s hs => (hd s hs).hasDerivAt) hle h0 t ht
    · intro M₀ C κ₁ κ₂ hC h1' h12
      simpa [MetriplecticWorldModel.ceiling] using h3 M₀ C hC κ₁ κ₂ h1' h12
    · intro t ht
      obtain ⟨d, hd, hle⟩ := h4a t ht
      rw [one_div_fun]
      refine ⟨hd.differentiableAt, ?_⟩
      rw [hd.deriv, one_div]
      simpa using hle
    · rintro ⟨B, hB⟩
      exact h4b ⟨B, fun t ht => by simpa [one_div] using hB t ht.1 ht.2⟩
  · rintro ⟨p1, p2, p3, p4a, p4b⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro C κ hκ M M' hM hle t ht
      have hd : ∀ s : ℝ, 0 ≤ s → DifferentiableAt ℝ M s :=
        fun s hs => (hM s hs).differentiableAt
      have hle' : ∀ s : ℝ, 0 ≤ s → deriv M s ≤ C * M s ^ 2 - κ * M s ^ 3 := by
        intro s hs
        rw [(hM s hs).deriv]
        exact hle s hs
      have key := p1 C κ M hd hle' hκ t ht
      simpa [MetriplecticWorldModel.ceiling] using key
    · intro C κ hκ hC M M' hM hle h0 t ht
      have hd : ∀ s : ℝ, 0 ≤ s → DifferentiableAt ℝ M s :=
        fun s hs => (hM s hs).differentiableAt
      have hle' : ∀ s : ℝ, 0 ≤ s → deriv M s ≤ C * M s ^ 2 - κ * M s ^ 3 := by
        intro s hs
        rw [(hM s hs).deriv]
        exact hle s hs
      exact p2 C κ M hd hle' hκ hC h0 t ht
    · intro M0 C hC κ₁ κ₂ h1' h12
      simpa [MetriplecticWorldModel.ceiling] using p3 M0 C κ₁ κ₂ hC h1' h12
    · intro t ht
      obtain ⟨hdiff, hle⟩ := p4a t ht
      rw [one_div_fun] at hdiff hle
      refine ⟨_, hdiff.hasDerivAt, ?_⟩
      rw [one_div] at hle
      simpa using hle
    · rintro ⟨B, hB⟩
      exact p4b ⟨B, fun t h0 h1' => by simpa [one_div] using hB t ⟨h0, h1'⟩⟩
-- TRUTH-GATE LOCK END

/-- The repository's theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim :=
  MetriplecticWorldModel.uniform_ceiling_full

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

/-- Non-vacuity witness: `C = 1`, `κ = 1`, `M ≡ 1/2` satisfies every hypothesis of clauses (i)
and (ii) of `paper_claim` (`M' = 0 ≤ 1/4 - 1/8`, `κ > 0`, `C ≥ 0`, `M(0) = 1/2 ≤ C/κ`). -/
theorem nonvacuity_witness :
    (∀ t : ℝ, 0 ≤ t → DifferentiableAt ℝ (fun _ : ℝ => (1 / 2 : ℝ)) t) ∧
    (∀ t : ℝ, 0 ≤ t → deriv (fun _ : ℝ => (1 / 2 : ℝ)) t ≤
      1 * (fun _ : ℝ => (1 / 2 : ℝ)) t ^ 2 - 1 * (fun _ : ℝ => (1 / 2 : ℝ)) t ^ 3) ∧
    (0 : ℝ) < 1 ∧ (0 : ℝ) ≤ 1 ∧ (fun _ : ℝ => (1 / 2 : ℝ)) 0 ≤ 1 / 1 := by
  refine ⟨fun _ _ => differentiableAt_const _, fun t _ => ?_, by norm_num, by norm_num, by norm_num⟩
  simp only [deriv_const]
  norm_num

end TruthGate
