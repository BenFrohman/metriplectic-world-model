/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Tethered Lyapunov (rebuild of the May 28 2026 layout, LOCAL)

Mirrors `Modules/TetheredLyapunov.lean` of `complete_implementation_2026-05-28`.
The May file had `ComparisonODE`, `comparison_majorant_global_bound`,
`lemma_3_1_uniform_bound_and_continuation` and `global_regularity`, all `sorry`.
Here every step that can honestly be proved is proved; the Navier–Stokes inputs are
named `Prop`s (no `sorry`, no axioms), so the remaining gap is fully visible.

Abstraction: a candidate solution is recorded by `y t` (the controlled quantity, e.g.
`‖ω(t)‖_∞`), its right derivative `y'`, and `SmoothOn T` ("the solution exists and is
C^∞ on `[0,T]`"). `Torus.lean` connects this record to an actual velocity field on 𝕋³ (`toNSTetherSolution`).
-/
import TetherMayForm.Main

namespace Frohman.Tether

/-- Data of one candidate Navier–Stokes solution as seen by the tethered Lyapunov argument. -/
structure NSTetherSolution where
  y : ℝ → ℝ
  y' : ℝ → ℝ
  SmoothOn : ℝ → Prop
  smoothOn_mono : ∀ {T T' : ℝ}, T' ≤ T → SmoothOn T → SmoothOn T'
  smoothOn_zero : SmoothOn 0
  y_zero_nonneg : 0 ≤ y 0

/-- May name kept. The comparison majorant is the constant `max(y₀, C/κ'')`
(the stable-equilibrium envelope of `y' = C y² − κ'' y³`). -/
noncomputable def ComparisonODE (C κ'' y0 : ℝ) : ℝ → ℝ := fun _ => max y0 (C / κ'')

/-- **OPEN STEP (Navier–Stokes input).** On every interval where the solution is smooth,
`y` is continuous, right-differentiable, and obeys the tethered differential inequality
`y' ≤ C y² − κ'' y³`. Deriving this from the actual 3D Navier–Stokes equations
(with the tether feedback) is the unproved part. -/
def NSTetherEnstrophyInequality (s : NSTetherSolution) (C κ'' : ℝ) : Prop :=
  ∀ T, s.SmoothOn T →
    ContinuousOn s.y (Set.Icc 0 T) ∧
    (∀ x ∈ Set.Ico 0 T, HasDerivWithinAt s.y (s.y' x) (Set.Ici x) x) ∧
    (∀ x ∈ Set.Ico 0 T, s.y' x ≤ comparisonField C κ'' (s.y x))

/-- Beale–Kato–Majda continuation (classical, not in Mathlib). Literature: J. T. Beale,
T. Kato, A. Majda, *Remarks on the breakdown of smooth solutions for the 3-D Euler equations*,
Comm. Math. Phys. 94 (1984) 61–66 (Euler; the NS case follows identically, cf. Majda–Bertozzi
2002, Thm 3.6): a smooth solution on `[0,T)` with `∫₀ᵀ ‖ω(t)‖_∞ dt < ∞` extends beyond `T`.
Here the hypothesis is `sup_{[0,T)} y < ∞`, which implies the BKM integral condition, so this
Prop is a (weaker) CONSEQUENCE of BKM. Kept as an explicit hypothesis, never an `axiom`. -/
def BKMContinuation (s : NSTetherSolution) : Prop :=
  ∀ T, 0 < T → (∀ T' < T, s.SmoothOn T') → (∃ M, ∀ t ∈ Set.Ico 0 T, s.y t ≤ M) → s.SmoothOn T

/-- Local existence / continuation (classical, not in Mathlib). Literature: H. Fujita,
T. Kato, *On the Navier–Stokes initial value problem I*, Arch. Rational Mech. Anal. 16 (1964)
269–315 (`H^{1/2}` data); T. Kato, *Strong Lᵖ-solutions of the Navier–Stokes equation in ℝᵐ*,
Math. Z. 187 (1984) 471–480. Smooth periodic data at time `T` give a smooth solution on
`[T, T+δ)` with `δ` depending on the data's norm; parabolic smoothing gives C^∞. Explicit
hypothesis, never an `axiom`. -/
def LocalContinuation (s : NSTetherSolution) : Prop :=
  ∀ T, s.SmoothOn T → ∃ δ > 0, s.SmoothOn (T + δ)

/-- Globally smooth: smooth on `[0,T]` for every `T`. -/
def GloballySmooth (s : NSTetherSolution) : Prop := ∀ T, s.SmoothOn T

/-- **comparison_majorant_global_bound** (May name; was `sorry`). -/
theorem comparison_majorant_global_bound {s : NSTetherSolution} {C κ'' : ℝ} (hκ : 0 < κ'')
    (hI : NSTetherEnstrophyInequality s C κ'') {T : ℝ} (hT : s.SmoothOn T) :
    ∀ t ∈ Set.Icc 0 T, s.y t ≤ ComparisonODE C κ'' (s.y 0) t := by
  obtain ⟨hc, hd, hi⟩ := hI T hT
  exact comparison_bound hκ s.y_zero_nonneg hc hd hi

/-- **lemma_3_1_uniform_bound_and_continuation** (May name; was `sorry` with `True`).
Uniform bound on `[0,T)` from smoothness on every earlier interval. -/
theorem lemma_3_1_uniform_bound_and_continuation {s : NSTetherSolution} {C κ'' : ℝ}
    (hκ : 0 < κ'') (hI : NSTetherEnstrophyInequality s C κ'') {T : ℝ}
    (hpre : ∀ T' < T, s.SmoothOn T') :
    ∀ t ∈ Set.Ico 0 T, s.y t ≤ max (s.y 0) (C / κ'') := by
  intro t ht
  exact comparison_majorant_global_bound hκ hI (hpre t ht.2) t ⟨ht.1, le_rfl⟩

/-- **global_regularity** (May name; was `sorry`), conditional on the named NS inputs. -/
theorem global_regularity {s : NSTetherSolution} {C κ'' : ℝ} (hκ : 0 < κ'')
    (hI : NSTetherEnstrophyInequality s C κ'') (hB : BKMContinuation s)
    (hL : LocalContinuation s) : GloballySmooth s := by
  by_contra hns
  simp only [GloballySmooth, not_forall] at hns
  obtain ⟨T0, hT0⟩ := hns
  set A := {T : ℝ | s.SmoothOn T}
  have hbdd : BddAbove A := ⟨T0, fun T hT => by
    by_contra h; exact hT0 (s.smoothOn_mono (le_of_lt (not_le.1 h)) hT)⟩
  have h0 : (0 : ℝ) ∈ A := s.smoothOn_zero
  set σ := sSup A
  have hσ0 : 0 ≤ σ := le_csSup hbdd h0
  have hpre : ∀ T' < σ, s.SmoothOn T' := by
    intro T' hT'
    obtain ⟨b, hb, hlt⟩ := exists_lt_of_lt_csSup ⟨0, h0⟩ hT'
    exact s.smoothOn_mono hlt.le hb
  have hσ : s.SmoothOn σ := by
    rcases hσ0.lt_or_eq with hpos | heq
    · exact hB σ hpos hpre ⟨_, lemma_3_1_uniform_bound_and_continuation hκ hI hpre⟩
    · rw [← heq]; exact s.smoothOn_zero
  obtain ⟨δ, hδ, hsδ⟩ := hL σ hσ
  have := le_csSup hbdd hsδ
  linarith

end Frohman.Tether
