/-
Copyright (c) 2026 Benjamin Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Frohman (prepared with assistance from Grok; not a co-author).

# Layer 2 — abstract analytic corollary (build_context rules, June 2026)

Rules (citing the May 20 manuscript): `ε = κ/4` (Young absorption),
`κ'' = ½κ − C_abs > 0`, comparison ODE `y' = C y² − κ'' y³`, equilibria `y = 0`
(unstable) and `y = C/κ''` (stable), bound `y(t) ≤ max(y(0), C/κ'')`.

**Scope.** This is a real-variable statement about any function obeying the
differential inequality. It does *not* derive that inequality from Navier–Stokes and
claims no Navier–Stokes regularity.
-/
import Mathlib.Analysis.Calculus.MeanValue

namespace Frohman.Tether

/-- `κ'' = ½κ − C_abs`. -/
noncomputable def kappaDD (κ Cabs : ℝ) : ℝ := κ / 2 - Cabs

/-- The comparison vector field `f(y) = C y² − κ'' y³`. -/
def comparisonField (C κ'' y : ℝ) : ℝ := C * y ^ 2 - κ'' * y ^ 3

/-- **Young absorption with `ε = κ/4`:** `a b ≤ (κ/4) a² + b²/κ` for `κ > 0`. -/
theorem young_absorption {κ : ℝ} (hκ : 0 < κ) (a b : ℝ) :
    a * b ≤ (κ / 4) * a ^ 2 + b ^ 2 / κ := by
  have h : 0 ≤ (κ * a - 2 * b) ^ 2 / (4 * κ) := by positivity
  have e : (κ / 4) * a ^ 2 + b ^ 2 / κ - a * b = (κ * a - 2 * b) ^ 2 / (4 * κ) := by
    field_simp; ring
  linarith

theorem comparisonField_zero (C κ'' : ℝ) : comparisonField C κ'' 0 = 0 := by
  simp [comparisonField]

theorem comparisonField_equilibrium (C : ℝ) {κ'' : ℝ} (h : 0 < κ'') :
    comparisonField C κ'' (C / κ'') = 0 := by
  unfold comparisonField; field_simp; ring

/-- Above the stable equilibrium the field points down (attracting from above). -/
theorem comparisonField_neg_above {C κ'' y : ℝ} (h : 0 < κ'') (hy0 : 0 < y)
    (hy : C / κ'' < y) : comparisonField C κ'' y < 0 := by
  have : C < κ'' * y := by rw [div_lt_iff₀ h] at hy; linarith
  unfold comparisonField
  have : y ^ 2 * (C - κ'' * y) < 0 := mul_neg_of_pos_of_neg (by positivity) (by linarith)
  nlinarith

/-- Between the equilibria the field points up: `0` is unstable, `C/κ''` attracts
from below. -/
theorem comparisonField_pos_between {C κ'' y : ℝ} (h : 0 < κ'') (hy0 : 0 < y)
    (hy : y < C / κ'') : 0 < comparisonField C κ'' y := by
  have : κ'' * y < C := by rw [lt_div_iff₀ h] at hy; linarith
  unfold comparisonField
  have : 0 < y ^ 2 * (C - κ'' * y) := mul_pos (by positivity) (by linarith)
  nlinarith

/-- Auxiliary: `y` stays below every constant `M > max(y(0), C/κ'')`. -/
theorem comparison_bound_of_gt {y y' : ℝ → ℝ} {C κ'' T : ℝ} (hκ : 0 < κ'')
    (hy0 : 0 ≤ y 0) (hc : ContinuousOn y (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ico 0 T, HasDerivWithinAt y (y' x) (Set.Ici x) x)
    (hineq : ∀ x ∈ Set.Ico 0 T, y' x ≤ comparisonField C κ'' (y x))
    {M : ℝ} (hM : max (y 0) (C / κ'') < M) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ M := by
  have hM0 : 0 < M := lt_of_le_of_lt hy0 (lt_of_le_of_lt (le_max_left _ _) hM)
  have hMC : C / κ'' < M := lt_of_le_of_lt (le_max_right _ _) hM
  intro t ht
  exact image_le_of_deriv_right_lt_deriv_boundary' (f := y) (f' := y')
    (a := 0) (b := T) (B := fun _ => M) (B' := fun _ => 0) hc hd
    (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hM)) continuousOn_const
    (fun x _ => hasDerivWithinAt_const _ _ _)
    (fun x hx hyx => lt_of_le_of_lt (hineq x hx)
      (by rw [hyx]; exact comparisonField_neg_above hκ hM0 hMC)) ht

/-- **Comparison bound.** If `y(0) ≥ 0`, `y` is continuous on `[0,T]`, has right
derivative `y'` on `[0,T)` with `y' ≤ C y² − κ'' y³`, and `κ'' > 0`, then
`y(t) ≤ max(y(0), C/κ'')` on `[0,T]`. -/
theorem comparison_bound {y y' : ℝ → ℝ} {C κ'' T : ℝ} (hκ : 0 < κ'')
    (hy0 : 0 ≤ y 0) (hc : ContinuousOn y (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ico 0 T, HasDerivWithinAt y (y' x) (Set.Ici x) x)
    (hineq : ∀ x ∈ Set.Ico 0 T, y' x ≤ comparisonField C κ'' (y x)) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ max (y 0) (C / κ'') := by
  intro t ht
  refine le_of_forall_gt fun M hM => ?_
  have h := comparison_bound_of_gt hκ hy0 hc hd hineq
    (M := (max (y 0) (C / κ'') + M) / 2) (by linarith) t ht
  linarith

/-- Layer-2 corollary with the build_context constants: `κ'' = ½κ − C_abs > 0`. -/
theorem layer2_bound {y y' : ℝ → ℝ} {C κ Cabs T : ℝ} (hκ : 0 < kappaDD κ Cabs)
    (hy0 : 0 ≤ y 0) (hc : ContinuousOn y (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ico 0 T, HasDerivWithinAt y (y' x) (Set.Ici x) x)
    (hineq : ∀ x ∈ Set.Ico 0 T, y' x ≤ C * y x ^ 2 - kappaDD κ Cabs * y x ^ 3) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ max (y 0) (C / kappaDD κ Cabs) :=
  comparison_bound hκ hy0 hc hd hineq

end Frohman.Tether
