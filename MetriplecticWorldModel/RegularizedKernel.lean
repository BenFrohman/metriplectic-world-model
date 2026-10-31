/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.NewtonKernel

/-!
# Newton-potential step 3, regularized-kernel route (partial)

* `regNewton ε y := (‖y‖² + ε²)^(-1/2)`: smooth everywhere for `ε ≠ 0`.
* `scalarLaplacian_regNewton` (**proved**): `Δ regNewton ε = −3ε² (‖y‖²+ε²)^(-5/2)` everywhere.
* `regNewton_le` (**proved**): `0 ≤ regNewton ε y ≤ newtonRadial y` (domination for ε → 0).
* `tendsto_regNewton` (**proved**): `regNewton ε y → newtonRadial y` as `ε → 0`, for `y ≠ 0`.
* `integral_regRadial` (**proved**): `∫₀^∞ r²·3ε²(r²+ε²)^(-5/2) dr = 1` (1D FTC on `Ioi 0`).
* `integral_neg_scalarLaplacian_regNewton` (**proved**): `∫_{ℝ³} 3ε²(‖y‖²+ε²)^(-5/2) = 4π`
  (polar decomposition; no sphere surface integrals).
* `tendsto_regPeak_approxIdentity` (**proved**): `−Δ regNewton / 4π` is an approximate identity.
* **Open:** `N_ε ⋆ Δg = (Δ N_ε) ⋆ g` (integration by parts on ℝ³), and passing `ε → 0`.
-/

open NavierStokes3D MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace

namespace MetriplecticWorldModel

noncomputable def regNewton (ε : ℝ) (y : T3) : ℝ := (‖y‖ ^ 2 + ε ^ 2) ^ (-(1 / 2 : ℝ))

theorem hasFDerivAt_regSq_rpow (p : ℝ) {ε : ℝ} (hε : ε ≠ 0) (y : T3) :
    HasFDerivAt (fun z : T3 => (‖z‖ ^ 2 + ε ^ 2) ^ p)
      ((p * (‖y‖ ^ 2 + ε ^ 2) ^ (p - 1)) • (2 • innerSL ℝ y)) y :=
  ((hasStrictFDerivAt_norm_sq y).hasFDerivAt.add_const (ε ^ 2)).rpow_const
    (Or.inl (by positivity))

theorem regSq_rpow_partial (p : ℝ) {ε : ℝ} (hε : ε ≠ 0) (y : T3) (i : Fin 3) :
    fderiv ℝ (fun z : T3 => (‖z‖ ^ 2 + ε ^ 2) ^ p) y (EuclideanSpace.single i 1) =
      2 * p * (‖y‖ ^ 2 + ε ^ 2) ^ (p - 1) * y i := by
  rw [(hasFDerivAt_regSq_rpow p hε y).fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  simp [inner_single_one]
  ring

theorem scalarLaplacian_regNewton {ε : ℝ} (hε : ε ≠ 0) (x : T3) :
    scalarLaplacian (regNewton ε) x = -3 * ε ^ 2 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) := by
  unfold scalarLaplacian
  have hpart : ∀ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ (regNewton ε) y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) =
      3 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) * x i * x i - (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) := by
    intro i
    have hev : (fun y => fderiv ℝ (regNewton ε) y (EuclideanSpace.single i 1)) =
        fun y => -(‖y‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) * y i := by
      funext y
      unfold regNewton
      rw [regSq_rpow_partial _ hε]
      norm_num
    rw [hev]
    have hA := (hasFDerivAt_regSq_rpow (-(3 / 2 : ℝ)) hε x).fun_neg
    have hB : HasFDerivAt (fun y : T3 => y i) (EuclideanSpace.proj i : T3 →L[ℝ] ℝ) x :=
      (EuclideanSpace.proj i : T3 →L[ℝ] ℝ).hasFDerivAt
    rw [(hA.fun_mul hB).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.neg_apply, innerSL_apply_apply]
    simp [inner_single_one]
    norm_num
    ring
  simp only [hpart, Fin.sum_univ_three]
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have hpos : 0 < ‖x‖ ^ 2 + ε ^ 2 := by positivity
  have key : (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) * (‖x‖ ^ 2 + ε ^ 2) =
      (‖x‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) := by
    conv_lhs => arg 2; rw [← Real.rpow_one (‖x‖ ^ 2 + ε ^ 2)]
    rw [← Real.rpow_add hpos]; norm_num
  rw [← key]
  have : x 0 * x 0 + x 1 * x 1 + x 2 * x 2 = ‖x‖ ^ 2 := by rw [hn]; ring
  linear_combination (3 * (‖x‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))) * this

theorem regNewton_nonneg (ε : ℝ) (y : T3) : 0 ≤ regNewton ε y := by
  unfold regNewton; positivity

theorem regNewton_le (ε : ℝ) {y : T3} (hy : y ≠ 0) : regNewton ε y ≤ newtonRadial y := by
  unfold regNewton newtonRadial
  exact Real.rpow_le_rpow_of_exponent_nonpos (by positivity)
    (by nlinarith [sq_nonneg ε]) (by norm_num)

theorem tendsto_regNewton {y : T3} (hy : y ≠ 0) :
    Tendsto (fun ε : ℝ => regNewton ε y) (𝓝 0) (𝓝 (newtonRadial y)) := by
  unfold regNewton newtonRadial
  have hc : Continuous fun ε : ℝ => ‖y‖ ^ 2 + ε ^ 2 := by continuity
  have := (hc.tendsto 0).rpow_const (p := -(1 / 2 : ℝ)) (Or.inl (by simp [hy]))
  simpa using this

/-- Antiderivative for the radial normalization: `F(r) = r³ (r²+ε²)^(-3/2)`. -/
theorem hasDerivAt_regRadialPrimitive {ε : ℝ} (hε : ε ≠ 0) (r : ℝ) :
    HasDerivAt (fun r : ℝ => r ^ 3 * (r ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)))
      (r ^ 2 * (3 * ε ^ 2 * (r ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)))) r := by
  have hq : 0 < r ^ 2 + ε ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => r ^ 2 + ε ^ 2) (2 * r) r := by
    simpa using (hasDerivAt_pow 2 r).add_const (ε ^ 2)
  have h2 := h1.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl hq.ne')
  have h3 := (hasDerivAt_pow 3 r).mul h2
  convert h3 using 1
  have key : (r ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) =
      (r ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) * (r ^ 2 + ε ^ 2) := by
    conv_rhs => arg 2; rw [← Real.rpow_one (r ^ 2 + ε ^ 2)]
    rw [← Real.rpow_add hq]; norm_num
  have key2 : (-(3 / 2 : ℝ) - 1) = -(5 / 2 : ℝ) := by norm_num
  rw [key2, key]
  push_cast
  ring

theorem tendsto_regRadialPrimitive (ε : ℝ) :
    Tendsto (fun r : ℝ => r ^ 3 * (r ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))) atTop (𝓝 1) := by
  have hev : (fun r : ℝ => (1 + ε ^ 2 * (r ^ 2)⁻¹) ^ (-(3 / 2 : ℝ))) =ᶠ[atTop]
      fun r : ℝ => r ^ 3 * (r ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) := by
    filter_upwards [eventually_gt_atTop 0] with r hr
    have hr2 : 0 < r ^ 2 := by positivity
    have : r ^ 2 + ε ^ 2 = r ^ 2 * (1 + ε ^ 2 * (r ^ 2)⁻¹) := by field_simp
    rw [this, Real.mul_rpow hr2.le (by positivity)]
    have h3 : (r ^ 2) ^ (-(3 / 2 : ℝ)) = (r ^ 3)⁻¹ := by
      rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le, ← Real.rpow_natCast r 3,
        ← Real.rpow_neg hr.le]
      norm_num
    rw [h3, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  refine Tendsto.congr' hev ?_
  have ht : Tendsto (fun r : ℝ => 1 + ε ^ 2 * (r ^ 2)⁻¹) atTop (𝓝 1) := by
    have := ((tendsto_pow_atTop (two_ne_zero)).inv_tendsto_atTop.const_mul (ε ^ 2)).const_add 1
    simpa using this
  have := ht.rpow_const (p := -(3 / 2 : ℝ)) (Or.inl one_ne_zero)
  simpa using this

/-- **Radial normalization** of the approximate identity `−Δ regNewton ε`:
`∫₀^∞ r² · 3ε² (r²+ε²)^(-5/2) dr = 1`. Multiplied by the area `4π` of the unit sphere this gives
total mass `4π`. -/
theorem integral_regRadial {ε : ℝ} (hε : ε ≠ 0) :
    ∫ r in Ioi (0 : ℝ), r ^ 2 * (3 * ε ^ 2 * (r ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))) = 1 := by
  have hc : ContinuousWithinAt (fun r : ℝ => r ^ 3 * (r ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))) (Ici 0) 0 :=
    (hasDerivAt_regRadialPrimitive hε 0).continuousAt.continuousWithinAt
  have hd : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun r : ℝ => r ^ 3 * (r ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)))
      (x ^ 2 * (3 * ε ^ 2 * (x ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)))) x :=
    fun x _ => hasDerivAt_regRadialPrimitive hε x
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ x ^ 2 * (3 * ε ^ 2 * (x ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))) :=
    fun x _ => by positivity
  have hi := integrableOn_Ioi_deriv_of_nonneg hc hd hpos (tendsto_regRadialPrimitive ε)
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hc hd hi (tendsto_regRadialPrimitive ε)]
  simp

/-- **Total mass** of the approximate identity: `∫_{ℝ³} 3ε²(‖y‖²+ε²)^(-5/2) dy = 4π`, via
Mathlib's polar decomposition `integral_fun_norm_addHaar` and `volume_ball_fin_three`. -/
theorem integral_neg_scalarLaplacian_regNewton {ε : ℝ} (hε : ε ≠ 0) :
    ∫ y : T3, 3 * ε ^ 2 * (‖y‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)) = 4 * Real.pi := by
  have h := integral_fun_norm_addHaar (MeasureTheory.volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (fun r : ℝ => 3 * ε ^ 2 * (r ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ)))
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] at h
  change ∫ y : EuclideanSpace ℝ (Fin 3), _ = _
  rw [h, integral_regRadial hε]
  simp [Measure.real, EuclideanSpace.volume_ball_fin_three]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

/-- Normalized profile of `−Δ regNewton 1 / (4π)`: a probability density on ℝ³. -/
noncomputable def regPeak (y : T3) : ℝ := (4 * Real.pi)⁻¹ * (3 * (‖y‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ)))

theorem regPeak_nonneg (y : T3) : 0 ≤ regPeak y := by
  unfold regPeak; have := Real.pi_pos; positivity

theorem integral_regPeak : ∫ y : T3, regPeak y = 1 := by
  unfold regPeak
  rw [integral_const_mul]
  have h := integral_neg_scalarLaplacian_regNewton (ε := 1) one_ne_zero
  simp only [one_pow, mul_one] at h
  rw [h]; field_simp [Real.pi_pos.ne']

theorem tendsto_regPeak_decay :
    Tendsto (fun x : T3 => ‖x‖ ^ Module.finrank ℝ T3 * regPeak x) (Bornology.cobounded T3) (𝓝 0) := by
  have hd : Module.finrank ℝ T3 = 3 := by simp
  rw [hd]
  have hq : Tendsto (fun x : T3 => ‖x‖ ^ 2 + 1) (Bornology.cobounded T3) atTop :=
    tendsto_atTop_add_const_right _ _
      ((tendsto_pow_atTop two_ne_zero).comp tendsto_norm_cobounded_atTop)
  have hinv := (hq.inv_tendsto_atTop).const_mul ((4 * Real.pi)⁻¹ * 3)
  rw [mul_zero] at hinv
  refine squeeze_zero (fun x => by have := regPeak_nonneg x; positivity) (fun x => ?_) hinv
  have hpos : 0 < ‖x‖ ^ 2 + 1 := by positivity
  have h1 : ‖x‖ ^ 3 ≤ (‖x‖ ^ 2 + 1) ^ (3 / 2 : ℝ) := by
    have : ‖x‖ ^ 3 = (‖x‖ ^ 2) ^ (3 / 2 : ℝ) := by
      rw [← Real.rpow_natCast ‖x‖ 2, ← Real.rpow_mul (norm_nonneg _)]; norm_num
    rw [this]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by norm_num)
  have h2 : (‖x‖ ^ 2 + 1) ^ (3 / 2 : ℝ) * (‖x‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ)) = (‖x‖ ^ 2 + 1)⁻¹ := by
    rw [← Real.rpow_add hpos, ← Real.rpow_neg_one]; norm_num
  unfold regPeak
  have hc : 0 ≤ (4 * Real.pi)⁻¹ * 3 * (‖x‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ)) := by
    have := Real.pi_pos; positivity
  calc ‖x‖ ^ 3 * ((4 * Real.pi)⁻¹ * (3 * (‖x‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ))))
      = ‖x‖ ^ 3 * ((4 * Real.pi)⁻¹ * 3 * (‖x‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ))) := by ring
    _ ≤ (‖x‖ ^ 2 + 1) ^ (3 / 2 : ℝ) * ((4 * Real.pi)⁻¹ * 3 * (‖x‖ ^ 2 + 1) ^ (-(5 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_right h1 hc
    _ = (4 * Real.pi)⁻¹ * 3 * (‖x‖ ^ 2 + 1)⁻¹ := by rw [← h2]; ring

/-- **Approximate identity** (Mathlib's peak-function theorem instantiated): for integrable `g`
continuous at `x₀`, `∫ c³ regPeak (c(x₀ − y)) g(y) dy → g(x₀)` as `c → ∞`. Note
`c³ regPeak (c y) = (4π)⁻¹ · (−Δ regNewton (1/c)) y` (see `scalarLaplacian_regNewton`). -/
theorem tendsto_regPeak_approxIdentity {g : T3 → ℝ} {x₀ : T3}
    (hg : Integrable g (MeasureTheory.volume : Measure T3)) (h'g : ContinuousAt g x₀) :
    Tendsto (fun c : ℝ => ∫ y : T3, (c ^ 3 * regPeak (c • (x₀ - y))) * g y) atTop (𝓝 (g x₀)) := by
  have := tendsto_integral_comp_smul_smul_of_integrable' (μ := (MeasureTheory.volume : Measure T3))
    regPeak_nonneg integral_regPeak tendsto_regPeak_decay hg h'g
  simpa using this

end MetriplecticWorldModel
