/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.RegularizedKernel

/-!
# Newton-potential step 3 (closed): `Δ(N ⋆ g) = −4π g`
-/

open NavierStokes3D MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace

namespace MetriplecticWorldModel

local notation "e" i => (EuclideanSpace.single i (1 : ℝ) : T3)

/-- One coordinate of the Laplacian moved across by two integrations by parts. -/
theorem integral_mul_dd_eq {K g : T3 → ℝ} (hK : ContDiff ℝ 2 K) (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (v : T3) :
    ∫ y, K y * fderiv ℝ (fun z => fderiv ℝ g z v) y v =
      ∫ y, fderiv ℝ (fun z => fderiv ℝ K z v) y v * g y := by
  have hK1 : ContDiff ℝ 1 (fun z => fderiv ℝ K z v) :=
    (hK.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hg1 : ContDiff ℝ 1 (fun z => fderiv ℝ g z v) :=
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have cK0 := hK.continuous
  have cK1 := hK1.continuous
  have cK2 : Continuous (fun y => fderiv ℝ (fun z => fderiv ℝ K z v) y v) :=
    (hK1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have cg0 := hg.continuous
  have cg1 := hg1.continuous
  have cg2 : Continuous (fun y => fderiv ℝ (fun z => fderiv ℝ g z v) y v) :=
    (hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have sg1 : HasCompactSupport (fun z => fderiv ℝ g z v) := hc.fderiv_apply (𝕜 := ℝ) v
  have sg2 : HasCompactSupport (fun y => fderiv ℝ (fun z => fderiv ℝ g z v) y v) :=
    sg1.fderiv_apply (𝕜 := ℝ) v
  have I : ∀ {a b : T3 → ℝ}, Continuous a → Continuous b → HasCompactSupport b →
      Integrable (fun y => a y * b y) (MeasureTheory.volume : Measure T3) := fun ha hb hs =>
    (ha.mul hb).integrable_of_hasCompactSupport (hs.mul_left)
  have step1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (MeasureTheory.volume : Measure T3)) (f := K) (g := fun z => fderiv ℝ g z v) (v := v)
    (I cK1 cg1 sg1) (I cK0 cg2 sg2) (I cK0 cg1 sg1)
    (fun x _ => hK.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) x) (fun x _ => hg1.differentiable one_ne_zero x)
  have step2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (MeasureTheory.volume : Measure T3)) (f := fun z => fderiv ℝ K z v) (g := g) (v := v)
    (I cK2 cg0 hc) (I cK1 cg1 sg1) (I cK1 cg0 hc)
    (fun x _ => hK1.differentiable one_ne_zero x) (fun x _ => hg.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) x)
  rw [step1, step2, neg_neg]

/-- **Green's identity on ℝ³ for compactly supported `g`** (no boundary terms):
`∫ K Δg = ∫ (ΔK) g`. -/
theorem integral_mul_scalarLaplacian_eq {K g : T3 → ℝ} (hK : ContDiff ℝ 2 K)
    (hg : ContDiff ℝ 2 g) (hc : HasCompactSupport g) :
    ∫ y, K y * scalarLaplacian g y = ∫ y, scalarLaplacian K y * g y := by
  have cK0 := hK.continuous
  have term : ∀ (L : T3 → ℝ) (hL : ContDiff ℝ 2 L) (i : Fin 3),
      Continuous (fun y => fderiv ℝ (fun z => fderiv ℝ L z (e i)) y (e i)) := fun L hL i =>
    ((((hL.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
      one_ne_zero).clm_apply continuous_const)
  have sg2 : ∀ i : Fin 3, HasCompactSupport
      (fun y => fderiv ℝ (fun z => fderiv ℝ g z (e i)) y (e i)) := fun i =>
    (hc.fderiv_apply (𝕜 := ℝ) _).fderiv_apply (𝕜 := ℝ) _
  unfold scalarLaplacian
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finset_sum, integral_finset_sum]
  · exact Finset.sum_congr rfl (fun i _ => integral_mul_dd_eq hK hg hc _)
  · intro i _
    exact ((term K hK i).mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left
  · intro i _
    exact (cK0.mul (term g hg i)).integrable_of_hasCompactSupport (sg2 i).mul_left


/-! ### Translation and the regularized kernel -/

theorem scalarLaplacian_comp_sub (f : T3 → ℝ) (a y : T3) :
    scalarLaplacian (fun z => f (z - a)) y = scalarLaplacian f (y - a) := by
  unfold scalarLaplacian
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have : (fun z => fderiv ℝ (fun w => f (w - a)) z (e i)) =
      fun z => (fun w => fderiv ℝ f w (e i)) (z - a) := by
    funext z; rw [fderiv_comp_sub]
  rw [this]
  have h2 := fderiv_comp_sub (𝕜 := ℝ) (f := fun w => fderiv ℝ f w (e i)) (x := y) a
  beta_reduce at h2 ⊢
  rw [h2]

theorem contDiff_regNewton {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ 2 (regNewton ε) := by
  unfold regNewton
  refine ((contDiff_norm_sq ℝ).add contDiff_const).rpow_const_of_ne (fun y => ?_)
  have : 0 < ε ^ 2 := by positivity
  positivity

theorem regNewton_neg (ε : ℝ) (y : T3) : regNewton ε (-y) = regNewton ε y := by
  simp [regNewton]

/-- **Step (a):** `(N_ε ⋆ Δg)(x) = ∫ (Δ N_ε)(y − x) g(y) dy`. -/
theorem regNewton_conv_laplacian {ε : ℝ} (hε : ε ≠ 0) {g : T3 → ℝ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (x : T3) :
    ∫ t, regNewton ε t * scalarLaplacian g (x - t) =
      ∫ y, scalarLaplacian (regNewton ε) (y - x) * g y := by
  have h1 : ∫ t, regNewton ε t * scalarLaplacian g (x - t) =
      ∫ y, regNewton ε (y - x) * scalarLaplacian g y := by
    rw [← integral_sub_left_eq_self (fun y => regNewton ε (y - x) * scalarLaplacian g y)
      (μ := (MeasureTheory.volume : Measure T3)) x]
    congr 1; funext t
    simp only [sub_sub_cancel_left, regNewton_neg]
  have hK : ContDiff ℝ 2 (fun y => regNewton ε (y - x)) :=
    (contDiff_regNewton hε).comp (contDiff_id.sub contDiff_const)
  rw [h1, integral_mul_scalarLaplacian_eq hK hg hc]
  simp_rw [scalarLaplacian_comp_sub]

theorem regPeak_scale {ε : ℝ} (hε : 0 < ε) (z : T3) :
    ε⁻¹ ^ 3 * regPeak (ε⁻¹ • z) =
      (4 * Real.pi)⁻¹ * (3 * ε ^ 2 * (‖z‖ ^ 2 + ε ^ 2) ^ (-(5 / 2 : ℝ))) := by
  unfold regPeak
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hε]
  have h : (ε⁻¹ * ‖z‖) ^ 2 + 1 = (ε ^ 2)⁻¹ * (‖z‖ ^ 2 + ε ^ 2) := by
    field_simp
  have h5 : ((ε ^ 2)⁻¹) ^ (-(5 / 2 : ℝ)) = ε ^ 5 := by
    rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv,
      ← Real.rpow_natCast ε 2, ← Real.rpow_mul hε.le]
    norm_num
  rw [h, Real.mul_rpow (by positivity) (by positivity), h5]
  field_simp

/-! ### Step (b): `ε → 0` by dominated convergence -/

theorem ae_ne_zero_T3 : ∀ᵐ t ∂(MeasureTheory.volume : Measure T3), t ≠ 0 := by
  rw [ae_iff]; simp

theorem integrable_newtonRadial_mul {h : T3 → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (x : T3) : Integrable (fun t => newtonRadial t * h (x - t)) (MeasureTheory.volume : Measure T3) := by
  have := hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
    locallyIntegrable_newtonRadial hh x
  simpa [ConvolutionExistsAt] using this

theorem tendsto_regNewton_conv {h : T3 → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (x : T3) :
    Tendsto (fun ε => ∫ t, regNewton ε t * h (x - t)) (𝓝 0)
      (𝓝 (∫ t, newtonRadial t * h (x - t))) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun t => newtonRadial t * |h (x - t)|)
    (Eventually.of_forall (fun ε => ?_)) (Eventually.of_forall (fun ε => ?_))
    (integrable_newtonRadial_mul hh.abs hc.abs x) ?_
  · have hm : Measurable (regNewton ε) := by unfold regNewton; fun_prop
    exact (hm.aestronglyMeasurable.mul
      (hh.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · filter_upwards [ae_ne_zero_T3] with t ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (regNewton_nonneg ε t)]
    exact mul_le_mul_of_nonneg_right (regNewton_le ε ht) (abs_nonneg _)
  · filter_upwards [ae_ne_zero_T3] with t ht
    exact (tendsto_regNewton ht).mul_const _

/-! ### Step (c): `Δ(N ⋆ g) = N ⋆ Δg` -/

theorem newtonPotential_apply (h : T3 → ℝ) (x : T3) :
    newtonPotential h x = ∫ t, newtonRadial t * h (x - t) := by
  simp [newtonPotential, convolution_def]

theorem fderiv_newtonPotential_apply {h : T3 → ℝ} (hc : HasCompactSupport h) (hh : ContDiff ℝ 1 h)
    (v : T3) :
    (fun y => fderiv ℝ (newtonPotential h) y v) = newtonPotential (fun z => fderiv ℝ h z v) := by
  funext y
  rw [(hasFDerivAt_newtonPotential hc hh y).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.lsmul ℝ ℝ) locallyIntegrable_newtonRadial (hc.fderiv (𝕜 := ℝ))
    (hh.continuous_fderiv one_ne_zero) y v

theorem scalarLaplacian_newtonPotential {g : T3 → ℝ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (x : T3) :
    scalarLaplacian (newtonPotential g) x = ∫ t, newtonRadial t * scalarLaplacian g (x - t) := by
  unfold scalarLaplacian
  have hg1 : ∀ i : Fin 3, ContDiff ℝ 1 (fun z => fderiv ℝ g z (e i)) := fun i =>
    (hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have cont2 : ∀ i : Fin 3, Continuous (fun z => fderiv ℝ (fun w => fderiv ℝ g w (e i)) z (e i)) :=
    fun i => ((hg1 i).continuous_fderiv one_ne_zero).clm_apply continuous_const
  have step : ∀ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ (newtonPotential g) y (e i)) x (e i) =
        ∫ t, newtonRadial t * fderiv ℝ (fun w => fderiv ℝ g w (e i)) (x - t) (e i) := by
    intro i
    rw [fderiv_newtonPotential_apply hc (hg.of_le (by norm_num)),
      congrFun (fderiv_newtonPotential_apply (hc.fderiv_apply (𝕜 := ℝ) _) (hg1 i) (e i)) x,
      newtonPotential_apply]
  simp_rw [step, Finset.mul_sum]
  rw [integral_finset_sum]
  intro i _
  exact integrable_newtonRadial_mul (cont2 i) ((hc.fderiv_apply (𝕜 := ℝ) _).fderiv_apply (𝕜 := ℝ) _) x

/-! ### Assembly -/

/-- **Newton potential, step 3 (closed):** for `g ∈ C²_c(ℝ³)`, `Δ(N ⋆ g) = −4π g` pointwise,
where `N(y) = 1/|y|`. No hypotheses beyond smoothness and compact support. -/
theorem scalarLaplacian_newtonPotential_eq {g : T3 → ℝ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (x : T3) :
    scalarLaplacian (newtonPotential g) x = -(4 * Real.pi) * g x := by
  have contL : Continuous (scalarLaplacian g) := by
    unfold scalarLaplacian
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact (((hg.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  have suppL : HasCompactSupport (scalarLaplacian g) := by
    unfold scalarLaplacian
    have t := fun i : Fin 3 => (hc.fderiv_apply (𝕜 := ℝ) (e i)).fderiv_apply (𝕜 := ℝ) (e i)
    simp only [Fin.sum_univ_three]
    exact ((t 0).add (t 1)).add (t 2)
  have hB := (tendsto_regNewton_conv contL suppL x).comp tendsto_inv_atTop_zero
  rw [← scalarLaplacian_newtonPotential hg hc] at hB
  have hA := (tendsto_regPeak_approxIdentity (hg.continuous.integrable_of_hasCompactSupport hc) hg.continuous.continuousAt
    (g := g) (x₀ := x)).const_mul (-(4 * Real.pi))
  · refine tendsto_nhds_unique hB (hA.congr' ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hcpos
    have hε : 0 < c⁻¹ := inv_pos.mpr hcpos
    simp only [Function.comp]
    rw [regNewton_conv_laplacian hε.ne' hg hc, ← integral_const_mul]
    congr 1; funext y
    rw [scalarLaplacian_regNewton hε.ne', ← inv_inv c, regPeak_scale hε, norm_sub_rev]
    field_simp

end MetriplecticWorldModel
