/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.BiotSavartNewton

/-!
# Biot–Savart self-adjointness and the Gâteaux derivative of helicity on the test class
-/

open NavierStokes3D ArnoldGeometric FrohmanianTether MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace

namespace MetriplecticWorldModel

local notation "e" i => (EuclideanSpace.single i (1 : ℝ) : T3)

theorem biotSavartKernel_eq (x y : T3) :
    biotSavartKernel x y = (4 * Real.pi)⁻¹ * ‖x - y‖ ^ (-(3 : ℝ)) := by
  by_cases h : x = y
  · subst h; simp [Real.zero_rpow (by norm_num : (-(3:ℝ)) ≠ 0)]
  · exact biotSavartKernel_of_ne h

theorem continuous_cross : Continuous (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
    cross p.1 p.2) := by
  unfold cross
  fun_prop

theorem inner_cross_eq (u v w : EuclideanSpace ℝ (Fin 3)) :
    ⟪cross u v, w⟫ = ⟪cross w (-v), u⟫ := by
  obtain ⟨a0, a1, a2⟩ := cross_coord u v
  obtain ⟨b0, b1, b2⟩ := cross_coord w (-v)
  simp only [PiLp.inner_apply, Fin.sum_univ_three, a0, a1, a2,
    b0, b1, b2, PiLp.neg_apply]
  simp only [inner, conj_trivial, RCLike.re_to_real]
  ring

theorem norm_cross_le (u v : EuclideanSpace ℝ (Fin 3)) : ‖cross u v‖ ≤ ‖u‖ * ‖v‖ := by
  obtain ⟨a0, a1, a2⟩ := cross_coord u v
  have h : ‖cross u v‖ ^ 2 ≤ (‖u‖ * ‖v‖) ^ 2 := by
    rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, a0, a1, a2]
    nlinarith [sq_nonneg (u 0 * v 0 + u 1 * v 1 + u 2 * v 2)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h

theorem measurable_rpow_neg_two_sub :
    Measurable (fun p : T3 × T3 => ‖p.1 - p.2‖ ^ (-(2 : ℝ))) := by fun_prop

theorem integrable_rpow_neg_two_sub {g : T3 → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    (x : T3) : Integrable (fun y => ‖x - y‖ ^ (-(2 : ℝ)) * g y) := by
  have := (integrable_rpow_neg_two_mul hg hc x).comp_sub_left x
  simpa using this

theorem continuous_conv_rpow_neg_two {g : T3 → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Continuous (fun x => ∫ y, ‖x - y‖ ^ (-(2 : ℝ)) * g y) := by
  have h := hc.continuous_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (μ := (MeasureTheory.volume : Measure T3)) locallyIntegrable_norm_rpow_neg_two hg
  convert h using 1
  funext x
  rw [convolution_def]
  rw [← integral_sub_left_eq_self _ (MeasureTheory.volume : Measure T3) x]
  simp

/-- `‖x-y‖⁻² f(x) g(y)` is integrable on `ℝ³ × ℝ³` for continuous compactly supported `f, g`. -/
theorem integrable_prod_rpow_neg_two {f g : T3 → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun p : T3 × T3 => ‖p.1 - p.2‖ ^ (-(2 : ℝ)) * (f p.1 * g p.2))
      ((MeasureTheory.volume : Measure T3).prod MeasureTheory.volume) := by
  have hm : AEStronglyMeasurable (fun p : T3 × T3 => ‖p.1 - p.2‖ ^ (-(2 : ℝ)) * (f p.1 * g p.2))
      ((MeasureTheory.volume : Measure T3).prod MeasureTheory.volume) :=
    (measurable_rpow_neg_two_sub.mul ((hf.measurable.comp measurable_fst).mul
      (hg.measurable.comp measurable_snd))).aestronglyMeasurable
  rw [integrable_prod_iff hm]
  refine ⟨Eventually.of_forall fun x => ?_, ?_⟩
  · have := (integrable_rpow_neg_two_sub hg hgc x).const_mul (f x)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only; ring
  · have hc : Continuous (fun x => |f x| * ∫ y, ‖x - y‖ ^ (-(2 : ℝ)) * |g y|) :=
      hf.abs.mul (continuous_conv_rpow_neg_two hg.abs hgc.abs)
    have hs : HasCompactSupport (fun x => |f x| * ∫ y, ‖x - y‖ ^ (-(2 : ℝ)) * |g y|) :=
      hfc.abs.mul_right
    refine (hc.integrable_of_hasCompactSupport hs).congr (Eventually.of_forall fun x => ?_)
    simp only
    rw [← integral_const_mul]
    congr 1; funext y
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    ring

theorem norm_kernel_smul_cross_le (x y : T3) (v : EuclideanSpace ℝ (Fin 3)) :
    ‖biotSavartKernel x y • cross v (x - y)‖ ≤ (4 * Real.pi)⁻¹ * (‖x - y‖ ^ (-(2 : ℝ)) * ‖v‖) := by
  by_cases h : x = y
  · subst h; simp only [biotSavartKernel_diag, zero_smul, norm_zero]; positivity
  have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  rw [norm_smul, biotSavartKernel_of_ne h, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  calc (4 * Real.pi)⁻¹ * ‖x - y‖ ^ (-(3 : ℝ)) * ‖cross v (x - y)‖
      ≤ (4 * Real.pi)⁻¹ * ‖x - y‖ ^ (-(3 : ℝ)) * (‖v‖ * ‖x - y‖) :=
        mul_le_mul_of_nonneg_left (norm_cross_le _ _) (by positivity)
    _ = (4 * Real.pi)⁻¹ * ((‖x - y‖ ^ (-(3 : ℝ)) * ‖x - y‖) * ‖v‖) := by ring
    _ = _ := by rw [← Real.rpow_add_one hn.ne']; norm_num

theorem measurable_biotSavartKernel :
    Measurable (fun p : T3 × T3 => biotSavartKernel p.1 p.2) := by
  simp_rw [biotSavartKernel_eq]; fun_prop

theorem kernel_symm (x y : T3) : biotSavartKernel x y = biotSavartKernel y x := by
  rw [biotSavartKernel_eq, biotSavartKernel_eq, norm_sub_rev]

/-- Biot–Savart integrand density in `y` is integrable for a continuous compactly supported field. -/
theorem integrable_biotSavart_density {a : T3 → EuclideanSpace ℝ (Fin 3)} (ha : Continuous a)
    (hac : HasCompactSupport a) (x : T3) :
    Integrable (fun y => biotSavartKernel x y • cross (a y) (x - y)) := by
  refine Integrable.mono' ((integrable_rpow_neg_two_sub ha.norm hac.norm x).const_mul
    (4 * Real.pi)⁻¹) ?_ (Eventually.of_forall fun y => norm_kernel_smul_cross_le x y (a y))
  have hm : Measurable (fun y => biotSavartKernel x y • cross (a y) (x - y)) :=
    (measurable_biotSavartKernel.comp (measurable_const.prodMk measurable_id)).smul
      (continuous_cross.measurable.comp (ha.measurable.prodMk (measurable_const.sub measurable_id)))
  exact hm.aestronglyMeasurable

/-- The two-point pairing density of `⟪B a, b⟫`. -/
noncomputable def bsPairDensity (a b : T3 → EuclideanSpace ℝ (Fin 3)) (p : T3 × T3) : ℝ :=
  ⟪biotSavartKernel p.1 p.2 • cross (a p.2) (p.1 - p.2), b p.1⟫

theorem integrable_bsPairDensity {a b : T3 → EuclideanSpace ℝ (Fin 3)} (ha : Continuous a)
    (hac : HasCompactSupport a) (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (bsPairDensity a b) ((MeasureTheory.volume : Measure T3).prod MeasureTheory.volume) := by
  refine Integrable.mono' ((integrable_prod_rpow_neg_two hb.norm hbc.norm ha.norm hac.norm).const_mul
    (4 * Real.pi)⁻¹) ?_ (Eventually.of_forall fun p => ?_)
  · have hm : Measurable (bsPairDensity a b) :=
      (measurable_biotSavartKernel.smul (continuous_cross.measurable.comp
        ((ha.measurable.comp measurable_snd).prodMk (measurable_fst.sub measurable_snd)))).inner
        (hb.measurable.comp measurable_fst)
    exact hm.aestronglyMeasurable
  · unfold bsPairDensity
    refine (norm_inner_le_norm _ _).trans ?_
    have := norm_kernel_smul_cross_le p.1 p.2 (a p.2)
    calc _ ≤ (4 * Real.pi)⁻¹ * (‖p.1 - p.2‖ ^ (-(2 : ℝ)) * ‖a p.2‖) * ‖b p.1‖ :=
          mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := by ring

theorem bsPairDensity_swap (a b : T3 → EuclideanSpace ℝ (Fin 3)) (x y : T3) :
    bsPairDensity a b (x, y) = bsPairDensity b a (y, x) := by
  unfold bsPairDensity
  simp only
  rw [kernel_symm x y, real_inner_smul_left, real_inner_smul_left, inner_cross_eq, neg_sub]

theorem inner_biotSavart_eq_integral {a : T3 → EuclideanSpace ℝ (Fin 3)} (ha : Continuous a)
    (hac : HasCompactSupport a) (b : T3 → EuclideanSpace ℝ (Fin 3)) (x : T3) :
    ⟪BiotSavart a x, b x⟫ = ∫ y, bsPairDensity a b (x, y) := by
  unfold bsPairDensity BiotSavart
  rw [show (NavierStokes3D.volume : Measure T3) = MeasureTheory.volume from rfl,
    real_inner_comm, ← integral_inner (integrable_biotSavart_density ha hac x)]
  simp only [real_inner_comm]

/-- **Biot–Savart self-adjointness** for continuous compactly supported fields:
`∫ ⟪B a, b⟫ = ∫ ⟪B b, a⟫`. -/
theorem biotSavart_selfAdjoint {a b : T3 → EuclideanSpace ℝ (Fin 3)} (ha : Continuous a)
    (hac : HasCompactSupport a) (hb : Continuous b) (hbc : HasCompactSupport b) :
    ∫ x, ⟪BiotSavart a x, b x⟫ = ∫ x, ⟪BiotSavart b x, a x⟫ := by
  simp_rw [inner_biotSavart_eq_integral ha hac b, inner_biotSavart_eq_integral hb hbc a]
  have hI := integrable_bsPairDensity ha hac hb hbc
  rw [integral_integral_swap (f := fun x y => bsPairDensity a b (x, y)) hI]
  simp_rw [bsPairDensity_swap a b]

theorem integrable_inner_biotSavart {a b : T3 → EuclideanSpace ℝ (Fin 3)} (ha : Continuous a)
    (hac : HasCompactSupport a) (hb : Continuous b) (hbc : HasCompactSupport b) :
    Integrable (fun x => ⟪BiotSavart a x, b x⟫) := by
  simp_rw [inner_biotSavart_eq_integral ha hac b]
  exact (integrable_bsPairDensity ha hac hb hbc).integral_prod_left

theorem IsTestOrbit.continuous {ω : CoadjointOrbit} (hω : IsTestOrbit ω) : Continuous ω.val := by
  have h : Continuous (fun y => WithLp.toLp 2 (fun k => ω.val y k) : T3 → EuclideanSpace ℝ (Fin 3)) :=
    (PiLp.continuous_toLp 2 _).comp (continuous_pi fun k => (hω.1 k).continuous)
  simpa using h

/-- **Helicity** `𝓗(ω) = ∫ ⟪B ω, ω⟫`. -/
noncomputable def helicity (ω : CoadjointOrbit) : ℝ :=
  ∫ x, pairing (BiotSavart ω.val x) (ω.val x)

/-- Helicity along an affine test line is the quadratic `P + 2 A t + Q t²`. -/
theorem helicity_line {ω ε : CoadjointOrbit} (hω : IsTestOrbit ω) (hε : IsTestOrbit ε) (t : ℝ)
    (hd : ∀ x, NavierStokes3D.div (fun y => ω.val y + t • ε.val y) x = 0) :
    helicity ⟨fun x => ω.val x + t • ε.val x, hd⟩ =
      helicity ω + t * (2 * ∫ x, ⟪BiotSavart ω.val x, ε.val x⟫) +
        t ^ 2 * ∫ x, ⟪BiotSavart ε.val x, ε.val x⟫ := by
  have cω := hω.continuous; have cε := hε.continuous
  have sω := hω.2; have sε := hε.2
  unfold helicity pairing
  simp only
  have hpt : ∀ x, ⟪BiotSavart (fun y => ω.val y + t • ε.val y) x, ω.val x + t • ε.val x⟫ =
      ⟪BiotSavart ω.val x, ω.val x⟫ + t * (⟪BiotSavart ω.val x, ε.val x⟫ +
        ⟪BiotSavart ε.val x, ω.val x⟫) + t ^ 2 * ⟪BiotSavart ε.val x, ε.val x⟫ := by
    intro x
    rw [BiotSavart_affine _ _ t (integrable_biotSavart_density cω sω x)
      (integrable_biotSavart_density cε sε x)]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    ring
  simp_rw [hpt]
  have i1 := integrable_inner_biotSavart cω sω cω sω
  have i2 := integrable_inner_biotSavart cω sω cε sε
  have i3 := integrable_inner_biotSavart cε sε cω sω
  have i4 := integrable_inner_biotSavart cε sε cε sε
  have i23 : Integrable (fun x => ⟪BiotSavart ω.val x, ε.val x⟫ + ⟪BiotSavart ε.val x, ω.val x⟫) :=
    i2.add i3
  have i23t : Integrable (fun x => t * (⟪BiotSavart ω.val x, ε.val x⟫ +
      ⟪BiotSavart ε.val x, ω.val x⟫)) := i23.const_mul t
  have i123 : Integrable (fun x => ⟪BiotSavart ω.val x, ω.val x⟫ + t * (⟪BiotSavart ω.val x, ε.val x⟫ +
      ⟪BiotSavart ε.val x, ω.val x⟫)) := i1.add i23t
  have i4t : Integrable (fun x => t ^ 2 * ⟪BiotSavart ε.val x, ε.val x⟫) := i4.const_mul _
  rw [integral_add i123 i4t, integral_add i1 i23t, integral_const_mul, integral_const_mul,
    integral_add i2 i3, biotSavart_selfAdjoint cε sε cω sω]
  ring

/-- **Gâteaux derivative of helicity**: `D𝓗(ω) = 2 u` with `u = B ω`, on the test class. -/
theorem helicity_gateaux (ω : CoadjointOrbit) (hω : IsTestOrbit ω) :
    IsGateauxRepOn helicity ω hω (fun x => (2 : ℝ) • BiotSavart ω.val x) := by
  intro ε hε
  have hfun : (fun t : ℝ => helicity ⟨fun x => ω.val x + t • ε.val x,
      fun x => orbit_add_smul_div_free ω ε t (hω.1.differentiable) (hε.1.differentiable) x⟩) =
      fun t => helicity ω + t * (2 * ∫ x, ⟪BiotSavart ω.val x, ε.val x⟫) +
        t ^ 2 * ∫ x, ⟪BiotSavart ε.val x, ε.val x⟫ :=
    funext fun t => helicity_line hω hε t _
  rw [hfun]
  have hval : (∫ x, pairing ((fun x => (2 : ℝ) • BiotSavart ω.val x) x) (ε.val x)
      ∂NavierStokes3D.volume) = 2 * ∫ x, ⟪BiotSavart ω.val x, ε.val x⟫ := by
    show (∫ x, pairing ((2 : ℝ) • BiotSavart ω.val x) (ε.val x) ∂MeasureTheory.volume) = _
    unfold pairing; simp_rw [real_inner_smul_left]; rw [integral_const_mul]
  rw [hval]
  have h1 : HasDerivAt (fun t : ℝ => t * (2 * ∫ x, ⟪BiotSavart ω.val x, ε.val x⟫))
      (2 * ∫ x, ⟪BiotSavart ω.val x, ε.val x⟫) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (2 * ∫ x, ⟪BiotSavart ω.val x, ε.val x⟫)
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * ∫ x, ⟪BiotSavart ε.val x, ε.val x⟫) 0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (∫ x, ⟪BiotSavart ε.val x, ε.val x⟫))
  simpa using ((hasDerivAt_const (0 : ℝ) (helicity ω)).add h1).add h2

theorem hasCompactSupport_fderiv_apply {g : T3 → ℝ} (hgc : HasCompactSupport g) (v : T3) :
    HasCompactSupport (fun x => fderiv ℝ g x v) :=
  (hgc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : T3 →L[ℝ] ℝ => L v) (by simp)

theorem continuous_fderiv_apply {g : T3 → ℝ} (hg : ContDiff ℝ 1 g) (v : T3) :
    Continuous (fun x => fderiv ℝ g x v) :=
  (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const

/-- Scalar integration by parts against a smooth compactly supported test function. -/
theorem integral_mul_fderiv_test {f g : T3 → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : T3) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x := by
  have c1 := hf.continuous.mul (continuous_fderiv_apply hg v)
  have c2 := (continuous_fderiv_apply hf v).mul hg.continuous
  have c3 := hf.continuous.mul hg.continuous
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (c2.integrable_of_hasCompactSupport hgc.mul_left)
    (c1.integrable_of_hasCompactSupport (hasCompactSupport_fderiv_apply hgc v).mul_left)
    (c3.integrable_of_hasCompactSupport hgc.mul_left)
    (fun x _ => (hf.differentiable one_ne_zero) x) (fun x _ => (hg.differentiable one_ne_zero) x)

theorem integral_ibp_two {d1 d2 χ : T3 → ℝ} (h1 : ContDiff ℝ 1 d1) (h2 : ContDiff ℝ 1 d2)
    (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) (b c : T3) :
    ∫ x, (d1 x * fderiv ℝ χ x b - d2 x * fderiv ℝ χ x c) =
      ∫ x, (fderiv ℝ d2 x c - fderiv ℝ d1 x b) * χ x := by
  have i1 : Integrable (fun x => d1 x * fderiv ℝ χ x b) :=
    (h1.continuous.mul (continuous_fderiv_apply hχ b)).integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply hχc b).mul_left
  have i2 : Integrable (fun x => d2 x * fderiv ℝ χ x c) :=
    (h2.continuous.mul (continuous_fderiv_apply hχ c)).integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply hχc c).mul_left
  have j1 : Integrable (fun x => fderiv ℝ d1 x b * χ x) :=
    ((continuous_fderiv_apply h1 b).mul hχ.continuous).integrable_of_hasCompactSupport hχc.mul_left
  have j2 : Integrable (fun x => fderiv ℝ d2 x c * χ x) :=
    ((continuous_fderiv_apply h2 c).mul hχ.continuous).integrable_of_hasCompactSupport hχc.mul_left
  simp_rw [sub_mul]
  rw [integral_sub i1 i2, integral_sub j2 j1, integral_mul_fderiv_test h1 hχ hχc,
    integral_mul_fderiv_test h2 hχ hχc]
  ring

theorem coord_smul_single (χ : T3 → ℝ) (k l : Fin 3) :
    (fun y => (χ y • (EuclideanSpace.single k (1:ℝ) : EuclideanSpace ℝ (Fin 3))) l) =
      if l = k then χ else fun _ => 0 := by
  funext y; by_cases h : l = k <;> simp [h]


theorem integral_pairing_curl_single_0 {d : T3 → EuclideanSpace ℝ (Fin 3)}
    (hd : ∀ c, ContDiff ℝ 1 (fun y => d y c)) {χ : T3 → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) :
    ∫ x, pairing (d x) (curl (fun y => χ y • (EuclideanSpace.single 0 (1:ℝ) :
      EuclideanSpace ℝ (Fin 3))) x) = ∫ x, curl d x 0 * χ x := by
  have hpt : ∀ x, pairing (d x) (curl (fun y => χ y • (EuclideanSpace.single 0 (1:ℝ) :
      EuclideanSpace ℝ (Fin 3))) x) =
      d x 1 * fderiv ℝ χ x (EuclideanSpace.single 2 1) -
        d x 2 * fderiv ℝ χ x (EuclideanSpace.single 1 1) := fun x => by
    obtain ⟨c0, c1, c2⟩ := curl_apply (fun y => χ y • (EuclideanSpace.single 0 (1:ℝ) :
      EuclideanSpace ℝ (Fin 3))) x
    simp only [directionalCoord, coord_smul_single] at c0 c1 c2
    simp at c0 c1 c2
    unfold pairing
    simp only [PiLp.inner_apply, Fin.sum_univ_three, c0, c1, c2]
    simp only [inner, conj_trivial, RCLike.re_to_real]
    ring
  simp_rw [hpt]
  rw [integral_ibp_two (hd 1) (hd 2) hχ hχc]
  congr 1; funext x
  rw [(curl_apply d x).1]
  rfl

theorem integral_pairing_curl_single_1 {d : T3 → EuclideanSpace ℝ (Fin 3)}
    (hd : ∀ c, ContDiff ℝ 1 (fun y => d y c)) {χ : T3 → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) :
    ∫ x, pairing (d x) (curl (fun y => χ y • (EuclideanSpace.single 1 (1:ℝ) :
      EuclideanSpace ℝ (Fin 3))) x) = ∫ x, curl d x 1 * χ x := by
  have hpt : ∀ x, pairing (d x) (curl (fun y => χ y • (EuclideanSpace.single 1 (1:ℝ) :
      EuclideanSpace ℝ (Fin 3))) x) =
      d x 2 * fderiv ℝ χ x (EuclideanSpace.single 0 1) -
        d x 0 * fderiv ℝ χ x (EuclideanSpace.single 2 1) := fun x => by
    obtain ⟨c0, c1, c2⟩ := curl_apply (fun y => χ y • (EuclideanSpace.single 1 (1:ℝ) :
      EuclideanSpace ℝ (Fin 3))) x
    simp only [directionalCoord, coord_smul_single] at c0 c1 c2
    simp at c0 c1 c2
    unfold pairing
    simp only [PiLp.inner_apply, Fin.sum_univ_three, c0, c1, c2]
    simp only [inner, conj_trivial, RCLike.re_to_real]
    ring
  simp_rw [hpt]
  rw [integral_ibp_two (hd 2) (hd 0) hχ hχc]
  congr 1; funext x
  rw [(curl_apply d x).2.1]
  rfl

theorem integral_pairing_curl_single_2 {d : T3 → EuclideanSpace ℝ (Fin 3)}
    (hd : ∀ c, ContDiff ℝ 1 (fun y => d y c)) {χ : T3 → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) :
    ∫ x, pairing (d x) (curl (fun y => χ y • (EuclideanSpace.single 2 (1:ℝ) :
      EuclideanSpace ℝ (Fin 3))) x) = ∫ x, curl d x 2 * χ x := by
  have hpt : ∀ x, pairing (d x) (curl (fun y => χ y • (EuclideanSpace.single 2 (1:ℝ) :
      EuclideanSpace ℝ (Fin 3))) x) =
      d x 0 * fderiv ℝ χ x (EuclideanSpace.single 1 1) -
        d x 1 * fderiv ℝ χ x (EuclideanSpace.single 0 1) := fun x => by
    obtain ⟨c0, c1, c2⟩ := curl_apply (fun y => χ y • (EuclideanSpace.single 2 (1:ℝ) :
      EuclideanSpace ℝ (Fin 3))) x
    simp only [directionalCoord, coord_smul_single] at c0 c1 c2
    simp at c0 c1 c2
    unfold pairing
    simp only [PiLp.inner_apply, Fin.sum_univ_three, c0, c1, c2]
    simp only [inner, conj_trivial, RCLike.re_to_real]
    ring
  simp_rw [hpt]
  rw [integral_ibp_two (hd 0) (hd 1) hχ hχc]
  congr 1; funext x
  rw [(curl_apply d x).2.2]
  rfl

/-- `∫ ⟪d, curl (χ e_k)⟫ = ∫ (curl d)_k χ` for `C¹` `d` and a `C¹` compactly supported `χ`. -/
theorem integral_pairing_curl_single {d : T3 → EuclideanSpace ℝ (Fin 3)}
    (hd : ∀ c, ContDiff ℝ 1 (fun y => d y c)) {χ : T3 → ℝ} (hχ : ContDiff ℝ 1 χ)
    (hχc : HasCompactSupport χ) (k : Fin 3) :
    ∫ x, pairing (d x) (curl (fun y => χ y • (EuclideanSpace.single k (1:ℝ) :
      EuclideanSpace ℝ (Fin 3))) x) = ∫ x, curl d x k * χ x := by
  fin_cases k
  · exact integral_pairing_curl_single_0 hd hχ hχc
  · exact integral_pairing_curl_single_1 hd hχ hχc
  · exact integral_pairing_curl_single_2 hd hχ hχc

theorem contDiff_directionalCoord {u : T3 → EuclideanSpace ℝ (Fin 3)}
    (hu : ∀ c, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => u y c)) (c j : Fin 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => directionalCoord u c j y) := by
  unfold directionalCoord
  exact ((hu c).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const

theorem contDiff_curl_coord {u : T3 → EuclideanSpace ℝ (Fin 3)}
    (hu : ∀ c, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => u y c)) (i : Fin 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => curl u y i) := by
  have d := contDiff_directionalCoord hu
  fin_cases i
  · simpa [(curl_apply u _).1] using (d 2 1).sub (d 1 2)
  · simpa [(curl_apply u _).2.1] using (d 0 2).sub (d 2 0)
  · simpa [(curl_apply u _).2.2] using (d 1 0).sub (d 0 1)

theorem hasCompactSupport_curl {u : T3 → EuclideanSpace ℝ (Fin 3)}
    (hc : ∀ c, HasCompactSupport (fun y => u y c)) : HasCompactSupport (curl u) := by
  have d : ∀ c j, HasCompactSupport (fun y => directionalCoord u c j y) := fun c j =>
    hasCompactSupport_fderiv_apply (hc c) _
  have s : ∀ (i : Fin 3) (f : T3 → ℝ), HasCompactSupport f →
      HasCompactSupport (fun y => (EuclideanSpace.single i (f y) : EuclideanSpace ℝ (Fin 3))) :=
    fun i f hf => hf.comp_left (g := fun r => (EuclideanSpace.single i r : EuclideanSpace ℝ (Fin 3)))
      (by simp)
  unfold curl
  exact ((s 0 _ ((d 2 1).sub (d 1 2))).add (s 1 _ ((d 0 2).sub (d 2 0)))).add
    (s 2 _ ((d 1 0).sub (d 0 1)))

/-- The curl of a smooth compactly supported field, as a divergence-free orbit element. -/
noncomputable def curlOrbit (u : T3 → EuclideanSpace ℝ (Fin 3))
    (hu : ∀ c, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => u y c)) : CoadjointOrbit :=
  ⟨curl u, fun x => div_curl u x (fun k => ((hu k).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)⟩

theorem isTestOrbit_curlOrbit (u : T3 → EuclideanSpace ℝ (Fin 3))
    (hu : ∀ c, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => u y c))
    (hc : ∀ c, HasCompactSupport (fun y => u y c)) : IsTestOrbit (curlOrbit u hu) :=
  ⟨fun i => contDiff_curl_coord hu i, hasCompactSupport_curl hc⟩

theorem continuous_curl_of_C1 {d : T3 → EuclideanSpace ℝ (Fin 3)}
    (hd : ∀ c, ContDiff ℝ 1 (fun y => d y c)) : Continuous (curl d) := by
  have h : ∀ c j, Continuous (fun y => directionalCoord d c j y) := fun c j =>
    continuous_fderiv_apply (hd c) _
  have s : ∀ (i : Fin 3) (f : T3 → ℝ), Continuous f →
      Continuous (fun y => (EuclideanSpace.single i (f y) : EuclideanSpace ℝ (Fin 3))) :=
    fun i f hf => by
      have he : (fun y => (EuclideanSpace.single i (f y) : EuclideanSpace ℝ (Fin 3))) =
          fun y => f y • (EuclideanSpace.single i (1 : ℝ) : EuclideanSpace ℝ (Fin 3)) := by
        funext y; ext j; by_cases h : j = i <;> simp [h]
      rw [he]; exact hf.smul continuous_const
  unfold curl
  exact ((s 0 _ ((h 2 1).sub (h 1 2))).add (s 1 _ ((h 0 2).sub (h 2 0)))).add
    (s 2 _ ((h 1 0).sub (h 0 1)))

/-- **Curl uniqueness of Gâteaux representatives** on the test class: any two `C¹` representatives
of the same functional have the same curl. -/
theorem curl_eq_of_isGateauxRepOn {F : CoadjointOrbit → ℝ} {ω : CoadjointOrbit} {hω : IsTestOrbit ω}
    {d₁ d₂ : T3 → EuclideanSpace ℝ (Fin 3)}
    (h₁ : ∀ c, ContDiff ℝ 1 (fun y => d₁ y c)) (h₂ : ∀ c, ContDiff ℝ 1 (fun y => d₂ y c))
    (r₁ : IsGateauxRepOn F ω hω d₁) (r₂ : IsGateauxRepOn F ω hω d₂) : curl d₁ = curl d₂ := by
  have key : ∀ k : Fin 3, (fun x => curl d₁ x k) = fun x => curl d₂ x k := by
    intro k
    have c₁ : Continuous (fun x => curl d₁ x k) :=
      (PiLp.continuous_apply 2 _ k).comp (continuous_curl_of_C1 h₁)
    have c₂ : Continuous (fun x => curl d₂ x k) :=
      (PiLp.continuous_apply 2 _ k).comp (continuous_curl_of_C1 h₂)
    refine (c₁.ae_eq_iff_eq (MeasureTheory.volume : Measure T3) c₂).1 ?_
    refine ae_eq_of_integral_contDiff_smul_eq c₁.locallyIntegrable c₂.locallyIntegrable ?_
    intro g hg hgc
    set ψ : T3 → EuclideanSpace ℝ (Fin 3) := fun y => g y • (EuclideanSpace.single k (1:ℝ) :
      EuclideanSpace ℝ (Fin 3)) with hψ
    have hψs : ∀ c, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => ψ y c) := fun c => by
      rw [hψ, coord_smul_single]; split_ifs
      · exact hg
      · exact contDiff_const
    have hψc : ∀ c, HasCompactSupport (fun y => ψ y c) := fun c => by
      rw [hψ, coord_smul_single]; split_ifs
      · exact hgc
      · exact HasCompactSupport.zero
    have hε := isTestOrbit_curlOrbit ψ hψs hψc
    have hu := (r₁ _ hε).unique (r₂ _ hε)
    have g1 : ContDiff ℝ 1 g := hg.of_le (by exact_mod_cast le_top)
    have e₁ := integral_pairing_curl_single h₁ g1 hgc k
    have e₂ := integral_pairing_curl_single h₂ g1 hgc k
    change (∫ x, pairing (d₁ x) (curl ψ x) ∂MeasureTheory.volume) =
      ∫ x, pairing (d₂ x) (curl ψ x) ∂MeasureTheory.volume at hu
    simp only [smul_eq_mul]
    simp_rw [mul_comm (g _)]
    rw [← e₁, ← e₂, hu]
  funext x; ext k
  exact congrFun (key k) x

theorem contDiff_biotSavart_coord {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (c : Fin 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => BiotSavart ω.val y c) := by
  have hn : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => newtonVec ω.val y k) := fun k => by
    rw [newtonVec_coord]
    refine contDiff_newtonPotential ?_ (hω.1 k)
    have := hω.2.comp_left (g := fun v : EuclideanSpace ℝ (Fin 3) => v k) (by simp)
    simpa [Function.comp_def] using this
  have := (contDiff_curl_coord hn c).const_smul (4 * Real.pi)⁻¹
  convert this using 1
  funext y
  rw [biotSavart_eq_curl_newtonVec hω y]
  simp

/-- Every `C¹` Gâteaux representative of helicity on the test class has curl `2 ω`. -/
theorem curl_eq_two_of_helicity_rep {ω : CoadjointOrbit} (hω : IsTestOrbit ω)
    {d : T3 → EuclideanSpace ℝ (Fin 3)} (hd : ∀ c, ContDiff ℝ 1 (fun y => d y c))
    (hr : IsGateauxRepOn helicity ω hω d) : ∀ x, curl d x = (2 : ℝ) • ω.val x := by
  have h2 : ∀ c, ContDiff ℝ 1 (fun y => ((2 : ℝ) • BiotSavart ω.val y) c) := fun c => by
    have := ((contDiff_biotSavart_coord hω c).const_smul (2 : ℝ)).of_le
      (by exact_mod_cast le_top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    simpa using this
  have hc := curl_eq_of_isGateauxRepOn hd h2 hr (helicity_gateaux ω hω)
  intro x
  rw [hc, curl_smul, ← velocity_from_vorticity_eq_BiotSavart, curlBiotSavartTest ω hω]

/-- **Helicity Casimir, closed with no hypothesis on the value of `D S`**: for any `D` whose value
on `S` is a `C¹` Gâteaux representative of helicity on the test class, `S` is a Casimir of the
concrete choice-free Arnold bracket. -/
theorem helicity_casimir_of_rep (ω : CoadjointOrbit) (hω : IsTestOrbit ω)
    (D : Functional → T3 → EuclideanSpace ℝ (Fin 3)) (S : Functional)
    (hC : ∀ c, ContDiff ℝ 1 (fun y => D S y c)) (hr : IsGateauxRepOn helicity ω hω (D S)) :
    EntropyCasimir (fun F G => ArnoldBracketOf ω (D F) (D G)) S :=
  entropyCasimir_arnold ω D S 2 (curl_eq_two_of_helicity_rep hω hC hr)

/-- The canonical derivative assignment: `2 u` on helicity-like `S`. With `D S = 2 B ω` the
Casimir holds unconditionally on the test class. -/
theorem helicity_casimir_canonical (ω : CoadjointOrbit) (hω : IsTestOrbit ω)
    (D : Functional → T3 → EuclideanSpace ℝ (Fin 3)) (S : Functional)
    (hD : D S = fun x => (2 : ℝ) • BiotSavart ω.val x) :
    EntropyCasimir (fun F G => ArnoldBracketOf ω (D F) (D G)) S := by
  refine helicity_casimir_of_rep ω hω D S (fun c => ?_) (hD ▸ helicity_gateaux ω hω)
  rw [hD]
  have := ((contDiff_biotSavart_coord hω c).const_smul (2 : ℝ)).of_le
    (by exact_mod_cast le_top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
  simpa using this

/-- Kinetic-energy representatives: any two `C¹` Gâteaux representatives of the kinetic energy
on the test class differ by a curl-free field (the curl half of Helmholtz uniqueness). -/
theorem kineticEnergy_reps_curl_eq {ω : CoadjointOrbit} {hω : IsTestOrbit ω}
    {d₁ d₂ : T3 → EuclideanSpace ℝ (Fin 3)}
    (h₁ : ∀ c, ContDiff ℝ 1 (fun y => d₁ y c)) (h₂ : ∀ c, ContDiff ℝ 1 (fun y => d₂ y c))
    (r₁ : IsGateauxRepOn KineticEnergyHamiltonian ω hω d₁)
    (r₂ : IsGateauxRepOn KineticEnergyHamiltonian ω hω d₂) : curl d₁ = curl d₂ :=
  curl_eq_of_isGateauxRepOn h₁ h₂ r₁ r₂


/-- Named `Prop` (open): the Poincaré lemma on `ℝ³` — a `C²` curl-free field is the gradient of
a `C²` potential. -/
def CurlFreeIsGradient : Prop :=
  ∀ v : T3 → EuclideanSpace ℝ (Fin 3), (∀ c, ContDiff ℝ 2 (fun y => v y c)) → curl v = 0 →
    ∃ φ : T3 → ℝ, ContDiff ℝ 2 φ ∧ v = grad φ

/-- `StreamFunctionRepModGradOn` reduces to existence of one `C²` stream-function representative
plus the Poincaré lemma; uniqueness modulo gradients is then proved via
`kineticEnergy_reps_curl_eq`. -/
theorem streamFunctionRepModGradOn_of_exists {ω : CoadjointOrbit} {hω : IsTestOrbit ω}
    (hP : CurlFreeIsGradient) (ψ : T3 → EuclideanSpace ℝ (Fin 3))
    (hψ : ∀ c, ContDiff ℝ 2 (fun y => ψ y c))
    (hrep : IsGateauxRepOn KineticEnergyHamiltonian ω hω ψ)
    (hcurl : curl ψ = velocity_from_vorticity ω) : StreamFunctionRepModGradOn ω hω := by
  refine ⟨ψ, hψ, hrep, hcurl, fun d hd hdr => ?_⟩
  have one : ∀ {f : T3 → ℝ}, ContDiff ℝ 2 f → ContDiff ℝ 1 f := fun h => h.of_le (by norm_num)
  have hc := kineticEnergy_reps_curl_eq (fun c => one (hd c)) (fun c => one (hψ c)) hdr hrep
  set v : T3 → EuclideanSpace ℝ (Fin 3) := fun y => d y - ψ y with hv
  have hvs : ∀ c, ContDiff ℝ 2 (fun y => v y c) := fun c => by
    simpa [hv] using (hd c).sub (hψ c)
  have hv0 : curl v = 0 := by
    funext x
    have hsub : curl v x = curl d x - curl ψ x := by
      ext i
      have dd : ∀ (u : T3 → EuclideanSpace ℝ (Fin 3)) (hu : ∀ c, ContDiff ℝ 2 (fun y => u y c))
          (c j : Fin 3), DifferentiableAt ℝ (fun y => u y c) x := fun u hu c j =>
        ((hu c).differentiable (by norm_num)) x
      have dc : ∀ c j, directionalCoord v c j x = directionalCoord d c j x -
          directionalCoord ψ c j x := fun c j => by
        unfold directionalCoord
        have : (fun y => v y c) = fun y => d y c - ψ y c := by funext y; simp [hv]
        rw [this, fderiv_fun_sub (dd d hd c j) (dd ψ hψ c j)]
        rfl
      fin_cases i
      · simp only [Fin.zero_eta, Fin.isValue, PiLp.sub_apply, (curl_apply v x).1,
          (curl_apply d x).1, (curl_apply ψ x).1, dc]; ring
      · simp only [Fin.mk_one, Fin.isValue, PiLp.sub_apply, (curl_apply v x).2.1,
          (curl_apply d x).2.1, (curl_apply ψ x).2.1, dc]; ring
      · simp only [Fin.reduceFinMk, Fin.isValue, PiLp.sub_apply, (curl_apply v x).2.2,
          (curl_apply d x).2.2, (curl_apply ψ x).2.2, dc]; ring
    rw [hsub, hc, sub_self]; rfl
  obtain ⟨φ, hφ, hvφ⟩ := hP v hvs hv0
  refine ⟨φ, hφ, funext fun y => ?_⟩
  have := congrFun hvφ y
  simp only [hv] at this
  rw [← this]; abel

end MetriplecticWorldModel
