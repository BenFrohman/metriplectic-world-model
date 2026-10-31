/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.NewtonLaplacian

/-!
# Newton-potential steps 4–5: `curl (BiotSavart ω) = ω` on the test class
-/

open NavierStokes3D ArnoldGeometric FrohmanianTether MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace

namespace MetriplecticWorldModel

local notation "e" i => (EuclideanSpace.single i (1 : ℝ) : T3)

/-- Regularized gradient-kernel coordinate `t_j (‖t‖²+ε²)^(-3/2)`; `ε = 0` gives `t_j/|t|³`. -/
noncomputable def gradKer (ε : ℝ) (j : Fin 3) (t : T3) : ℝ :=
  t j * (‖t‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ))

theorem gradKer_bound (ε : ℝ) (j : Fin 3) {t : T3} (ht : t ≠ 0) :
    |gradKer ε j t| ≤ ‖t‖ ^ (-(2 : ℝ)) := by
  unfold gradKer
  have hn : 0 < ‖t‖ := norm_pos_iff.mpr ht
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (‖t‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)))]
  have h1 : |t j| ≤ ‖t‖ := by simpa using PiLp.norm_apply_le t j
  have h2 : (‖t‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) ≤ (‖t‖ ^ 2) ^ (-(3 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [sq_nonneg ε]) (by norm_num)
  have h3 : (‖t‖ ^ 2) ^ (-(3 / 2 : ℝ)) = ‖t‖ ^ (-(3 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]; norm_num
  have h4 : ‖t‖ * ‖t‖ ^ (-(3 : ℝ)) = ‖t‖ ^ (-(2 : ℝ)) := by
    rw [show (-(2:ℝ)) = 1 + -3 by norm_num, Real.rpow_add hn, Real.rpow_one]
  calc |t j| * (‖t‖ ^ 2 + ε ^ 2) ^ (-(3 / 2 : ℝ)) ≤ ‖t‖ * (‖t‖ ^ 2) ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul h1 h2 (by positivity) (norm_nonneg _)
    _ = _ := by rw [h3, h4]

theorem locallyIntegrable_norm_rpow_neg_two :
    LocallyIntegrable (fun t : T3 => ‖t‖ ^ (-(2 : ℝ))) (MeasureTheory.volume : Measure T3) := by
  intro x
  exact ⟨ball (0 : T3) (‖x‖ + 1), isOpen_ball.mem_nhds (by simp),
    integrableOn_ball_norm_rpow_neg (s := 2) (by norm_num) (‖x‖ + 1)⟩

theorem integrable_rpow_neg_two_mul {h : T3 → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (x : T3) :
    Integrable (fun t => ‖t‖ ^ (-(2 : ℝ)) * h (x - t)) (MeasureTheory.volume : Measure T3) := by
  have := hc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ)
    locallyIntegrable_norm_rpow_neg_two hh x
  simpa [ConvolutionExistsAt] using this

theorem tendsto_gradKer_conv {h : T3 → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (j : Fin 3) (x : T3) :
    Tendsto (fun ε => ∫ t, gradKer ε j t * h (x - t)) (𝓝 0)
      (𝓝 (∫ t, gradKer 0 j t * h (x - t))) := by
  refine tendsto_integral_filter_of_dominated_convergence (fun t => ‖t‖ ^ (-(2 : ℝ)) * |h (x - t)|)
    (Eventually.of_forall (fun ε => ?_)) (Eventually.of_forall (fun ε => ?_))
    (integrable_rpow_neg_two_mul hh.abs hc.abs x) ?_
  · have hm : Measurable (gradKer ε j) := by unfold gradKer; fun_prop
    exact (hm.aestronglyMeasurable.mul
      (hh.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  · filter_upwards [ae_ne_zero_T3] with t ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (gradKer_bound ε j ht) (abs_nonneg _)
  · filter_upwards [ae_ne_zero_T3] with t ht
    refine Tendsto.mul_const _ (Tendsto.const_mul _ ?_)
    have hc' : Continuous fun ε : ℝ => ‖t‖ ^ 2 + ε ^ 2 := by continuity
    have := (hc'.tendsto 0).rpow_const (p := -(3 / 2 : ℝ)) (Or.inl (by simp [ht]))
    simpa using this

/-- Regularized identity: `∫ N_ε(t) (∂ⱼh)(x−t) dt = −∫ gradKer ε j t · h(x−t) dt`. -/
theorem regNewton_conv_deriv {ε : ℝ} (hε : ε ≠ 0) {h : T3 → ℝ} (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) (j : Fin 3) (x : T3) :
    ∫ t, regNewton ε t * fderiv ℝ h (x - t) (e j) = -∫ t, gradKer ε j t * h (x - t) := by
  set H : T3 → ℝ := fun t => h (x - t) with hH
  have hHd : ∀ t, HasFDerivAt H (-(fderiv ℝ h (x - t))) t := by
    intro t
    have h1 : HasFDerivAt (fun t : T3 => x - t) (-(ContinuousLinearMap.id ℝ T3)) t :=
      (hasFDerivAt_id t).const_sub x
    have := ((hh.differentiable one_ne_zero) (x - t)).hasFDerivAt.comp t h1
    simpa using this
  have hHc : HasCompactSupport H := by
    have := hc.comp_homeomorph (Homeomorph.subLeft x)
    simpa [Function.comp_def, hH] using this
  have hN := contDiff_regNewton hε
  have cN : Continuous (regNewton ε) := hN.continuous
  have cN1 : Continuous (fun t => fderiv ℝ (regNewton ε) t (e j)) :=
    (hN.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have cH : Continuous H := hh.continuous.comp (continuous_const.sub continuous_id)
  have cH1 : Continuous (fun t => fderiv ℝ H t (e j)) := by
    have : (fun t => fderiv ℝ H t (e j)) = fun t => -(fderiv ℝ h (x - t) (e j)) := by
      funext t; rw [(hHd t).fderiv]; rfl
    rw [this]
    exact (((hh.continuous_fderiv one_ne_zero).comp
      (continuous_const.sub continuous_id)).clm_apply continuous_const).neg
  have sH1 : HasCompactSupport (fun t => fderiv ℝ H t (e j)) := hHc.fderiv_apply (𝕜 := ℝ) _
  have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := (MeasureTheory.volume : Measure T3)) (f := regNewton ε) (g := H) (v := e j)
    ((cN1.mul cH).integrable_of_hasCompactSupport hHc.mul_left)
    ((cN.mul cH1).integrable_of_hasCompactSupport sH1.mul_left)
    ((cN.mul cH).integrable_of_hasCompactSupport hHc.mul_left)
    (fun t _ => hN.differentiable (by norm_num) t) (fun t _ => (hHd t).differentiableAt)
  have lhs : (fun t => regNewton ε t * fderiv ℝ h (x - t) (e j)) =
      fun t => -(regNewton ε t * fderiv ℝ H t (e j)) := by
    funext t; rw [(hHd t).fderiv]; simp
  have rhs : (fun t => fderiv ℝ (regNewton ε) t (e j) * H t) =
      fun t => -(gradKer ε j t * h (x - t)) := by
    funext t
    unfold regNewton gradKer
    rw [regSq_rpow_partial _ hε]
    norm_num [hH]
    exact Or.inl (mul_comm _ _)
  rw [lhs, integral_neg, ibp, rhs, integral_neg, neg_neg]


/-- **Step 5 kernel identity:** `N ⋆ ∂ⱼh = −∫ (tⱼ/|t|³) h(x−t) dt` for `h ∈ C¹_c`. -/
theorem newtonPotential_deriv_eq {h : T3 → ℝ} (hh : ContDiff ℝ 1 h) (hc : HasCompactSupport h)
    (j : Fin 3) (x : T3) :
    newtonPotential (fun z => fderiv ℝ h z (e j)) x = -∫ t, gradKer 0 j t * h (x - t) := by
  have c1 : Continuous (fun z => fderiv ℝ h z (e j)) :=
    (hh.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hA := (tendsto_regNewton_conv c1 (hc.fderiv_apply (𝕜 := ℝ) _) x).mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  have hB := ((tendsto_gradKer_conv hh.continuous hc j x).neg).mono_left
    (nhdsWithin_le_nhds (s := {0}ᶜ))
  rw [newtonPotential_apply]
  refine tendsto_nhds_unique hA (hB.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (regNewton_conv_deriv hε hh hc j x).symm

/-- Componentwise Newton potential of a vector field. -/
noncomputable def newtonVec (ω : T3 → EuclideanSpace ℝ (Fin 3)) : T3 → EuclideanSpace ℝ (Fin 3) :=
  fun y => WithLp.toLp 2 (fun k => newtonPotential (fun z => ω z k) y)

theorem newtonVec_coord (ω : T3 → EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    (fun y => newtonVec ω y k) = newtonPotential (fun z => ω z k) := by
  funext y; simp [newtonVec]

theorem directionalCoord_newtonVec {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (k j : Fin 3)
    (x : T3) :
    directionalCoord (newtonVec ω.val) k j x =
      -∫ t, gradKer 0 j t * ω.val (x - t) k := by
  have hk : ContDiff ℝ 1 (fun z => ω.val z k) := (hω.1 k).of_le (by simp)
  have hck : HasCompactSupport (fun z => ω.val z k) := by
    have := hω.2.comp_left (g := fun v : EuclideanSpace ℝ (Fin 3) => v k) (by simp)
    simpa [Function.comp_def] using this
  unfold directionalCoord
  rw [newtonVec_coord, congrFun (fderiv_newtonPotential_apply hck hk (e j)) x,
    newtonPotential_deriv_eq hk hck]


theorem integrable_gradKer_mul {h : T3 → ℝ} (hh : Continuous h) (hc : HasCompactSupport h)
    (j : Fin 3) (x : T3) :
    Integrable (fun t => gradKer 0 j t * h (x - t)) (MeasureTheory.volume : Measure T3) := by
  refine (integrable_rpow_neg_two_mul hh.abs hc.abs x).mono' ?_ ?_
  · have hm : Measurable (gradKer 0 j) := by unfold gradKer; fun_prop
    exact hm.aestronglyMeasurable.mul
      (hh.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards [ae_ne_zero_T3] with t ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (gradKer_bound 0 j ht) (abs_nonneg _)

theorem gradKer_zero_eq (j : Fin 3) (t : T3) : gradKer 0 j t = t j * ‖t‖ ^ (-(3 : ℝ)) := by
  unfold gradKer
  rw [zero_pow two_ne_zero, add_zero, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  norm_num

/-- **Step 5:** on the test class, the repo's `BiotSavart` is `(4π)⁻¹ curl (N ⋆ ω)`. -/
theorem biotSavart_eq_curl_newtonVec {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (x : T3) :
    BiotSavart ω.val x = (4 * Real.pi)⁻¹ • curl (newtonVec ω.val) x := by
  set w : Fin 3 → T3 → ℝ := fun k z => ω.val z k with hw
  have cw : ∀ k, Continuous (w k) := fun k => (hω.1 k).continuous
  have sw : ∀ k, HasCompactSupport (w k) := fun k => by
    have := hω.2.comp_left (g := fun v : EuclideanSpace ℝ (Fin 3) => v k) (by simp)
    simpa [Function.comp_def] using this
  set A : Fin 3 → Fin 3 → T3 → ℝ := fun j k t => gradKer 0 j t * w k (x - t) with hA
  have IA : ∀ j k, Integrable (A j k) (MeasureTheory.volume : Measure T3) := fun j k =>
    integrable_gradKer_mul (cw k) (sw k) j x
  have h1 : BiotSavart ω.val x =
      ∫ t, biotSavartKernel x (x - t) • cross (ω.val (x - t)) t := by
    unfold BiotSavart NavierStokes3D.volume
    rw [← integral_sub_left_eq_self
      (fun y => biotSavartKernel x y • cross (ω.val y) (x - y))
      (μ := (MeasureTheory.volume : Measure T3)) x]
    simp only [sub_sub_cancel]
  have h2 : (fun t => biotSavartKernel x (x - t) • cross (ω.val (x - t)) t) =
      fun t => (4 * Real.pi)⁻¹ • ((A 2 1 t - A 1 2 t) • (e 0) + (A 0 2 t - A 2 0 t) • (e 1) +
        (A 1 0 t - A 0 1 t) • (e 2)) := by
    funext t
    obtain ⟨c0, c1, c2⟩ := cross_coord (ω.val (x - t)) t
    by_cases ht : t = 0
    · subst ht
      ext i; fin_cases i <;> simp [hA, gradKer]
    · have hne : x ≠ x - t := by intro h; apply ht; have := congrArg (x - ·) h; simp at this; exact this.symm
      rw [biotSavartKernel_of_ne hne, sub_sub_cancel]
      ext i; fin_cases i <;>
        simp [hA, hw, gradKer_zero_eq, c0, c1, c2, smul_eq_mul] <;> ring
  rw [h1, h2, integral_smul]
  have IE : ∀ (a : T3 → ℝ), Integrable a (MeasureTheory.volume : Measure T3) → ∀ i : Fin 3,
      Integrable (fun t => a t • (e i)) (MeasureTheory.volume : Measure T3) :=
    fun a ha i => ha.smul_const _
  have I0 := IE _ ((IA 2 1).sub (IA 1 2)) 0
  have I1 := IE _ ((IA 0 2).sub (IA 2 0)) 1
  have I2 := IE _ ((IA 1 0).sub (IA 0 1)) 2
  simp only [Pi.sub_apply] at I0 I1 I2
  rw [show (∫ t, (A 2 1 t - A 1 2 t) • (e 0) + (A 0 2 t - A 2 0 t) • (e 1) +
      (A 1 0 t - A 0 1 t) • (e 2)) = (∫ t, (A 2 1 t - A 1 2 t) • (e 0) + (A 0 2 t - A 2 0 t) • (e 1)) +
      ∫ t, (A 1 0 t - A 0 1 t) • (e 2) from integral_add (I0.add I1) I2]
  rw [integral_add I0 I1,
    integral_smul_const, integral_smul_const, integral_smul_const,
    integral_sub (IA 2 1) (IA 1 2), integral_sub (IA 0 2) (IA 2 0), integral_sub (IA 1 0) (IA 0 1)]
  congr 1
  ext i; fin_cases i <;> simp [curl, directionalCoord_newtonVec hω, hA, hw] <;> ring


/-- Symmetry of mixed second partials for `C²` scalar fields. -/
theorem fderiv_fderiv_swap {f : T3 → ℝ} (hf : ContDiff ℝ 2 f) (x : T3) (a b : Fin 3) :
    fderiv ℝ (fun y => fderiv ℝ f y (e b)) x (e a) =
      fderiv ℝ (fun y => fderiv ℝ f y (e a)) x (e b) := by
  have hs := hf.contDiffAt.isSymmSndFDerivAt (x := x) (by simp)
  have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) x
  rw [fderiv_clm_apply hd (differentiableAt_const _), fderiv_clm_apply hd (differentiableAt_const _)]
  simpa using hs (e a) (e b)

/-- **Step 4 (curl curl):** on the test class, `curl curl (N ⋆ ω) = 4π ω`. -/
theorem curl_curl_newtonVec {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (x : T3) :
    curl (curl (newtonVec ω.val)) x = (4 * Real.pi) • ω.val x := by
  set w : Fin 3 → T3 → ℝ := fun k z => ω.val z k with hw
  have sw : ∀ k, HasCompactSupport (w k) := fun k => by
    have := hω.2.comp_left (g := fun v : EuclideanSpace ℝ (Fin 3) => v k) (by simp)
    simpa [Function.comp_def] using this
  have smw : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (w k) := fun k => (hω.1 k).of_le le_top
  set ψ : Fin 3 → T3 → ℝ := fun k => newtonPotential (w k) with hψ
  have smψ : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ψ k) := fun k =>
    contDiff_newtonPotential (sw k) (smw k)
  set G : Fin 3 → Fin 3 → T3 → ℝ := fun k j y => fderiv ℝ (ψ k) y (e j) with hG
  have dG : ∀ k j, Differentiable ℝ (G k j) := fun k j =>
    (((smψ k).fderiv_right (m := 1) (WithTop.coe_le_coe.mpr le_top)).clm_apply
      contDiff_const).differentiable one_ne_zero
  have hc : ∀ (a b c d : Fin 3),
      (fun y => directionalCoord (newtonVec ω.val) a b y -
        directionalCoord (newtonVec ω.val) c d y) = fun y => G a b y - G c d y := by
    intro a b c d; funext y; simp only [directionalCoord, newtonVec_coord, hG, hψ, hw]
  have dsub : ∀ (a b c d i : Fin 3), fderiv ℝ (fun y => G a b y - G c d y) x (e i) =
      fderiv ℝ (G a b) x (e i) - fderiv ℝ (G c d) x (e i) := by
    intro a b c d i
    rw [fderiv_fun_sub (dG a b x) (dG c d x)]; rfl
  have c0 : (fun y => curl (newtonVec ω.val) y 0) = fun y => G 2 1 y - G 1 2 y := by
    rw [← hc]; funext y; exact (curl_apply _ y).1
  have c1 : (fun y => curl (newtonVec ω.val) y 1) = fun y => G 0 2 y - G 2 0 y := by
    rw [← hc]; funext y; exact (curl_apply _ y).2.1
  have c2 : (fun y => curl (newtonVec ω.val) y 2) = fun y => G 1 0 y - G 0 1 y := by
    rw [← hc]; funext y; exact (curl_apply _ y).2.2
  -- symmetry
  have sym : ∀ k a b, fderiv ℝ (G k b) x (e a) = fderiv ℝ (G k a) x (e b) := fun k a b =>
    fderiv_fderiv_swap ((smψ k).of_le (WithTop.coe_le_coe.mpr le_top)) x a b
  -- Laplacian
  have lap : ∀ k, fderiv ℝ (G k 0) x (e 0) + fderiv ℝ (G k 1) x (e 1) + fderiv ℝ (G k 2) x (e 2)
      = -(4 * Real.pi) * w k x := by
    intro k
    have := scalarLaplacian_newtonPotential_eq ((smw k).of_le (WithTop.coe_le_coe.mpr le_top)) (sw k) x
    simpa [scalarLaplacian, Fin.sum_univ_three, hG, hψ] using this
  -- divergence of ψ vanishes identically
  have divψ : (fun y => G 0 0 y + G 1 1 y + G 2 2 y) = fun _ => 0 := by
    funext y
    have h1 : ∀ k, ContDiff ℝ 1 (w k) := fun k => (smw k).of_le (WithTop.coe_le_coe.mpr le_top)
    have hcd : ∀ k j, Continuous (fun z => fderiv ℝ (w k) z (e j)) := fun k j =>
      ((h1 k).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have I : ∀ k, Integrable (fun t => newtonRadial t * fderiv ℝ (w k) (y - t) (e k))
        (MeasureTheory.volume : Measure T3) := fun k =>
      integrable_newtonRadial_mul (hcd k k) ((sw k).fderiv_apply (𝕜 := ℝ) _) y
    simp only [hG, hψ]
    rw [congrFun (fderiv_newtonPotential_apply (sw 0) (h1 0) (e 0)) y,
      congrFun (fderiv_newtonPotential_apply (sw 1) (h1 1) (e 1)) y,
      congrFun (fderiv_newtonPotential_apply (sw 2) (h1 2) (e 2)) y,
      newtonPotential_apply, newtonPotential_apply, newtonPotential_apply,
      ← integral_add (I 0) (I 1)]
    have I01 : Integrable (fun t => newtonRadial t * fderiv ℝ (w 0) (y - t) (e 0) +
        newtonRadial t * fderiv ℝ (w 1) (y - t) (e 1)) (MeasureTheory.volume : Measure T3) :=
      (I 0).add (I 1)
    rw [← integral_add I01 (I 2)]
    have hz : ∀ t, newtonRadial t * fderiv ℝ (w 0) (y - t) (e 0) +
        newtonRadial t * fderiv ℝ (w 1) (y - t) (e 1) +
        newtonRadial t * fderiv ℝ (w 2) (y - t) (e 2) = 0 := by
      intro t
      have := ω.property (y - t)
      simp only [div, Fin.sum_univ_three] at this
      rw [← mul_add, ← mul_add]
      simp only [hw]; rw [this, mul_zero]
    simp only [hz, integral_zero]
  have dv : ∀ i, fderiv ℝ (G 0 0) x (e i) + fderiv ℝ (G 1 1) x (e i) +
      fderiv ℝ (G 2 2) x (e i) = 0 := by
    intro i
    have := congrArg (fun F => fderiv ℝ F x (e i)) divψ
    simp only at this
    have d01 : DifferentiableAt ℝ (fun y => G 0 0 y + G 1 1 y) x := (dG 0 0 x).add (dG 1 1 x)
    rw [fderiv_fun_add d01 (dG 2 2 x),
      fderiv_fun_add (dG 0 0 x) (dG 1 1 x)] at this
    simpa using this
  obtain ⟨k0, k1, k2⟩ := curl_apply (curl (newtonVec ω.val)) x
  have s := sym; have l0 := lap 0; have l1 := lap 1; have l2 := lap 2
  have d0 := dv 0; have d1 := dv 1; have d2 := dv 2
  simp only [directionalCoord, c0, c1, c2, dsub] at k0 k1 k2
  have s101 := sym 1 0 1; have s202 := sym 2 0 2; have s010 := sym 0 1 0
  have s212 := sym 2 1 2; have s020 := sym 0 2 0; have s121 := sym 1 2 1
  ext i; fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
    rw [k0]; simp only [hw] at l0; linarith
  · simp only [Fin.mk_one, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
    rw [k1]; simp only [hw] at l1; linarith
  · simp only [Fin.reduceFinMk, Fin.isValue, PiLp.smul_apply, smul_eq_mul]
    rw [k2]; simp only [hw] at l2; linarith

/-- **`CurlBiotSavartTest` (proved):** on smooth compactly supported divergence-free
vorticity, `curl (BiotSavart ω) = ω`. -/
theorem curlBiotSavartTest : CurlBiotSavartTest := by
  intro ω hω
  funext x
  have hv : velocity_from_vorticity ω =
      fun y => (4 * Real.pi)⁻¹ • curl (newtonVec ω.val) y :=
    funext fun y => biotSavart_eq_curl_newtonVec hω y
  rw [hv, curl_smul, curl_curl_newtonVec hω x, smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]


/-- `helicity_casimir_test` with `CurlBiotSavartTest` discharged. The choice `D S = u` is still
an explicit argument (that it is the true Gâteaux derivative of helicity is not proved here). -/
theorem helicity_casimir_test_closed (ω : CoadjointOrbit) (hω : IsTestOrbit ω)
    (D : Functional → T3 → EuclideanSpace ℝ (Fin 3)) (S : Functional)
    (hD : D S = velocity_from_vorticity ω) :
    EntropyCasimir (fun F G => ArnoldBracketOf ω (D F) (D G)) S :=
  helicity_casimir_test curlBiotSavartTest ω hω D S hD

end MetriplecticWorldModel
