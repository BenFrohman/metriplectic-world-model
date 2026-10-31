/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.PoincareR3
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# The kinetic-energy Gâteaux representative `ψ = (4π)⁻¹ N ⋆ ω` and `StreamFunctionRepModGradOn`

Decay: for continuous compactly supported `g` with `∫ g = 0`, `|N ⋆ g (x)| ≲ (1 + |x|)⁻²`
(`decays_newtonPotential`). Mean-zero inputs: derivatives of test functions, and the
coordinates of a divergence-free test field. With this, all integrations by parts over `ℝ³`
needed for `∫ ⟪B ω, B ε⟫ = ∫ ⟪ψ, ε⟫` are justified.
-/

open NavierStokes3D ArnoldGeometric FrohmanianTether MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace

set_option linter.unusedSimpArgs false

namespace MetriplecticWorldModel

/-- Quadratic decay: continuous and `|f x| ≤ C (1 + ‖x‖)⁻²`. -/
def Decays (f : T3 → ℝ) : Prop :=
  Continuous f ∧ ∃ C, ∀ x, |f x| ≤ C * ((1 + ‖x‖) ^ 2)⁻¹

theorem Decays.sub {f g : T3 → ℝ} (hf : Decays f) (hg : Decays g) : Decays (fun x => f x - g x) := by
  obtain ⟨cf, C, hC⟩ := hf; obtain ⟨cg, D, hD⟩ := hg
  refine ⟨cf.sub cg, C + D, fun x => ?_⟩
  calc |f x - g x| ≤ |f x| + |g x| := abs_sub _ _
    _ ≤ _ := by rw [add_mul]; exact add_le_add (hC x) (hD x)

theorem Decays.const_mul {f : T3 → ℝ} (hf : Decays f) (c : ℝ) : Decays (fun x => c * f x) := by
  obtain ⟨cf, C, hC⟩ := hf
  refine ⟨continuous_const.mul cf, |c| * C, fun x => ?_⟩
  rw [abs_mul, mul_assoc]; exact mul_le_mul_of_nonneg_left (hC x) (abs_nonneg _)

theorem Decays.integrable_mul {f g : T3 → ℝ} (hf : Decays f) (hg : Decays g) :
    Integrable (fun x => f x * g x) (MeasureTheory.volume : Measure T3) := by
  obtain ⟨cf, C, hC⟩ := hf; obtain ⟨cg, D, hD⟩ := hg
  have hI : Integrable (fun x : T3 => (C * D) * (1 + ‖x‖) ^ (-(4 : ℝ)))
      (MeasureTheory.volume : Measure T3) :=
    (integrable_one_add_norm (by simp; norm_num)).const_mul _
  refine hI.mono' (cf.mul cg).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hp : 0 < 1 + ‖x‖ := by positivity
  have e4 : (1 + ‖x‖) ^ (-(4 : ℝ)) = ((1 + ‖x‖) ^ 2)⁻¹ * ((1 + ‖x‖) ^ 2)⁻¹ := by
    rw [Real.rpow_neg hp.le, ← mul_inv, ← pow_add]; norm_cast
  rw [Real.norm_eq_abs, abs_mul, e4]
  have h0 : 0 ≤ |f x| := abs_nonneg _
  have h1 : 0 ≤ |g x| := abs_nonneg _
  calc |f x| * |g x| ≤ (C * ((1 + ‖x‖) ^ 2)⁻¹) * (D * ((1 + ‖x‖) ^ 2)⁻¹) :=
        mul_le_mul (hC x) (hD x) h1 (h0.trans (hC x))
    _ = _ := by ring

theorem abs_inv_norm_sub_le {x y : T3} {R : ℝ} (hy : ‖y‖ ≤ R) (hx : 2 * R ≤ ‖x‖) (hR : 0 < R) :
    |‖x - y‖⁻¹ - ‖x‖⁻¹| ≤ 2 * R * (‖x‖ ^ 2)⁻¹ := by
  have hx0 : 0 < ‖x‖ := by linarith
  have hxy : ‖x‖ / 2 ≤ ‖x - y‖ := by
    have := norm_sub_norm_le x y; linarith [norm_sub_rev x y]
  have hxy0 : 0 < ‖x - y‖ := by linarith
  rw [inv_sub_inv hxy0.ne' hx0.ne', abs_div, abs_of_pos (mul_pos hxy0 hx0)]
  have hn : |‖x‖ - ‖x - y‖| ≤ ‖y‖ := by
    have := abs_norm_sub_norm_le x (x - y); simpa using this
  rw [div_le_iff₀ (mul_pos hxy0 hx0)]
  calc |‖x‖ - ‖x - y‖| ≤ R := hn.trans hy
    _ = 2 * R * (‖x‖ ^ 2)⁻¹ * ((‖x‖ / 2) * ‖x‖) := by field_simp
    _ ≤ 2 * R * (‖x‖ ^ 2)⁻¹ * (‖x - y‖ * ‖x‖) := by
        gcongr

theorem newtonRadial_eq_inv (y : T3) : newtonRadial y = ‖y‖⁻¹ := by
  rw [newtonRadial_eq, Real.rpow_neg_one]

theorem continuous_newtonPotential {g : T3 → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) :
    Continuous (newtonPotential g) :=
  hc.continuous_convolution_right _ locallyIntegrable_newtonRadial hg

theorem newtonPotential_eq_swap (g : T3 → ℝ) (x : T3) :
    newtonPotential g x = ∫ y, newtonRadial (x - y) * g y := by
  rw [newtonPotential_apply]
  have := MeasureTheory.integral_sub_left_eq_self (fun t => newtonRadial t * g (x - t))
    (MeasureTheory.volume : Measure T3) x
  rw [← this]; simp

/-- **Decay of mean-zero Newton potentials.** -/
theorem decays_newtonPotential {g : T3 → ℝ} (hg : Continuous g) (hc : HasCompactSupport g)
    (h0 : ∫ y, g y = 0) : Decays (newtonPotential g) := by
  refine ⟨continuous_newtonPotential hg hc, ?_⟩
  obtain ⟨R0, hR0⟩ := hc.isCompact.isBounded.subset_closedBall 0
  set R := max R0 1 with hRdef
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR : 0 < R := by linarith
  have hsupp : ∀ y, R < ‖y‖ → g y = 0 := fun y hy => by
    by_contra hne
    have := hR0 (subset_tsupport _ hne)
    simp at this; linarith [le_max_left R0 1]
  have hgi : Integrable g (MeasureTheory.volume : Measure T3) := hg.integrable_of_hasCompactSupport hc
  set A := ∫ y, |g y|
  -- far bound
  have far : ∀ x : T3, 2 * R ≤ ‖x‖ → |newtonPotential g x| ≤ (8 * R * A) * ((1 + ‖x‖) ^ 2)⁻¹ := by
    intro x hx
    have hx0 : 0 < ‖x‖ := by linarith
    have hI1 : Integrable (fun y => newtonRadial (x - y) * g y) (MeasureTheory.volume : Measure T3) := by
      have := MeasureTheory.Integrable.comp_sub_left (integrable_newtonRadial_mul hg hc x) x
      simpa using this
    have key : newtonPotential g x = ∫ y, (newtonRadial (x - y) - newtonRadial x) * g y := by
      rw [newtonPotential_eq_swap]
      simp_rw [sub_mul]
      rw [integral_sub hI1 (hgi.const_mul _), integral_const_mul, h0, mul_zero, sub_zero]
    rw [key]
    have hb : ∀ y, |(newtonRadial (x - y) - newtonRadial x) * g y| ≤ 2 * R * (‖x‖ ^ 2)⁻¹ * |g y| := by
      intro y
      rw [abs_mul]
      by_cases hy : ‖y‖ ≤ R
      · gcongr
        simp only [newtonRadial_eq_inv]; exact abs_inv_norm_sub_le hy hx hR
      · rw [hsupp y (lt_of_not_ge hy)]; simp
    calc |∫ y, (newtonRadial (x - y) - newtonRadial x) * g y|
        ≤ ∫ y, |(newtonRadial (x - y) - newtonRadial x) * g y| := abs_integral_le_integral_abs
      _ ≤ ∫ y, 2 * R * (‖x‖ ^ 2)⁻¹ * |g y| :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (hgi.abs.const_mul _) (Eventually.of_forall hb)
      _ = 2 * R * (‖x‖ ^ 2)⁻¹ * A := integral_const_mul _ _
      _ ≤ (8 * R * A) * ((1 + ‖x‖) ^ 2)⁻¹ := by
          have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
          have h4 : (‖x‖ ^ 2)⁻¹ ≤ 4 * ((1 + ‖x‖) ^ 2)⁻¹ := by
            rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), ← div_eq_inv_mul,
              div_le_iff₀ (by positivity)]
            nlinarith
          calc 2 * R * (‖x‖ ^ 2)⁻¹ * A = 2 * R * A * (‖x‖ ^ 2)⁻¹ := by ring
            _ ≤ 2 * R * A * (4 * ((1 + ‖x‖) ^ 2)⁻¹) := by gcongr
            _ = _ := by ring
  -- near bound
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : T3) (2 * R)).exists_bound_of_continuousOn
    (continuous_newtonPotential hg hc).continuousOn
  refine ⟨8 * R * A + |M| * (1 + 2 * R) ^ 2, fun x => ?_⟩
  have hA : 0 ≤ A := integral_nonneg fun _ => abs_nonneg _
  have hp : 0 ≤ ((1 + ‖x‖) ^ 2)⁻¹ := by positivity
  rw [add_mul]
  by_cases hx : 2 * R ≤ ‖x‖
  · have := far x hx
    have : 0 ≤ |M| * (1 + 2 * R) ^ 2 * ((1 + ‖x‖) ^ 2)⁻¹ := by positivity
    linarith
  · push Not at hx
    have hMx := hM x (by simpa using hx.le)
    rw [Real.norm_eq_abs] at hMx
    have : |M| ≤ |M| * (1 + 2 * R) ^ 2 * ((1 + ‖x‖) ^ 2)⁻¹ := by
      rw [mul_assoc]
      have : 1 ≤ (1 + 2 * R) ^ 2 * ((1 + ‖x‖) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
        have := norm_nonneg x
        nlinarith
      nlinarith [abs_nonneg M]
    have : 0 ≤ 8 * R * A * ((1 + ‖x‖) ^ 2)⁻¹ := by positivity
    linarith [le_abs_self M]

local notation "eS" j => (EuclideanSpace.single j (1 : ℝ) : T3)

/-- Derivatives of compactly supported `C¹` functions have mean zero. -/
theorem integral_fderiv_eq_zero {g : T3 → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (v : T3) : ∫ x, fderiv ℝ g x v = 0 := by
  have := integral_mul_fderiv_test (f := fun _ => (1 : ℝ)) contDiff_const hg hc v
  simpa using this

theorem IsTestOrbit.coord_contDiff {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (k : Fin 3) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => ω.val z k) := hω.1 k

theorem IsTestOrbit.coord_compact {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (k : Fin 3) :
    HasCompactSupport (fun z => ω.val z k) := by
  have := hω.2.comp_left (g := fun v : EuclideanSpace ℝ (Fin 3) => v k) (by simp)
  simpa [Function.comp_def] using this

/-- Coordinates of a divergence-free test field have mean zero. -/
theorem IsTestOrbit.integral_coord_eq_zero {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (k : Fin 3) :
    ∫ x, ω.val x k = 0 := by
  have hj : ∀ j : Fin 3, ContDiff ℝ 1 (fun y : T3 => y k * ω.val y j) := fun j =>
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) k).contDiff).mul ((hω.1 j).of_le (by simp))
  have hjc : ∀ j : Fin 3, HasCompactSupport (fun y : T3 => y k * ω.val y j) := fun j =>
    (hω.coord_compact j).mul_left
  have hpt : ∀ x, ω.val x k = ∑ j : Fin 3, fderiv ℝ (fun y : T3 => y k * ω.val y j) x (eS j) := by
    intro x
    have hd := ω.property x
    unfold NavierStokes3D.div at hd
    have e1 : ∀ j : Fin 3, fderiv ℝ (fun y : T3 => y k * ω.val y j) x (eS j) =
        (if j = k then ω.val x j else 0) + x k * fderiv ℝ (fun y => ω.val y j) x (eS j) := by
      intro j
      have hp : HasFDerivAt (fun y : T3 => y k) (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) k) x :=
        (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) k).hasFDerivAt
      have hw := ((hω.1 j).differentiable (by simp) x).hasFDerivAt
      rw [fderiv_fun_mul hp.differentiableAt hw.differentiableAt, hp.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
        PiLp.proj_apply, PiLp.single_apply]
      by_cases h : j = k
      · subst h; simp <;> ring
      · simp [h, Ne.symm h] <;> ring
    simp_rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum, hd, mul_zero, add_zero]
    simp
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_finset_sum]
  · exact Finset.sum_eq_zero fun j _ => integral_fderiv_eq_zero (hj j) (hjc j) _
  · intro j _
    exact (continuous_fderiv_apply (hj j) _).integrable_of_hasCompactSupport
      (hasCompactSupport_fderiv_apply (hjc j) _)

/-- Differentiable, decaying, with decaying coordinate derivatives. -/
def DGood (f : T3 → ℝ) : Prop :=
  Differentiable ℝ f ∧ Decays f ∧ ∀ j : Fin 3, Decays (fun x => fderiv ℝ f x (eS j))

theorem dGood_newtonPotential {g : T3 → ℝ} (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g)
    (hc : HasCompactSupport g) (h0 : ∫ y, g y = 0) : DGood (newtonPotential g) := by
  have g1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  refine ⟨(contDiff_newtonPotential hc hg).differentiable (by simp),
    decays_newtonPotential hg.continuous hc h0, fun j => ?_⟩
  rw [fderiv_newtonPotential_apply hc g1]
  have gj : ContDiff ℝ 1 (fun z => fderiv ℝ g z (eS j)) :=
    (hg.fderiv_right (m := 1) (by norm_cast)).clm_apply contDiff_const
  exact decays_newtonPotential gj.continuous (hasCompactSupport_fderiv_apply hc _)
    (integral_fderiv_eq_zero g1 hc _)

theorem DGood.sub {f g : T3 → ℝ} (hf : DGood f) (hg : DGood g) : DGood (fun x => f x - g x) := by
  refine ⟨hf.1.sub hg.1, hf.2.1.sub hg.2.1, fun j => ?_⟩
  have : (fun x => fderiv ℝ (fun x => f x - g x) x (eS j)) =
      fun x => fderiv ℝ f x (eS j) - fderiv ℝ g x (eS j) := by
    funext x; rw [fderiv_fun_sub (hf.1 x) (hg.1 x)]; rfl
  rw [this]; exact (hf.2.2 j).sub (hg.2.2 j)

theorem DGood.const_mul {f : T3 → ℝ} (hf : DGood f) (c : ℝ) : DGood (fun x => c * f x) := by
  refine ⟨hf.1.const_mul c, hf.2.1.const_mul c, fun j => ?_⟩
  have : (fun x => fderiv ℝ (fun x => c * f x) x (eS j)) = fun x => c * fderiv ℝ f x (eS j) := by
    funext x; rw [fderiv_const_mul (hf.1 x)]; rfl
  rw [this]; exact (hf.2.2 j).const_mul c

theorem DGood.congr {f g : T3 → ℝ} (hf : DGood f) (h : f = g) : DGood g := h ▸ hf

/-- Coordinates of `N ⋆ ω` for a test orbit are `DGood`. -/
theorem dGood_newtonVec {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (k : Fin 3) :
    DGood (fun y => newtonVec ω.val y k) := by
  rw [newtonVec_coord]
  exact dGood_newtonPotential (hω.1 k) (hω.coord_compact k) (hω.integral_coord_eq_zero k)

/-- Directional derivatives of `N ⋆ ω` coordinates are `DGood`. -/
theorem dGood_directionalCoord_newtonVec {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (k j : Fin 3) :
    DGood (directionalCoord (newtonVec ω.val) k j) := by
  have hk1 : ContDiff ℝ 1 (fun z => ω.val z k) := (hω.1 k).of_le (by simp)
  have : directionalCoord (newtonVec ω.val) k j =
      newtonPotential (fun z => fderiv ℝ (fun z => ω.val z k) z (eS j)) := by
    funext x; unfold directionalCoord
    rw [newtonVec_coord, congrFun (fderiv_newtonPotential_apply (hω.coord_compact k) hk1 _) x]
  rw [this]
  exact dGood_newtonPotential ((hω.1 k).fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by norm_cast) |>.clm_apply contDiff_const)
    (hasCompactSupport_fderiv_apply (hω.coord_compact k) _)
    (integral_fderiv_eq_zero hk1 (hω.coord_compact k) _)

theorem DGood.ibp {f g : T3 → ℝ} (hf : DGood f) (hg : DGood g) (j : Fin 3) :
    ∫ x, f x * fderiv ℝ g x (eS j) = -∫ x, fderiv ℝ f x (eS j) * g x :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ((hf.2.2 j).integrable_mul hg.2.1)
    (hf.2.1.integrable_mul (hg.2.2 j)) (hf.2.1.integrable_mul hg.2.1)
    (fun x _ => hf.1 x) (fun x _ => hg.1 x)

theorem integral_lin6 {f₁ f₂ f₃ f₄ f₅ f₆ : T3 → ℝ} (h₁ : Integrable f₁ (MeasureTheory.volume : Measure T3))
    (h₂ : Integrable f₂ (MeasureTheory.volume : Measure T3)) (h₃ : Integrable f₃ (MeasureTheory.volume : Measure T3))
    (h₄ : Integrable f₄ (MeasureTheory.volume : Measure T3)) (h₅ : Integrable f₅ (MeasureTheory.volume : Measure T3))
    (h₆ : Integrable f₆ (MeasureTheory.volume : Measure T3)) :
    ∫ x, (f₁ x - f₂ x + f₃ x - f₄ x + f₅ x - f₆ x) =
      (∫ x, f₁ x) - (∫ x, f₂ x) + (∫ x, f₃ x) - (∫ x, f₄ x) + (∫ x, f₅ x) - ∫ x, f₆ x := by
  have i2 : Integrable (fun x => f₁ x - f₂ x) (MeasureTheory.volume : Measure T3) := h₁.sub h₂
  have i3 : Integrable (fun x => f₁ x - f₂ x + f₃ x) (MeasureTheory.volume : Measure T3) := i2.add h₃
  have i4 : Integrable (fun x => f₁ x - f₂ x + f₃ x - f₄ x) (MeasureTheory.volume : Measure T3) :=
    i3.sub h₄
  have i5 : Integrable (fun x => f₁ x - f₂ x + f₃ x - f₄ x + f₅ x)
    (MeasureTheory.volume : Measure T3) := i4.add h₅
  rw [integral_sub i5 h₆, integral_add i4 h₅, integral_sub i3 h₄, integral_add i2 h₃,
    integral_sub h₁ h₂]

/-- **Curl is symmetric** on `DGood` fields: `∫ ⟪a, curl b⟫ = ∫ ⟪curl a, b⟫`. -/
theorem integral_pairing_curl_symm {a b : T3 → EuclideanSpace ℝ (Fin 3)}
    (ha : ∀ i, DGood (fun x => a x i)) (hb : ∀ i, DGood (fun x => b x i)) :
    ∫ x, pairing (a x) (curl b x) = ∫ x, pairing (curl a x) (b x) := by
  set P : Fin 3 → Fin 3 → Fin 3 → T3 → ℝ := fun i j k x => a x i * fderiv ℝ (fun y => b y k) x (eS j)
  set Q : Fin 3 → Fin 3 → Fin 3 → T3 → ℝ := fun i j k x => fderiv ℝ (fun y => a y i) x (eS j) * b x k
  have hP : ∀ i j k, Integrable (P i j k) (MeasureTheory.volume : Measure T3) := fun i j k =>
    (ha i).2.1.integrable_mul ((hb k).2.2 j)
  have hQ : ∀ i j k, Integrable (Q i j k) (MeasureTheory.volume : Measure T3) := fun i j k =>
    ((ha i).2.2 j).integrable_mul (hb k).2.1
  have hPQ : ∀ i j k, ∫ x, P i j k x = -∫ x, Q i j k x := fun i j k => (ha i).ibp (hb k) j
  have hl : ∀ x, pairing (a x) (curl b x) =
      P 0 1 2 x - P 0 2 1 x + P 1 2 0 x - P 1 0 2 x + P 2 0 1 x - P 2 1 0 x := by
    intro x
    obtain ⟨c0, c1, c2⟩ := curl_apply b x
    unfold pairing
    simp only [PiLp.inner_apply, Fin.sum_univ_three, c0, c1, c2, directionalCoord, P]
    simp only [inner, conj_trivial, RCLike.re_to_real]
    ring
  have hr : ∀ x, pairing (curl a x) (b x) =
      Q 2 1 0 x - Q 1 2 0 x + Q 0 2 1 x - Q 2 0 1 x + Q 1 0 2 x - Q 0 1 2 x := by
    intro x
    obtain ⟨c0, c1, c2⟩ := curl_apply a x
    unfold pairing
    simp only [PiLp.inner_apply, Fin.sum_univ_three, c0, c1, c2, directionalCoord, Q]
    simp only [inner, conj_trivial, RCLike.re_to_real]
    ring
  simp_rw [hl, hr]
  rw [integral_lin6 (hP _ _ _) (hP _ _ _) (hP _ _ _) (hP _ _ _) (hP _ _ _) (hP _ _ _),
    integral_lin6 (hQ _ _ _) (hQ _ _ _) (hQ _ _ _) (hQ _ _ _) (hQ _ _ _) (hQ _ _ _)]
  simp only [hPQ]
  ring

theorem dGood_biotSavart {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (i : Fin 3) :
    DGood (fun x => BiotSavart ω.val x i) := by
  have hB : (fun x => BiotSavart ω.val x i) = fun x => (4 * Real.pi)⁻¹ * curl (newtonVec ω.val) x i := by
    funext x; rw [biotSavart_eq_curl_newtonVec hω x]; simp
  rw [hB]
  refine DGood.const_mul ?_ _
  have D := dGood_directionalCoord_newtonVec hω
  fin_cases i
  · exact ((D 2 1).sub (D 1 2)).congr (funext fun x => (curl_apply _ x).1.symm)
  · exact ((D 0 2).sub (D 2 0)).congr (funext fun x => (curl_apply _ x).2.1.symm)
  · exact ((D 1 0).sub (D 0 1)).congr (funext fun x => (curl_apply _ x).2.2.symm)

/-- The kinetic-energy stream function `ψ = (4π)⁻¹ N ⋆ ω`. -/
noncomputable def keStream (ω : CoadjointOrbit) : T3 → EuclideanSpace ℝ (Fin 3) :=
  fun x => (4 * Real.pi)⁻¹ • newtonVec ω.val x

theorem keStream_coord (ω : CoadjointOrbit) (k : Fin 3) :
    (fun x => keStream ω x k) = fun x => (4 * Real.pi)⁻¹ * newtonVec ω.val x k := by
  funext x; simp [keStream]

theorem dGood_keStream {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (k : Fin 3) :
    DGood (fun x => keStream ω x k) := by
  rw [keStream_coord]; exact (dGood_newtonVec hω k).const_mul _

theorem contDiff_keStream {ω : CoadjointOrbit} (hω : IsTestOrbit ω) (k : Fin 3) :
    ContDiff ℝ 2 (fun x => keStream ω x k) := by
  rw [keStream_coord]
  simp_rw [show ∀ x, newtonVec ω.val x k = newtonPotential (fun z => ω.val z k) x from
    fun x => congrFun (newtonVec_coord ω.val k) x]
  exact (contDiff_const.mul (contDiff_newtonPotential (hω.coord_compact k) (hω.1 k))).of_le
    (by norm_cast)

theorem curl_keStream {ω : CoadjointOrbit} (hω : IsTestOrbit ω) :
    curl (keStream ω) = velocity_from_vorticity ω := by
  funext x
  rw [velocity_from_vorticity_eq_BiotSavart, biotSavart_eq_curl_newtonVec hω x]
  exact curl_smul _ _ x

theorem pairing_eq_sum (u v : EuclideanSpace ℝ (Fin 3)) :
    pairing u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
  unfold pairing
  simp only [PiLp.inner_apply, Fin.sum_univ_three, inner, conj_trivial, RCLike.re_to_real]
  ring

theorem integrable_pairing_of_dGood {a b : T3 → EuclideanSpace ℝ (Fin 3)}
    (ha : ∀ i, DGood (fun x => a x i)) (hb : ∀ i, DGood (fun x => b x i)) :
    Integrable (fun x => pairing (a x) (b x)) (MeasureTheory.volume : Measure T3) := by
  simp_rw [pairing_eq_sum]
  exact (((ha 0).2.1.integrable_mul (hb 0).2.1).add ((ha 1).2.1.integrable_mul (hb 1).2.1)).add
    ((ha 2).2.1.integrable_mul (hb 2).2.1)

/-- `∫ ⟪B ω, B ε⟫ = ∫ ⟪ψ, ε⟫` on the test class. -/
theorem integral_inner_biotSavart_eq {ω ε : CoadjointOrbit} (hω : IsTestOrbit ω)
    (hε : IsTestOrbit ε) :
    ∫ x, pairing (BiotSavart ω.val x) (BiotSavart ε.val x) =
      ∫ x, pairing (keStream ω x) (ε.val x) := by
  have h1 : ∀ x, pairing (BiotSavart ω.val x) (BiotSavart ε.val x) =
      pairing (BiotSavart ε.val x) (curl (keStream ω) x) := fun x => by
    rw [curl_keStream hω, velocity_from_vorticity_eq_BiotSavart]
    unfold pairing; exact real_inner_comm _ _
  simp_rw [h1]
  rw [integral_pairing_curl_symm (dGood_biotSavart hε) (dGood_keStream hω)]
  have hc := curlBiotSavartTest ε hε
  rw [velocity_from_vorticity_eq_BiotSavart] at hc
  simp_rw [hc]
  unfold pairing; simp_rw [real_inner_comm]

/-- Kinetic energy along an affine test line is a quadratic in `t`. -/
theorem kineticEnergy_line {ω ε : CoadjointOrbit} (hω : IsTestOrbit ω) (hε : IsTestOrbit ε) (t : ℝ)
    (hd : ∀ x, NavierStokes3D.div (fun y => ω.val y + t • ε.val y) x = 0) :
    KineticEnergyHamiltonian ⟨fun x => ω.val x + t • ε.val x, hd⟩ =
      KineticEnergyHamiltonian ω + t * (∫ x, pairing (BiotSavart ω.val x) (BiotSavart ε.val x)) +
        t ^ 2 * ((1 / 2) * ∫ x, pairing (BiotSavart ε.val x) (BiotSavart ε.val x)) := by
  have cω := hω.continuous; have cε := hε.continuous
  unfold KineticEnergyHamiltonian
  simp only
  have hpt : ∀ x, ‖BiotSavart (fun y => ω.val y + t • ε.val y) x‖ ^ 2 =
      pairing (BiotSavart ω.val x) (BiotSavart ω.val x) +
        t * (2 * pairing (BiotSavart ω.val x) (BiotSavart ε.val x)) +
        t ^ 2 * pairing (BiotSavart ε.val x) (BiotSavart ε.val x) := by
    intro x
    rw [BiotSavart_affine _ _ t (integrable_biotSavart_density cω hω.2 x)
      (integrable_biotSavart_density cε hε.2 x), ← real_inner_self_eq_norm_sq]
    unfold pairing
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      real_inner_comm (BiotSavart ω.val x) (BiotSavart ε.val x)]
    ring
  have hn : ∀ x, ‖BiotSavart ω.val x‖ ^ 2 = pairing (BiotSavart ω.val x) (BiotSavart ω.val x) :=
    fun x => by unfold pairing; rw [real_inner_self_eq_norm_sq]
  simp_rw [show (NavierStokes3D.volume : Measure T3) = MeasureTheory.volume from rfl, hpt, hn]
  have i1 := integrable_pairing_of_dGood (dGood_biotSavart hω) (dGood_biotSavart hω)
  have i2 := integrable_pairing_of_dGood (dGood_biotSavart hω) (dGood_biotSavart hε)
  have i4 := integrable_pairing_of_dGood (dGood_biotSavart hε) (dGood_biotSavart hε)
  have j2 : Integrable (fun x => t * (2 * pairing (BiotSavart ω.val x) (BiotSavart ε.val x)))
    (MeasureTheory.volume : Measure T3) := (i2.const_mul 2).const_mul t
  have j12 : Integrable (fun x => pairing (BiotSavart ω.val x) (BiotSavart ω.val x) +
      t * (2 * pairing (BiotSavart ω.val x) (BiotSavart ε.val x)))
    (MeasureTheory.volume : Measure T3) := i1.add j2
  have j4 : Integrable (fun x => t ^ 2 * pairing (BiotSavart ε.val x) (BiotSavart ε.val x))
    (MeasureTheory.volume : Measure T3) := i4.const_mul _
  rw [integral_add j12 j4, integral_add i1 j2, integral_const_mul, integral_const_mul,
    integral_const_mul]
  ring

/-- **The kinetic-energy Gâteaux representative** `ψ = (4π)⁻¹ N ⋆ ω` on the test class. -/
theorem keStream_isGateauxRep (ω : CoadjointOrbit) (hω : IsTestOrbit ω) :
    IsGateauxRepOn KineticEnergyHamiltonian ω hω (keStream ω) := by
  intro ε hε
  have hfun : (fun t : ℝ => KineticEnergyHamiltonian ⟨fun x => ω.val x + t • ε.val x,
      fun x => orbit_add_smul_div_free ω ε t (hω.1.differentiable) (hε.1.differentiable) x⟩) =
      fun t => KineticEnergyHamiltonian ω +
        t * (∫ x, pairing (BiotSavart ω.val x) (BiotSavart ε.val x)) +
        t ^ 2 * ((1 / 2) * ∫ x, pairing (BiotSavart ε.val x) (BiotSavart ε.val x)) :=
    funext fun t => kineticEnergy_line hω hε t _
  rw [hfun, show (NavierStokes3D.volume : Measure T3) = MeasureTheory.volume from rfl,
    ← integral_inner_biotSavart_eq hω hε]
  set A := ∫ x, pairing (BiotSavart ω.val x) (BiotSavart ε.val x)
  set Q := (1 / 2) * ∫ x, pairing (BiotSavart ε.val x) (BiotSavart ε.val x)
  have h1 : HasDerivAt (fun t : ℝ => t * A) A 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const A
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * Q) 0 0 := by
    simpa using ((hasDerivAt_pow 2 (0 : ℝ)).mul_const Q)
  simpa using ((hasDerivAt_const (0 : ℝ) (KineticEnergyHamiltonian ω)).add h1).add h2

/-- **`StreamFunctionRepModGradOn` holds unconditionally on the test class.** -/
theorem streamFunctionRepModGradOn (ω : CoadjointOrbit) (hω : IsTestOrbit ω) :
    StreamFunctionRepModGradOn ω hω :=
  streamFunctionRepModGradOn_of_exists curlFreeIsGradient (keStream ω) (contDiff_keStream hω)
    (keStream_isGateauxRep ω hω) (curl_keStream hω)

end MetriplecticWorldModel
