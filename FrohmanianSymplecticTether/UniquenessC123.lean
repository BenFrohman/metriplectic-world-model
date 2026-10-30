/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianSymplecticTether.Uniqueness

/-!
# C1–C3 alone do not determine the tether kernel; two-sided feedback does

* `scaled_tether_admissible`: for `c ≥ 1`, `c · TetherKernel` is symmetric and satisfies C1, C3,
  and C2 whenever `TetherKernel` does.
* `c1_c3_not_unique`: if `TetherKernel` satisfies C2 and is nonzero somewhere on the diagonal,
  then `2 · TetherKernel` is a symmetric C1–C3 correction different from `TetherKernel`.
  So uniqueness needs an extra condition.
* `uniqueness_of_two_sided_feedback`: replace saturation by the minimality bound
  `B ω F F ≥ -κ ∫ |ω|² ‖Π_u δF‖²`. Together with C3 this forces the diagonal of `B`, and
  polarization gives `B = TetherKernel`.
* `step5_higher_order_vanishes`: a homogeneous remainder of degree `n ≥ 3` added to a
  degree-2 kernel cannot keep the sum of degree 2; it vanishes.
-/

open MeasureTheory ForMathlib ArnoldGeometric

namespace FrohmanianTether

variable {kappa : ℝ}

/-- `c · TetherKernel` with `c ≥ 1` is symmetric, C1, C3, and C2 when `TetherKernel` is. -/
public theorem scaled_tether_admissible (hκ : 0 < kappa) (c : ℝ) (hc : 1 ≤ c)
    (hC2T : DegenerateWRTKineticEnergy (TetherKernel kappa)) :
    let B := fun ω F G => c * TetherKernel kappa ω F G
    (∀ ω F G, B ω F G = B ω G F) ∧ InvariantUnderCoadjointAction B ∧
      DegenerateWRTKineticEnergy B ∧ ProducesControllableNegativeFeedback kappa B := by
  refine ⟨fun ω F G => by show c * _ = c * _; rw [tetherKernel_comm], fun g F G ω => by
    simp only [tetherKernel_C1 g F G ω], fun F ω => by simp only [hC2T F ω, mul_zero],
    fun F ω => ?_⟩
  show c * _ ≤ _
  rw [tetherKernel_quadratic_form]
  have hI : 0 ≤ ∫ x, ‖ω.val x‖ ^ 2 *
      ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2 ∂NavierStokes3D.volume :=
    integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  generalize (∫ x, ‖ω.val x‖ ^ 2 *
      ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2 ∂NavierStokes3D.volume) = I at hI ⊢
  have : 0 ≤ (c - 1) * (kappa * I) := mul_nonneg (by linarith) (mul_nonneg hκ.le hI)
  nlinarith

/-- **Scaffolding (ψ-slot).** C2 fails for this form (`shear_C2_fails`); the model is `TetherKernelVel` (VelocityTether.lean). C1–C3 and symmetry do not single out `TetherKernel`. -/
public theorem c1_c3_not_unique (hκ : 0 < kappa)
    (hC2T : DegenerateWRTKineticEnergy (TetherKernel kappa))
    (hne : ∃ ω F, TetherKernel kappa ω F F ≠ 0) :
    ∃ B : CoadjointOrbit → Functional → Functional → ℝ,
      (∀ ω F G, B ω F G = B ω G F) ∧ InvariantUnderCoadjointAction B ∧
      DegenerateWRTKineticEnergy B ∧ ProducesControllableNegativeFeedback kappa B ∧
      ∃ ω F G, B ω F G ≠ TetherKernel kappa ω F G := by
  obtain ⟨h1, h2, h3, h4⟩ := scaled_tether_admissible hκ 2 (by norm_num) hC2T
  obtain ⟨ω, F, hF⟩ := hne
  refine ⟨_, h1, h2, h3, h4, ω, F, F, ?_⟩
  intro h
  apply hF
  linarith

/-- Minimality: `B` dissipates no more than C3 requires. -/
public def FeedbackAtMost (kappa : ℝ) (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (F : Functional) (ω : CoadjointOrbit),
    -kappa * ∫ x, ‖ω.val x‖ ^ 2 *
        ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2 ∂NavierStokes3D.volume ≤ B ω F F

/-- C3 plus the minimality bound determine the quadratic form. -/
public theorem saturates_of_two_sided_feedback
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (hC3 : ProducesControllableNegativeFeedback kappa B) (hmin : FeedbackAtMost kappa B) :
    SaturatesTetherQuadratic kappa B := by
  intro F ω
  rw [tetherKernel_quadratic_form]
  exact le_antisymm (hC3 F ω) (hmin F ω)

/-- **Scaffolding (ψ-slot).** C2 fails for this form (`shear_C2_fails`); the model is `TetherKernelVel` (VelocityTether.lean). Uniqueness from C3, minimality and polarization, without assuming saturation. -/
public theorem uniqueness_of_two_sided_feedback
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (hC3 : ProducesControllableNegativeFeedback kappa B) (hmin : FeedbackAtMost kappa B)
    (h_polarB : Polarizes B) (h_polarT : Polarizes (TetherKernel kappa)) :
    ∀ ω F G, B ω F G = TetherKernel kappa ω F G := by
  intro ω F G
  have hs := saturates_of_two_sided_feedback B hC3 hmin
  have hB := h_polarB ω F G
  have hT := h_polarT ω F G
  have := hs F ω; have := hs G ω; have := hs (fun ω' => F ω' + G ω') ω
  linarith

/-- `TetherKernel` meets the minimality bound, so the class is nonempty. -/
public theorem tetherKernel_feedbackAtMost : FeedbackAtMost kappa (TetherKernel kappa) :=
  fun F ω => le_of_eq (tetherKernel_quadratic_form F ω).symm

/-- Step 5. If `B = Q + R` where `B` and `Q` scale with degree 2 and `R` with degree `n ≥ 3`
under some scaling `c` with `|c| > 1`, then `R = 0`. -/
public theorem step5_higher_order_vanishes {X : Type*} (scale : X → X) (c : ℝ) (hc : 1 < |c|)
    (B Q R : X → ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hsum : ∀ x, B x = Q x + R x)
    (hB : ∀ x, B (scale x) = c ^ 2 * B x) (hQ : ∀ x, Q (scale x) = c ^ 2 * Q x)
    (hR : ∀ x, R (scale x) = c ^ n * R x) :
    ∀ x, R x = 0 := by
  intro x
  have h1 := hsum (scale x)
  rw [hB, hQ, hR, hsum x] at h1
  have hne : c ^ n ≠ c ^ 2 := by
    intro h
    have h' : |c| ^ n = |c| ^ 2 := by rw [← abs_pow, ← abs_pow, h]
    have : |c| ^ 2 < |c| ^ n := pow_lt_pow_right₀ hc (by omega)
    linarith
  have : (c ^ n - c ^ 2) * R x = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h) hne
  · exact h

/-- Orbit scaling `ω ↦ c • ω`. -/
@[expose] public def scaleOrbit (c : ℝ) (ω : CoadjointOrbit) : CoadjointOrbit :=
  ⟨fun x => c • ω.val x, fun x => by rw [NavierStokes3D.div_smul, ω.property x, mul_zero]⟩

/-- **Scaffolding (ψ-slot).** C2 fails for this form (`shear_C2_fails`); the model is `TetherKernelVel` (VelocityTether.lean). **Step 5 for `TetherKernel`.** Fix `F, G` whose functional derivatives are invariant under
`ω ↦ c • ω` (`|c| > 1`). If a correction `B = TetherKernel + R` is degree 2 under this scaling
and `R` is degree `n ≥ 3`, then `R = 0`, i.e. `B = TetherKernel`. -/
public theorem step5_tetherKernel (F G : Functional) (c : ℝ) (hc : 1 < |c|)
    (hFD_F : ∀ ω, FunctionalDerivative F (scaleOrbit c ω) = FunctionalDerivative F ω)
    (hFD_G : ∀ ω, FunctionalDerivative G (scaleOrbit c ω) = FunctionalDerivative G ω)
    (B R : CoadjointOrbit → ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hsum : ∀ ω, B ω = TetherKernel kappa ω F G + R ω)
    (hB : ∀ ω, B (scaleOrbit c ω) = c ^ 2 * B ω)
    (hR : ∀ ω, R (scaleOrbit c ω) = c ^ n * R ω) :
    ∀ ω, B ω = TetherKernel kappa ω F G := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith
  have hR0 := step5_higher_order_vanishes (scaleOrbit c) c hc B
    (fun ω => TetherKernel kappa ω F G) R n hn hsum hB
    (fun ω => step2_degree_of_ne_zero F G ω c hc0 (hFD_F ω) (hFD_G ω)) hR
  intro ω; rw [hsum, hR0, add_zero]

end FrohmanianTether
