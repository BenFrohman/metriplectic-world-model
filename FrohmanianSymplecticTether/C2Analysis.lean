/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman.

# C2 for `TetherKernel`: where it holds, where it fails, and the fix

For `H = ½∫|u|²` viewed as a functional of `ω`, the Gâteaux derivative is the stream function
`ψ` with `curl ψ = u`, not `u`. `TetherKernel` projects `δH/δω = ψ`, so C2 needs `Π_u ψ = 0`.

* **Holds** when `δH/δω` is a multiple of `u` (Beltrami: `curl u = λu` gives `ψ = u/λ`):
  `tetherKernel_C2_of_parallel`.
* **Fails** on the explicit two-mode shear on `T³`, `u = (sin z + sin 2z, cos z + cos 2z, 0)`,
  `ψ = (sin z + ½ sin 2z, cos z + ½ cos 2z, 0)`, `ω = (sin z + 2 sin 2z, cos z + 2 cos 2z, 0)`:
  `curl ψ = u`, `curl u = ω`, and the tether pairing of `H` with itself is `-(3/4)κπ ≠ 0` per
  unit `(x,y)`-cell area (`shear_C2_fails`).
* **Fix:** project the velocity slot `curl (δF/δω)` instead (`TetherKernelVel`). Then `H`
  enters as `curl ψ = u` and `Π_u u = 0`: `tetherKernelVel_C2`. This is the same as treating
  `H` as a functional of `u` (`δH/δu = u`). Since `curl` kills gradients, the velocity slot
  also does not depend on the gauge choice in `δF/δω`.
-/
module

public import FrohmanianSymplecticTether.SymplecticTether
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

@[expose] public section

namespace FrohmanianTether

open MeasureTheory ForMathlib ArnoldGeometric NavierStokes3D Real

variable {kappa : ℝ}

/-! ## Repository model -/

/-- `Π_u (r • u) = 0` when `u` has nonzero energy. -/
theorem Pi_u_smul_self (u : VelocityField) (r : ℝ)
    (hE : (∫ y, ‖u y‖ ^ 2 ∂NavierStokes3D.volume) ≠ 0) : Pi_u u (r • u) = 0 := by
  funext x
  have hp : (fun y => pairing ((r • u) y) (u y)) = fun y => r * ‖u y‖ ^ 2 := by
    funext y
    simp [pairing, real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [Pi_u, hp, integral_const_mul, Pi.zero_apply]
  rw [mul_div_assoc, div_self hE, mul_one, Pi.smul_apply, sub_self]

/-- **C2 where it holds.** If `δH/δω = r • u` (Beltrami orbits, `ψ = u/λ`) and the energy is
nonzero, the tether pairing against `H` vanishes. -/
theorem tetherKernel_C2_of_parallel (F : Functional) (ω : CoadjointOrbit) (r : ℝ)
    (hδ : FunctionalDerivative KineticEnergyHamiltonian ω = r • velocity_from_vorticity ω)
    (hE : (∫ y, ‖velocity_from_vorticity ω y‖ ^ 2 ∂NavierStokes3D.volume) ≠ 0) :
    TetherKernel kappa ω F KineticEnergyHamiltonian = 0 := by
  apply tetherKernel_of_right_factor_zero
  rw [hδ]
  exact Pi_u_smul_self _ r hE

/-- **Velocity-slot tether**: project `curl (δF/δω)` instead of `δF/δω`. -/
noncomputable def TetherKernelVel (kappa : ℝ) (ω : CoadjointOrbit) (F G : Functional) : ℝ :=
  -kappa * ∫ x,
    ‖ω.val x‖ ^ 2 *
      inner ℝ
        (Pi_u (velocity_from_vorticity ω) (curl (FunctionalDerivative F ω)) x)
        (Pi_u (velocity_from_vorticity ω) (curl (FunctionalDerivative G ω)) x)
    ∂NavierStokes3D.volume

/-- **C2 for the velocity-slot tether.** With `curl (δH/δω) = u` (the stream-function identity
`curl ψ = u`) and nonzero energy, the pairing against `H` vanishes for every `F`. -/
theorem tetherKernelVel_C2 (F : Functional) (ω : CoadjointOrbit)
    (hcurl : curl (FunctionalDerivative KineticEnergyHamiltonian ω) = velocity_from_vorticity ω)
    (hE : (∫ y, ‖velocity_from_vorticity ω y‖ ^ 2 ∂NavierStokes3D.volume) ≠ 0) :
    TetherKernelVel kappa ω F KineticEnergyHamiltonian = 0 := by
  unfold TetherKernelVel
  rw [hcurl]
  have h := Pi_u_smul_self (velocity_from_vorticity ω) 1 hE
  rw [one_smul] at h
  simp [h]

/-! ## Explicit shear on `T³` (fields depend on `z` only; `x,y` contribute a constant area) -/

noncomputable def psiS (z : ℝ) : ℝ × ℝ := (sin z + sin (2 * z) / 2, cos z + cos (2 * z) / 2)
noncomputable def uS (z : ℝ) : ℝ × ℝ := (sin z + sin (2 * z), cos z + cos (2 * z))
noncomputable def wS (z : ℝ) : ℝ × ℝ := (sin z + 2 * sin (2 * z), cos z + 2 * cos (2 * z))

/-- `curl (f(z), g(z), 0) = (-g'(z), f'(z), 0)`. -/
noncomputable def curlZ (v : ℝ → ℝ × ℝ) (z : ℝ) : ℝ × ℝ :=
  (-deriv (fun t => (v t).2) z, deriv (fun t => (v t).1) z)

theorem hasDerivAt_sin_mul (a z : ℝ) : HasDerivAt (fun t => sin (a * t)) (cos (a * z) * a) z :=
  ((hasDerivAt_id z).const_mul a |>.sin).congr_deriv (by simp)

theorem hasDerivAt_cos_mul (a z : ℝ) : HasDerivAt (fun t => cos (a * t)) (-sin (a * z) * a) z :=
  ((hasDerivAt_id z).const_mul a |>.cos).congr_deriv (by simp)

theorem curlZ_psiS : curlZ psiS = uS := by
  funext z
  have h1 : HasDerivAt (fun t => (psiS t).1) (cos z + cos (2 * z)) z := by
    have := (hasDerivAt_sin z).add ((hasDerivAt_sin_mul 2 z).div_const 2)
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun t => (psiS t).2) (-(sin z + sin (2 * z))) z := by
    have := (hasDerivAt_cos z).add ((hasDerivAt_cos_mul 2 z).div_const 2)
    exact this.congr_deriv (by ring)
  simp only [curlZ, h1.deriv, h2.deriv, uS, neg_neg]

theorem curlZ_uS : curlZ uS = wS := by
  funext z
  have h1 : HasDerivAt (fun t => (uS t).1) (cos z + 2 * cos (2 * z)) z := by
    have := (hasDerivAt_sin z).add (hasDerivAt_sin_mul 2 z)
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun t => (uS t).2) (-(sin z + 2 * sin (2 * z))) z := by
    have := (hasDerivAt_cos z).add (hasDerivAt_cos_mul 2 z)
    exact this.congr_deriv (by ring)
  simp only [curlZ, h1.deriv, h2.deriv, wS, neg_neg]

theorem integral_quad_cos (a b c : ℝ) :
    ∫ z in (0 : ℝ)..(2 * π), (a + b * cos z + c * cos z ^ 2) = 2 * π * a + c * π := by
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous _).intervalIntegrable _ _) ((by fun_prop : Continuous _).intervalIntegrable _ _),
    intervalIntegral.integral_add ((by fun_prop : Continuous _).intervalIntegrable _ _) ((by fun_prop : Continuous _).intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_cos, integral_cos_sq]
  simp

theorem pair_psi_u (z : ℝ) :
    (psiS z).1 * (uS z).1 + (psiS z).2 * (uS z).2 = 3 / 2 + 3 / 2 * cos z + 0 * cos z ^ 2 := by
  simp only [psiS, uS, sin_two_mul, cos_two_mul]
  linear_combination (cos z + 1) * (2 * cos z + 1) * sin_sq_add_cos_sq z

theorem norm_u (z : ℝ) :
    (uS z).1 ^ 2 + (uS z).2 ^ 2 = 2 + 2 * cos z + 0 * cos z ^ 2 := by
  simp only [uS, sin_two_mul, cos_two_mul]
  linear_combination (2 * cos z + 1) ^ 2 * sin_sq_add_cos_sq z

/-- Gram–Schmidt coefficient `⟨ψ,u⟩/⟨u,u⟩` over one period. -/
noncomputable def coefS : ℝ :=
  (∫ z in (0 : ℝ)..(2 * π), ((psiS z).1 * (uS z).1 + (psiS z).2 * (uS z).2)) /
    ∫ z in (0 : ℝ)..(2 * π), ((uS z).1 ^ 2 + (uS z).2 ^ 2)

theorem coefS_eq : coefS = 3 / 4 := by
  unfold coefS
  simp only [pair_psi_u, norm_u, integral_quad_cos]
  field_simp [pi_pos.ne']
  ring

/-- Tether pairing of `H` with itself on the shear: `-κ ∫ |ω|² |Π_u ψ|²` over one period. -/
noncomputable def shearTetherHH (kappa : ℝ) : ℝ :=
  -kappa * ∫ z in (0 : ℝ)..(2 * π),
    ((wS z).1 ^ 2 + (wS z).2 ^ 2) *
      (((psiS z).1 - coefS * (uS z).1) ^ 2 + ((psiS z).2 - coefS * (uS z).2) ^ 2)

theorem shearTetherHH_eq : shearTetherHH kappa = -(3 / 4) * kappa * π := by
  unfold shearTetherHH
  rw [coefS_eq]
  have hpt : ∀ z, ((wS z).1 ^ 2 + (wS z).2 ^ 2) *
      (((psiS z).1 - 3 / 4 * (uS z).1) ^ 2 + ((psiS z).2 - 3 / 4 * (uS z).2) ^ 2) =
      10 / 16 + (-2 / 16) * cos z + (-8 / 16) * cos z ^ 2 := by
    intro z
    simp only [wS, psiS, uS, sin_two_mul, cos_two_mul]
    linear_combination
      ((64 * cos z ^ 6 - 32 * cos z ^ 5 + 64 * cos z ^ 4 * sin z ^ 2 - 76 * cos z ^ 4
        - 32 * cos z ^ 3 * sin z ^ 2 + 20 * cos z ^ 3 - 12 * cos z ^ 2 * sin z ^ 2
        + 33 * cos z ^ 2 + 4 * cos z * sin z ^ 2 - 6 * cos z + sin z ^ 2 + 6) / 16)
        * sin_sq_add_cos_sq z
  simp only [hpt, integral_quad_cos]
  ring

/-- **C2 fails** on the two-mode shear: `Π_u ψ ≠ 0` and the tether pairing of `H` with itself
is `-(3/4)κπ`, nonzero for `κ ≠ 0`. -/
theorem shear_C2_fails (hk : kappa ≠ 0) : shearTetherHH kappa ≠ 0 := by
  rw [shearTetherHH_eq]
  have := pi_pos.ne'
  intro h
  have : kappa * π = 0 := by linarith
  rcases mul_eq_zero.mp this with h | h <;> simp_all

/-- On the same shear the velocity slot sees `curl ψ = u`, and `Π_u u = 0` (coefficient 1). -/
theorem shear_velocity_slot_coef :
    (∫ z in (0 : ℝ)..(2 * π), ((uS z).1 * (uS z).1 + (uS z).2 * (uS z).2)) /
      (∫ z in (0 : ℝ)..(2 * π), ((uS z).1 ^ 2 + (uS z).2 ^ 2)) = 1 := by
  have : ∀ z, (uS z).1 * (uS z).1 + (uS z).2 * (uS z).2 = (uS z).1 ^ 2 + (uS z).2 ^ 2 :=
    fun z => by ring
  simp only [this, norm_u, integral_quad_cos]
  field_simp [pi_pos.ne']

end FrohmanianTether
