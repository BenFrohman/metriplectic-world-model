/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.SmoothOrbit

/-!
# Audit fixes: log-loss stretching, Arnold bracket, viscous bracket

* `StretchingLogLoss d C₁ C₂`: `St ≤ C₁ y³ + C₂ y³ log(1+y)`, the log-loss shape of the known
  `L∞` bound (Kozono–Taniuchi type), replacing the pure `y³` `StretchingCZ`, which is stronger
  than anything known for Navier–Stokes. Still a named `Prop` on maximizer data.
* `maxpoint_rate_logLoss` (**proved**): with log-loss stretching the rate still closes, with
  effective damping `κ/4 − C_abs` and constant `C₁ + κ/4 + 4C₂²/κ`. So the ceiling does not need
  the false-as-`L∞` pure `y³` bound.
* `classicalBracket_antisymm` (**proved**): the ported Arnold bracket
  `∫ ω·(δF × δG)` is antisymmetric, so it can fill the `P` slot.
* `ViscousBracket` (**proved** symmetric and positive semidefinite). It is **not** degenerate
  with respect to kinetic energy (viscosity dissipates energy), so adding it to `G` breaks
  `degen_G`; a degenerate metriplectic form with viscosity needs an internal-energy/entropy
  variable, which is not built here.
-/

open MeasureTheory NavierStokes3D ArnoldGeometric FrohmanianTether Frohman.Tether

namespace MetriplecticWorldModel

def StretchingLogLoss (d : MaxPointData) (C₁ C₂ : ℝ) : Prop :=
  d.St ≤ C₁ * d.y ^ 3 + C₂ * d.y ^ 3 * Real.log (1 + d.y)

theorem maxpoint_rate_logLoss (d : MaxPointData) (C₁ C₂ κ Cabs : ℝ) (hκ : 0 < κ)
    (hC₂ : 0 ≤ C₂) (hy : 0 < d.y)
    (hE : EnergyIdentity d) (hS : StretchingLogLoss d C₁ C₂) (hV : ViscousAtMax d)
    (hT : TetherFeedback d κ) (hX : CrossControlled d κ Cabs) :
    d.y' ≤ (C₁ + κ / 4 + 4 * C₂ ^ 2 / κ) * d.y ^ 2 - (κ / 4 - Cabs) * d.y ^ 3 := by
  unfold EnergyIdentity at hE; unfold StretchingLogLoss at hS; unfold ViscousAtMax at hV
  unfold TetherFeedback at hT; unfold CrossControlled at hX
  -- log(1+y) ≤ 2 √(1+y)
  set s := Real.sqrt (1 + d.y)
  have hs2 : s ^ 2 = 1 + d.y := Real.sq_sqrt (by linarith)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
  have hlog : Real.log (1 + d.y) ≤ 2 * s := by
    have h := Real.log_le_sub_one_of_pos hs0
    have : Real.log (1 + d.y) = 2 * Real.log s := by
      rw [← hs2, Real.log_pow]; push_cast; ring
    linarith
  have hamgm : 2 * C₂ * s ≤ κ / 4 * s ^ 2 + 4 * C₂ ^ 2 / κ := by
    have : 0 ≤ (κ * s - 4 * C₂) ^ 2 / (4 * κ) := by positivity
    have e : κ / 4 * s ^ 2 + 4 * C₂ ^ 2 / κ - 2 * C₂ * s = (κ * s - 4 * C₂) ^ 2 / (4 * κ) := by
      field_simp; ring
    linarith
  have hy3 : 0 ≤ d.y ^ 3 := by positivity
  have hSt : d.St ≤ (C₁ + κ / 4 + 4 * C₂ ^ 2 / κ) * d.y ^ 3 + κ / 4 * d.y ^ 4 := by
    have h1 : C₂ * Real.log (1 + d.y) ≤ κ / 4 * (1 + d.y) + 4 * C₂ ^ 2 / κ := by
      nlinarith [mul_le_mul_of_nonneg_left hlog hC₂]
    have h2 := mul_le_mul_of_nonneg_left h1 hy3
    nlinarith
  have h1 : κ / 2 * d.y ^ 4 + 2 / κ * d.b ^ 2 - 2 * d.y ^ 2 * d.b
      = (κ * d.y ^ 2 - 2 * d.b) ^ 2 / (2 * κ) := by field_simp; ring
  have h2 : 0 ≤ (κ * d.y ^ 2 - 2 * d.b) ^ 2 / (2 * κ) := by positivity
  have h3 : d.y * d.y' ≤
      d.y * ((C₁ + κ / 4 + 4 * C₂ ^ 2 / κ) * d.y ^ 2 - (κ / 4 - Cabs) * d.y ^ 3) := by
    nlinarith
  exact le_of_mul_le_mul_left h3 hy

theorem classicalBracket_antisymm (F G : Functional) (ω : CoadjointOrbit) :
    ClassicalBracket F G ω = -ClassicalBracket G F ω :=
  ClassicalBracket_antisymm F G ω

/-- Viscous bracket `ν ∫ ∑ᵢ ⟨∂ᵢ curl δF, ∂ᵢ curl δG⟩`. -/
noncomputable def ViscousBracket (ν : ℝ) (ω : CoadjointOrbit) (F G : Functional) : ℝ :=
  ν * ∫ x, ∑ i : Fin 3,
    inner ℝ (fderiv ℝ (curl (FunctionalDerivative F ω)) x (EuclideanSpace.single i 1))
      (fderiv ℝ (curl (FunctionalDerivative G ω)) x (EuclideanSpace.single i 1))
      ∂NavierStokes3D.volume

theorem viscousBracket_symm (ν : ℝ) (ω : CoadjointOrbit) (F G : Functional) :
    ViscousBracket ν ω F G = ViscousBracket ν ω G F := by
  simp only [ViscousBracket, real_inner_comm]

theorem viscousBracket_nonneg (ν : ℝ) (hν : 0 ≤ ν) (ω : CoadjointOrbit) (F : Functional) :
    0 ≤ ViscousBracket ν ω F F := by
  unfold ViscousBracket
  refine mul_nonneg hν (integral_nonneg fun x => Finset.sum_nonneg fun i _ => ?_)
  exact real_inner_self_nonneg

end MetriplecticWorldModel
