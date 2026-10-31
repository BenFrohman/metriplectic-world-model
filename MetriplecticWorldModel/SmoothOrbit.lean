/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.Model

/-!
# Smooth orbits, representatives modulo gradients, and the model evolution PDE

Note: in the ported files, `T3` is `EuclideanSpace ℝ (Fin 3)`, i.e. all of `ℝ³`, not the torus.
The original name is kept.

* `IsSmoothOrbit ω`: every coordinate of `ω` is `C^∞`.
* `grad φ`: coordinate gradient. `curl_grad_eq_zero` (**proved**): `curl (grad φ) = 0` for `C²` `φ`.
* `StreamFunctionRepModGrad ω` (named `Prop`, replaces the false-in-general exact uniqueness):
  there is a differentiable `ψ` with `curl ψ = u`, `ψ` a Gâteaux representative of the kinetic
  energy, and every representative equals `ψ + grad φ` for some `C²` `φ`.
* `kineticEnergyCurlIdentity_of_modGrad` (**proved**): that `Prop` implies
  `KineticEnergyCurlIdentity ω`. The `Prop` itself (Biot–Savart integration by parts plus
  Helmholtz uniqueness) is not proved here.
* `ModelVorticityPDE`: the model's evolution equation
  `∂ₜω + (u·∇)ω − (ω·∇)u = νΔω + Tterm`, `u = BiotSavart ω`, `div ω = 0` (definition only).
-/

open NavierStokes3D ArnoldGeometric FrohmanianTether

namespace MetriplecticWorldModel

def IsSmoothOrbit (ω : CoadjointOrbit) : Prop := ∀ i, ContDiff ℝ ⊤ (fun y => ω.val y i)

theorem IsSmoothOrbit.differentiable {ω : CoadjointOrbit} (h : IsSmoothOrbit ω) :
    ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x :=
  fun i x => ((h i).differentiable (by simp)).differentiableAt

/-- Coordinate gradient `∑ᵢ ∂ᵢφ eᵢ`. -/
noncomputable def grad (φ : T3 → ℝ) : VelocityField :=
  fun y => ∑ i : Fin 3, (fderiv ℝ φ y (EuclideanSpace.single i 1)) • EuclideanSpace.single i 1

theorem grad_apply (φ : T3 → ℝ) (y : T3) (c : Fin 3) :
    grad φ y c = fderiv ℝ φ y (EuclideanSpace.single c 1) := by
  simp [grad, Fin.sum_univ_three, EuclideanSpace.single_apply]
  fin_cases c <;> simp

theorem directionalCoord_grad (φ : T3 → ℝ) (hφ : ContDiff ℝ 2 φ) (c d : Fin 3) (x : T3) :
    directionalCoord (grad φ) c d x =
      fderiv ℝ (fderiv ℝ φ) x (EuclideanSpace.single d 1) (EuclideanSpace.single c 1) := by
  unfold directionalCoord
  simp_rw [grad_apply]
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)).differentiableAt
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem curl_grad_eq_zero (φ : T3 → ℝ) (hφ : ContDiff ℝ 2 φ) : curl (grad φ) = 0 := by
  funext x
  have hs : IsSymmSndFDerivAt ℝ φ x :=
    hφ.contDiffAt.isSymmSndFDerivAt (by simp)
  unfold curl
  simp only [directionalCoord_grad φ hφ, hs.eq _ _, sub_self]
  ext i; fin_cases i <;> simp [EuclideanSpace.single_apply]

/-- Named `Prop`: stream-function representative, unique modulo gradients. -/
def StreamFunctionRepModGrad (ω : CoadjointOrbit) : Prop :=
  ∃ ψ : T3 → EuclideanSpace ℝ (Fin 3),
    (∀ c, Differentiable ℝ (fun y => ψ y c)) ∧
    IsGateauxRepresentative KineticEnergyHamiltonian ω ψ ∧
    curl ψ = velocity_from_vorticity ω ∧
    ∀ d, IsGateauxRepresentative KineticEnergyHamiltonian ω d →
      ∃ φ : T3 → ℝ, ContDiff ℝ 2 φ ∧ d = fun y => ψ y + grad φ y

theorem curl_add_grad (ψ : VelocityField) (hψ : ∀ c, Differentiable ℝ (fun y => ψ y c))
    (φ : T3 → ℝ) (hφ : ContDiff ℝ 2 φ) : curl (fun y => ψ y + grad φ y) = curl ψ := by
  have hg : ∀ c, Differentiable ℝ (fun y => grad φ y c) := by
    intro c; simp_rw [grad_apply]
    exact fun y => ((hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
      |>.clm_apply (differentiable_const _)) y
  have hadd : ∀ c d x, directionalCoord (fun y => ψ y + grad φ y) c d x =
      directionalCoord ψ c d x + directionalCoord (grad φ) c d x := by
    intro c d x; unfold directionalCoord
    have : (fun y => (ψ y + grad φ y) c) = fun y => ψ y c + grad φ y c := by
      funext y; simp
    rw [this, fderiv_fun_add (hψ c x) (hg c x)]; rfl
  funext x
  have hs : IsSymmSndFDerivAt ℝ φ x := hφ.contDiffAt.isSymmSndFDerivAt (by simp)
  unfold curl
  simp only [hadd, directionalCoord_grad φ hφ, hs.eq _ _, add_sub_add_right_eq_sub]

theorem kineticEnergyCurlIdentity_of_modGrad (ω : CoadjointOrbit)
    (h : StreamFunctionRepModGrad ω) : KineticEnergyCurlIdentity ω := by
  obtain ⟨ψ, hψd, hrep, hcurl, huniq⟩ := h
  unfold KineticEnergyCurlIdentity
  have hex : ∃ d, IsGateauxRepresentative KineticEnergyHamiltonian ω d := ⟨ψ, hrep⟩
  rw [FunctionalDerivative_eq_choose hex]
  obtain ⟨φ, hφ, hd⟩ := huniq _ (Classical.choose_spec hex)
  rw [hd, curl_add_grad ψ hψd φ hφ, hcurl]

/-- The model's vorticity evolution (definition): `∂ₜω + (u·∇)ω − (ω·∇)u = νΔω + Tterm`,
`u = BiotSavart ω`, `div ω = 0`. `Tterm` is the tether forcing; `Tterm = 0` is unmodified
Navier–Stokes in vorticity form. -/
def ModelVorticityPDE (ν : ℝ) (ω u Tterm : ℝ → VelocityField) : Prop :=
  ∀ t, u t = BiotSavart (ω t) ∧ (∀ x, div (ω t) x = 0) ∧
    ∀ x, time_deriv ω t x + convective (u t) (ω t) x - convective (ω t) (u t) x =
      ν • laplacian (ω t) x + Tterm t x

end MetriplecticWorldModel
