/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import FrohmanianSymplecticTether.VelocityTether
import TetherMayForm.Enstrophy
import MetriplecticWorldModel.Bracket
import MetriplecticWorldModel.Ceiling

/-!
# The Frohmanian tethered metriplectic world model

**This is a model, distinct from unmodified 3D Navier–Stokes.** Its equations add the tether
(metric) bracket to the Lie–Poisson flow and a `y³` damping at the vorticity maximum that the
unmodified equations do not have. Nothing here bears on the Clay Millennium problem.

Contents:
1. the velocity tether `-TetherKernelVel κ` (ported) as the metric bracket of a
   `MetriplecticSystem`, with energy degeneracy proved from `KineticEnergyCurlIdentity`;
2. the maximizer inequality `M' ≤ C M² − κ_eff M³` derived from the ported may-form `Prop`s;
3. the uniform ceiling and global smooth existence within the model, from named `Prop`s.
-/

open Set MeasureTheory NavierStokes3D ArnoldGeometric FrohmanianTether

namespace MetriplecticWorldModel

/-! ## 1. Velocity tether as metric bracket -/

/-- Named Prop: the entropy functional `S` is a Casimir of the Lie–Poisson bracket `P`. -/
def EntropyCasimir (P : Functional → Functional → ℝ) (S : Functional) : Prop := ∀ F, P F S = 0

/-- The model's metriplectic structure at an orbit `ω`: `P` any antisymmetric bracket, metric
bracket `G = −TetherKernelVel κ ω`, Hamiltonian the kinetic energy. -/
noncomputable def velocityTetherSystem (κ : ℝ) (hκ : 0 < κ) (ω : CoadjointOrbit)
    (P : Functional → Functional → ℝ) (hP : ∀ a b, P a b = -P b a) (S : Functional)
    (hcas : EntropyCasimir P S) (hcurl : KineticEnergyCurlIdentity ω)
    (hInt : Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) NavierStokes3D.volume) :
    MetriplecticSystem Functional where
  P := P
  G := fun F G => -TetherKernelVel κ ω F G
  P_antisymm := hP
  G_symm := fun a b => by rw [tetherKernelVel_comm]
  G_nonneg := fun a => by linarith [tetherKernelVel_diag_nonpos hκ a ω]
  dH := KineticEnergyHamiltonian
  dS := S
  degen_P := hcas
  degen_G := fun a => by rw [tetherKernelVel_C2_at a ω hcurl hInt, neg_zero]

/-- In the model, kinetic energy is conserved by the full generator. -/
theorem velocityTether_energy_conserved (κ : ℝ) (hκ : 0 < κ) (ω : CoadjointOrbit)
    (P : Functional → Functional → ℝ) (hP : ∀ a b, P a b = -P b a) (S : Functional)
    (hcas : EntropyCasimir P S) (hcurl : KineticEnergyCurlIdentity ω)
    (hInt : Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) NavierStokes3D.volume) :
    (velocityTetherSystem κ hκ ω P hP S hcas hcurl hInt).gen KineticEnergyHamiltonian = 0 :=
  energy_conserved _

/-- In the model, entropy production equals `−TetherKernelVel κ ω S S`, and is `≥ 0`. -/
theorem velocityTether_entropy_production (κ : ℝ) (hκ : 0 < κ) (ω : CoadjointOrbit)
    (P : Functional → Functional → ℝ) (hP : ∀ a b, P a b = -P b a) (S : Functional)
    (hcas : EntropyCasimir P S) (hcurl : KineticEnergyCurlIdentity ω)
    (hInt : Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) NavierStokes3D.volume) :
    (velocityTetherSystem κ hκ ω P hP S hcas hcurl hInt).gen S = -TetherKernelVel κ ω S S ∧
      0 ≤ (velocityTetherSystem κ hκ ω P hP S hcas hcurl hInt).gen S :=
  ⟨gen_entropy_eq _, entropy_production _⟩

/-- Ported (frohmanian-symplectic-tether-regularity), unconditional facts re-exported. -/
theorem ported_velocityTether_facts (κ : ℝ) (hκ : 0 < κ) :
    (∀ ω F G, TetherKernelVel κ ω F G = TetherKernelVel κ ω G F) ∧
    (∀ F ω, TetherKernelVel κ ω F F ≤ 0) ∧
    InvariantUnderCoadjointAction (TetherKernelVel κ) ∧
    ProducesControllableNegativeFeedbackVel κ (TetherKernelVel κ) ∧
    FeedbackAtMostVel κ (TetherKernelVel κ) :=
  ⟨tetherKernelVel_comm, fun F ω => tetherKernelVel_diag_nonpos hκ F ω, tetherKernelVel_C1,
    tetherKernelVel_C3, tetherKernelVel_feedbackAtMost⟩

/-! ## 2. The maximizer inequality (ported may-form `Prop`s) -/

open Frohman.Tether in
/-- At a maximizer with `y > 0`: the energy identity, the stretching bound, the viscous sign,
the tether feedback `−κ y⁴` and cross control give `y' ≤ C y² − (κ/2 − C_abs) y³`. -/
theorem maxpoint_rate (d : MaxPointData) (C κ Cabs : ℝ) (hκ : 0 < κ) (hy : 0 < d.y)
    (hE : EnergyIdentity d) (hS : StretchingCZ d C) (hV : ViscousAtMax d)
    (hT : TetherFeedback d κ) (hX : CrossControlled d κ Cabs) :
    d.y' ≤ C * d.y ^ 2 - (κ / 2 - Cabs) * d.y ^ 3 := by
  unfold EnergyIdentity at hE; unfold StretchingCZ at hS; unfold ViscousAtMax at hV
  unfold TetherFeedback at hT; unfold CrossControlled at hX
  have h1 : κ / 2 * d.y ^ 4 + 2 / κ * d.b ^ 2 - 2 * d.y ^ 2 * d.b
      = (κ * d.y ^ 2 - 2 * d.b) ^ 2 / (2 * κ) := by field_simp; ring
  have h2 : 0 ≤ (κ * d.y ^ 2 - 2 * d.b) ^ 2 / (2 * κ) := by positivity
  have h3 : d.y * d.y' ≤ d.y * (C * d.y ^ 2 - (κ / 2 - Cabs) * d.y ^ 3) := by
    nlinarith
  exact le_of_mul_le_mul_left h3 hy

/-! ## 3. Uniform ceiling and global smooth existence within the model -/

/-- Named Prop (model property): the sup-vorticity `M` is differentiable with
`M' ≤ C M² − κ M³` for all `t ≥ 0`. -/
def TetheredMaxRate (C κ : ℝ) (M M' : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivAt M (M' t) t ∧ M' t ≤ C * M t ^ 2 - κ * M t ^ 3

open Frohman.Tether in
/-- Named Prop: at every `t ≥ 0` the maximizer data realize `M t, M' t` and satisfy the may-form
`Prop`s (energy identity, stretching bound, viscous sign, tether feedback, cross control). -/
def MaxPointRealization (C κ Cabs : ℝ) (M M' : ℝ → ℝ) : Prop :=
  (∀ t, 0 ≤ t → HasDerivAt M (M' t) t) ∧
  ∀ t, 0 ≤ t → ∃ d : MaxPointData, d.y = M t ∧ d.y' = M' t ∧ 0 < d.y ∧ EnergyIdentity d ∧
    StretchingCZ d C ∧ ViscousAtMax d ∧ TetherFeedback d κ ∧ CrossControlled d κ Cabs

/-- `MaxPointRealization` yields `TetheredMaxRate` with `κ_eff = κ/2 − C_abs`. -/
theorem tetheredMaxRate_of_realization (C κ Cabs : ℝ) (hκ : 0 < κ) (M M' : ℝ → ℝ)
    (h : MaxPointRealization C κ Cabs M M') : TetheredMaxRate C (κ / 2 - Cabs) M M' := by
  intro t ht
  refine ⟨h.1 t ht, ?_⟩
  obtain ⟨d, hy, hy', hpos, hE, hS, hV, hT, hX⟩ := h.2 t ht
  have := maxpoint_rate d C κ Cabs hκ hpos hE hS hV hT hX
  rw [hy, hy'] at this; exact this

/-- Named Prop (model local theory, BKM-type continuation): if `M` is bounded on every
`[0,T]`, the model solution is smooth at every `t ≥ 0`. -/
def ModelContinuation (Smooth : ℝ → Prop) (M : ℝ → ℝ) : Prop :=
  (∀ T, 0 ≤ T → ∃ B, ∀ t ∈ Icc 0 T, M t ≤ B) → ∀ t, 0 ≤ t → Smooth t

/-- Uniform-in-time vorticity ceiling in the model (κ a general parameter `> 0`). -/
theorem model_uniform_ceiling (C κ : ℝ) (hκ : 0 < κ) (M M' : ℝ → ℝ)
    (hrate : TetheredMaxRate C κ M M') : ∀ t, 0 ≤ t → M t ≤ ceiling (M 0) C κ :=
  uniform_ceiling C κ hκ M M' (fun t ht => (hrate t ht).1) (fun t ht => (hrate t ht).2)

/-- **Global smooth existence within the model**, with the uniform ceiling. -/
theorem model_global_regularity (C κ : ℝ) (hκ : 0 < κ) (M M' : ℝ → ℝ) (Smooth : ℝ → Prop)
    (hrate : TetheredMaxRate C κ M M') (hcont : ModelContinuation Smooth M) :
    (∀ t, 0 ≤ t → Smooth t) ∧ ∀ t, 0 ≤ t → M t ≤ ceiling (M 0) C κ :=
  ⟨hcont (bounded_on_every_interval C κ hκ M M' (fun t ht => (hrate t ht).1)
      (fun t ht => (hrate t ht).2)), model_uniform_ceiling C κ hκ M M' hrate⟩

/-- Global regularity from the may-form maximizer data, with `κ_eff = κ/2 − C_abs > 0`. -/
theorem model_global_regularity_of_realization (C κ Cabs : ℝ) (hκ : 0 < κ)
    (hgap : Cabs < κ / 2) (M M' : ℝ → ℝ) (Smooth : ℝ → Prop)
    (h : MaxPointRealization C κ Cabs M M') (hcont : ModelContinuation Smooth M) :
    (∀ t, 0 ≤ t → Smooth t) ∧ ∀ t, 0 ≤ t → M t ≤ ceiling (M 0) C (κ / 2 - Cabs) :=
  model_global_regularity C _ (by linarith) M M' Smooth
    (tetheredMaxRate_of_realization C κ Cabs hκ M M' h) hcont

/-! ## 4. Separation from unmodified Navier–Stokes: at `κ = 0` there is no ceiling -/

/-- With `κ = 0` the inequality `M' ≤ C M²` (here `C = 1`) admits `M = 1/(1−t)`, which is
unbounded on `[0,1)`. So the ceiling is produced by the `κ M³` term alone. -/
theorem kappa_zero_no_ceiling :
    (∀ t : ℝ, t < 1 → HasDerivAt (fun s : ℝ => (1 - s)⁻¹) (((1 - t) ^ 2)⁻¹) t ∧
        ((1 - t) ^ 2)⁻¹ ≤ 1 * ((1 - t)⁻¹) ^ 2 - 0 * ((1 - t)⁻¹) ^ 3) ∧
      ¬ ∃ B, ∀ t ∈ Ico (0:ℝ) 1, (1 - t)⁻¹ ≤ B := by
  refine ⟨fun t ht => ⟨?_, by rw [inv_pow]; simp⟩, ?_⟩
  · have hne : (1 - t) ≠ 0 := by linarith
    have := ((hasDerivAt_id t).const_sub 1).inv hne
    convert this using 1; simp
  · rintro ⟨B, hB⟩
    have hpos : 0 < |B| + 1 := by positivity
    have ht : 1 - 1 / (|B| + 1) ∈ Ico (0:ℝ) 1 := by
      constructor
      · rw [sub_nonneg, div_le_one hpos]; linarith [abs_nonneg B]
      · have : 0 < 1 / (|B| + 1) := by positivity
        linarith
    have := hB _ ht
    rw [sub_sub_cancel, one_div, inv_inv] at this
    linarith [le_abs_self B]

end MetriplecticWorldModel
