/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman.

# The velocity-slot tether (the model)

`TetherKernelVel κ ω F G = -κ ∫ |ω|² ⟨Π_u curl(δF/δω), Π_u curl(δG/δω)⟩`.

The earlier `TetherKernel` projects `δF/δω` directly. For `H = ½∫|u|²` that slot is the stream
function `ψ`, and C2 fails (`shear_C2_fails`), so `TetherKernel` and the results built on it are
scaffolding. Here the main results are redone for `TetherKernelVel`:

* symmetry, the quadratic form, C1, C3, and the pointwise sign;
* C2, from the stream-function identity `curl(δH/δω) = u` (`KineticEnergyCurlIdentity`, a named
  hypothesis, implied by `StreamFunctionRepresentative`) plus finite energy;
* polarization, from additivity of the projected slot plus integrability;
* uniqueness from C3, the minimality bound and polarization;
* non-uniqueness from C1–C3 alone (`2 · TetherKernelVel`), with C2 coming from the hypotheses
  above rather than from a false identity;
* degree 2 under `ω ↦ cω`, and Step 5 (no degree `≥ 3` remainder);
* the metriplectic split and the `P1`–`P4` product theorem.
-/
module

public import FrohmanianSymplecticTether.C2Analysis
public import FrohmanianSymplecticTether.UniquenessC123
public import FrohmanianSymplecticTether.FinalProductTheorem

@[expose] public section

namespace FrohmanianTether

open MeasureTheory ForMathlib ArnoldGeometric NavierStokes3D
open FrohmanianSymplecticTether.FinalProductTheorem

variable {kappa : ℝ}

/-- Projected velocity slot `Π_u curl(δF/δω)`. -/
noncomputable def velSlot (ω : CoadjointOrbit) (F : Functional) : VelocityField :=
  Pi_u (velocity_from_vorticity ω) (curl (FunctionalDerivative F ω))

theorem tetherKernelVel_eq (ω : CoadjointOrbit) (F G : Functional) :
    TetherKernelVel kappa ω F G =
      -kappa * ∫ x, ‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω F x) (velSlot ω G x)
        ∂NavierStokes3D.volume := rfl

/-- The stream-function identity `curl(δH/δω) = u` at `ω` (dischargeable via
`kineticEnergyCurlIdentity_of_streamFunctionRepresentative` from `StreamFunctionRepresentative`). -/
def KineticEnergyCurlIdentity (ω : CoadjointOrbit) : Prop :=
  curl (FunctionalDerivative KineticEnergyHamiltonian ω) = velocity_from_vorticity ω

/-- `dH` is the only Gâteaux representative of `F` at `ω`. -/
def GateauxRepresentativeUnique (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit)
    (dH : T3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ d, IsGateauxRepresentative F ω d → d = dH

/-- If `dH` is a Gâteaux representative of `F` at `ω` and is unique, the choice-based
`FunctionalDerivative F ω` equals `dH`. -/
theorem functionalDerivative_eq_of_unique_repr (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit)
    (dH : T3 → EuclideanSpace ℝ (Fin 3)) (h : IsGateauxRepresentative F ω dH)
    (huniq : GateauxRepresentativeUnique F ω dH) : FunctionalDerivative F ω = dH := by
  have hex : ∃ d, IsGateauxRepresentative F ω d := ⟨dH, h⟩
  rw [FunctionalDerivative_eq_choose hex]
  exact huniq _ (Classical.choose_spec hex)

/-- Remaining hypothesis for `KineticEnergyCurlIdentity` at `ω`: there is a stream function `ψ`
that is the unique Gâteaux representative of the kinetic energy at `ω` and has `curl ψ = u`.
Not proved here for fields on `T3` (it needs Biot–Savart integration by parts). On a single
Fourier mode the analogous statement is proved in torus-fourier-ns-lemmas
(`curl_modeFunctionalDerivative_eq_u`). -/
def StreamFunctionRepresentative (ω : CoadjointOrbit) : Prop :=
  ∃ ψ : T3 → EuclideanSpace ℝ (Fin 3),
    IsGateauxRepresentative KineticEnergyHamiltonian ω ψ ∧
    GateauxRepresentativeUnique KineticEnergyHamiltonian ω ψ ∧
    curl ψ = velocity_from_vorticity ω

theorem kineticEnergyCurlIdentity_of_streamFunctionRepresentative (ω : CoadjointOrbit)
    (h : StreamFunctionRepresentative ω) : KineticEnergyCurlIdentity ω := by
  obtain ⟨ψ, hrep, huniq, hcurl⟩ := h
  unfold KineticEnergyCurlIdentity
  rw [functionalDerivative_eq_of_unique_repr _ ω ψ hrep huniq]
  exact hcurl

/-! ## Symmetry, quadratic form, sign, C1, C3 -/

theorem tetherKernelVel_comm (ω : CoadjointOrbit) (F G : Functional) :
    TetherKernelVel kappa ω F G = TetherKernelVel kappa ω G F := by
  simp only [tetherKernelVel_eq, real_inner_comm]

theorem tetherKernelVel_quadratic_form (F : Functional) (ω : CoadjointOrbit) :
    TetherKernelVel kappa ω F F =
      -kappa * ∫ x, ‖ω.val x‖ ^ 2 * ‖velSlot ω F x‖ ^ 2 ∂NavierStokes3D.volume := by
  simp only [tetherKernelVel_eq, real_inner_self_eq_norm_sq]

theorem tetherKernelVel_diag_nonpos (hκ : 0 < kappa) (F : Functional) (ω : CoadjointOrbit) :
    TetherKernelVel kappa ω F F ≤ 0 := by
  rw [tetherKernelVel_quadratic_form]
  exact mul_nonpos_of_nonpos_of_nonneg (by linarith)
    (integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Pointwise density `-κ |ω|² ‖Π_u curl δF‖²`. -/
noncomputable def velPointwiseDensity (kappa : ℝ) (ω : CoadjointOrbit) (F : Functional)
    (x : T3) : ℝ := -kappa * ‖ω.val x‖ ^ 2 * ‖velSlot ω F x‖ ^ 2

theorem velPointwiseDensity_strict_neg (hκ : 0 < kappa) (ω : CoadjointOrbit) (F : Functional)
    (x : T3) (hω : ω.val x ≠ 0) (hP : velSlot ω F x ≠ 0) :
    velPointwiseDensity kappa ω F x < 0 := by
  unfold velPointwiseDensity
  have h1 : 0 < ‖ω.val x‖ ^ 2 := by positivity
  have h2 : 0 < ‖velSlot ω F x‖ ^ 2 := by positivity
  have := mul_pos (mul_pos hκ h1) h2
  linarith

theorem tetherKernelVel_C1 : InvariantUnderCoadjointAction (TetherKernelVel kappa) := by
  intro g F G ω; simp [CoadjointAction]

/-- C3 for the velocity slot. -/
def ProducesControllableNegativeFeedbackVel (kappa : ℝ)
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ F ω, B ω F F ≤ -kappa * ∫ x, ‖ω.val x‖ ^ 2 * ‖velSlot ω F x‖ ^ 2 ∂NavierStokes3D.volume

/-- Minimality bound for the velocity slot. -/
def FeedbackAtMostVel (kappa : ℝ) (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ F ω, -kappa * ∫ x, ‖ω.val x‖ ^ 2 * ‖velSlot ω F x‖ ^ 2 ∂NavierStokes3D.volume ≤ B ω F F

theorem tetherKernelVel_C3 : ProducesControllableNegativeFeedbackVel kappa (TetherKernelVel kappa) :=
  fun F ω => le_of_eq (tetherKernelVel_quadratic_form F ω)

theorem tetherKernelVel_feedbackAtMost : FeedbackAtMostVel kappa (TetherKernelVel kappa) :=
  fun F ω => le_of_eq (tetherKernelVel_quadratic_form F ω).symm

/-! ## C2 -/

/-- At one orbit: `curl(δH/δω) = u` and finite energy give `TetherKernelVel ω F H = 0`. -/
theorem tetherKernelVel_C2_at (F : Functional) (ω : CoadjointOrbit)
    (hcurl : KineticEnergyCurlIdentity ω)
    (hInt : Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) NavierStokes3D.volume) :
    TetherKernelVel kappa ω F KineticEnergyHamiltonian = 0 := by
  by_cases hE : (∫ y, ‖velocity_from_vorticity ω y‖ ^ 2 ∂NavierStokes3D.volume) ≠ 0
  · exact tetherKernelVel_C2 F ω hcurl hE
  · simp only [ne_eq, not_not] at hE
    set u := velocity_from_vorticity ω
    have hae : (fun y => ‖u y‖ ^ 2) =ᵐ[NavierStokes3D.volume] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hInt).mp hE
    have hu : u =ᵐ[NavierStokes3D.volume] 0 :=
      hae.mono fun x hx => norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (by simpa using hx))
    rw [tetherKernelVel_eq]
    have hker : (fun x => ‖ω.val x‖ ^ 2 *
        inner ℝ (velSlot ω F x) (velSlot ω KineticEnergyHamiltonian x))
        =ᵐ[NavierStokes3D.volume] 0 := by
      refine hu.mono fun x hx => ?_
      simp only [velSlot, KineticEnergyCurlIdentity] at *
      rw [hcurl]
      simp [Pi_u, u, hx]
    rw [integral_congr_ae hker]
    simp

/-- **C2 for the velocity-slot tether.** -/
theorem tetherKernelVel_degenerate
    (hcurl : ∀ ω, KineticEnergyCurlIdentity ω)
    (hInt : ∀ ω, Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) NavierStokes3D.volume) :
    DegenerateWRTKineticEnergy (TetherKernelVel kappa) :=
  fun F ω => tetherKernelVel_C2_at F ω (hcurl ω) (hInt ω)

/-! ## Polarization -/

/-- Polarization for `TetherKernelVel` at `(ω, F, G)`, from additivity of the projected slot and
integrability of the three diagonal/off-diagonal integrands. -/
theorem tetherKernelVel_polarizes_at (ω : CoadjointOrbit) (F G : Functional)
    (hadd : velSlot ω (fun ω' => F ω' + G ω') = velSlot ω F + velSlot ω G)
    (hFF : Integrable (fun x => ‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω F x) (velSlot ω F x))
      NavierStokes3D.volume)
    (hGG : Integrable (fun x => ‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω G x) (velSlot ω G x))
      NavierStokes3D.volume)
    (hFG : Integrable (fun x => ‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω F x) (velSlot ω G x))
      NavierStokes3D.volume) :
    2 * TetherKernelVel kappa ω F G =
      TetherKernelVel kappa ω (fun ω' => F ω' + G ω') (fun ω' => F ω' + G ω') -
        TetherKernelVel kappa ω F F - TetherKernelVel kappa ω G G := by
  simp only [tetherKernelVel_eq, hadd]
  have hpt : (fun x => ‖ω.val x‖ ^ 2 * inner ℝ ((velSlot ω F + velSlot ω G) x)
      ((velSlot ω F + velSlot ω G) x)) = fun x =>
      (‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω F x) (velSlot ω F x) +
        ‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω G x) (velSlot ω G x)) +
        2 * (‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω F x) (velSlot ω G x)) := by
    funext x
    simp only [Pi.add_apply, inner_add_left, inner_add_right, real_inner_comm (velSlot ω F x)]
    ring
  rw [hpt]
  have e := integral_add (μ := NavierStokes3D.volume)
    (f := fun x => ‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω F x) (velSlot ω F x) +
      ‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω G x) (velSlot ω G x))
    (g := fun x => 2 * (‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω F x) (velSlot ω G x)))
    (hFF.add hGG) (hFG.const_mul 2)
  have e2 := integral_add hFF hGG
  rw [e, e2, integral_const_mul]
  ring

theorem tetherKernelVel_polarizes
    (hadd : ∀ ω F G, velSlot ω (fun ω' => F ω' + G ω') = velSlot ω F + velSlot ω G)
    (hint : ∀ ω F G, Integrable
      (fun x => ‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω F x) (velSlot ω G x)) NavierStokes3D.volume) :
    Polarizes (TetherKernelVel kappa) := fun ω F G =>
  tetherKernelVel_polarizes_at ω F G (hadd ω F G) (hint ω F F) (hint ω G G) (hint ω F G)

/-! ## Uniqueness and non-uniqueness -/

/-- **Uniqueness.** C3, the minimality bound and polarization force `B = TetherKernelVel`. -/
theorem uniqueness_vel (B : CoadjointOrbit → Functional → Functional → ℝ)
    (hC3 : ProducesControllableNegativeFeedbackVel kappa B) (hmin : FeedbackAtMostVel kappa B)
    (hPB : Polarizes B) (hPT : Polarizes (TetherKernelVel kappa)) :
    ∀ ω F G, B ω F G = TetherKernelVel kappa ω F G := by
  have hs : ∀ F ω, B ω F F = TetherKernelVel kappa ω F F := fun F ω => by
    rw [tetherKernelVel_quadratic_form]; exact le_antisymm (hC3 F ω) (hmin F ω)
  intro ω F G
  have := hPB ω F G; have := hPT ω F G
  have := hs F ω; have := hs G ω; have := hs (fun ω' => F ω' + G ω') ω
  linarith

/-- **C1–C3 alone do not determine the tether.** `2 · TetherKernelVel` is symmetric, C1, C2, C3
whenever C2 holds for `TetherKernelVel` (e.g. from `tetherKernelVel_degenerate`). -/
theorem c1_c3_not_unique_vel (hκ : 0 < kappa)
    (hC2 : DegenerateWRTKineticEnergy (TetherKernelVel kappa))
    (hne : ∃ ω F, TetherKernelVel kappa ω F F ≠ 0) :
    ∃ B : CoadjointOrbit → Functional → Functional → ℝ,
      (∀ ω F G, B ω F G = B ω G F) ∧ InvariantUnderCoadjointAction B ∧
      DegenerateWRTKineticEnergy B ∧ ProducesControllableNegativeFeedbackVel kappa B ∧
      ∃ ω F G, B ω F G ≠ TetherKernelVel kappa ω F G := by
  obtain ⟨ω₀, F₀, hF₀⟩ := hne
  refine ⟨fun ω F G => 2 * TetherKernelVel kappa ω F G, fun ω F G => by
    simp only [tetherKernelVel_comm ω F G], fun g F G ω => by
    simp [CoadjointAction], fun F ω => by simp only [hC2 F ω, mul_zero], fun F ω => ?_,
    ω₀, F₀, F₀, fun h => hF₀ (by linarith)⟩
  have h := tetherKernelVel_diag_nonpos hκ F ω
  have := tetherKernelVel_quadratic_form (kappa := kappa) F ω
  show 2 * _ ≤ _
  linarith

/-- The C2 + C1–C3 non-uniqueness with C2 discharged from its hypotheses. -/
theorem c1_c3_not_unique_vel_of_curl (hκ : 0 < kappa)
    (hcurl : ∀ ω, KineticEnergyCurlIdentity ω)
    (hInt : ∀ ω, Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) NavierStokes3D.volume)
    (hne : ∃ ω F, TetherKernelVel kappa ω F F ≠ 0) :
    ∃ B : CoadjointOrbit → Functional → Functional → ℝ,
      (∀ ω F G, B ω F G = B ω G F) ∧ InvariantUnderCoadjointAction B ∧
      DegenerateWRTKineticEnergy B ∧ ProducesControllableNegativeFeedbackVel kappa B ∧
      ∃ ω F G, B ω F G ≠ TetherKernelVel kappa ω F G :=
  c1_c3_not_unique_vel hκ (tetherKernelVel_degenerate hcurl hInt) hne

/-! ## Degree 2 and Step 5 -/

theorem velSlot_scale (ω : CoadjointOrbit) (c : ℝ) (hc : c ≠ 0) (F : Functional)
    (hFD : FunctionalDerivative F (scaleOrbit c ω) = FunctionalDerivative F ω) :
    velSlot (scaleOrbit c ω) F = velSlot ω F := by
  unfold velSlot
  rw [hFD]
  have := hPi_of_ne_zero ω c hc
  simp only [scaleOrbit] at *
  rw [this]

/-- **Degree 2.** `TetherKernelVel (cω) = c² TetherKernelVel ω` when `δF, δG` are scale invariant. -/
theorem step2_degree_vel (F G : Functional) (ω : CoadjointOrbit) (c : ℝ) (hc : c ≠ 0)
    (hF : FunctionalDerivative F (scaleOrbit c ω) = FunctionalDerivative F ω)
    (hG : FunctionalDerivative G (scaleOrbit c ω) = FunctionalDerivative G ω) :
    TetherKernelVel kappa (scaleOrbit c ω) F G = c ^ 2 * TetherKernelVel kappa ω F G := by
  rw [tetherKernelVel_eq, tetherKernelVel_eq, velSlot_scale ω c hc F hF,
    velSlot_scale ω c hc G hG]
  have : (fun x => ‖(scaleOrbit c ω).val x‖ ^ 2 * inner ℝ (velSlot ω F x) (velSlot ω G x)) =
      fun x => c ^ 2 * (‖ω.val x‖ ^ 2 * inner ℝ (velSlot ω F x) (velSlot ω G x)) := by
    funext x
    simp only [scaleOrbit, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [this, integral_const_mul]
  ring

/-- **Step 5.** A degree `n ≥ 3` remainder of a degree-2 correction around `TetherKernelVel`
vanishes. -/
theorem step5_tetherKernelVel (F G : Functional) (c : ℝ) (hc : 1 < |c|)
    (hF : ∀ ω, FunctionalDerivative F (scaleOrbit c ω) = FunctionalDerivative F ω)
    (hG : ∀ ω, FunctionalDerivative G (scaleOrbit c ω) = FunctionalDerivative G ω)
    (B R : CoadjointOrbit → ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hsum : ∀ ω, B ω = TetherKernelVel kappa ω F G + R ω)
    (hB : ∀ ω, B (scaleOrbit c ω) = c ^ 2 * B ω)
    (hR : ∀ ω, R (scaleOrbit c ω) = c ^ n * R ω) :
    ∀ ω, B ω = TetherKernelVel kappa ω F G := by
  have hc0 : c ≠ 0 := by intro h; rw [h, abs_zero] at hc; linarith
  have hR0 := step5_higher_order_vanishes (scaleOrbit c) c hc B
    (fun ω => TetherKernelVel kappa ω F G) R n hn hsum hB
    (fun ω => step2_degree_vel F G ω c hc0 (hF ω) (hG ω)) hR
  intro ω; rw [hsum, hR0, add_zero]

/-! ## Metriplectic split -/

/-- Velocity-slot metriplectic pairing: KKS form plus `TetherKernelVel`. -/
noncomputable def MetriplecticPairingVel (kappa : ℝ) (ω : CoadjointOrbit) (F G : Functional) : ℝ :=
  kksSymplecticForm ω (FunctionalDerivative F ω) (FunctionalDerivative G ω) +
    TetherKernelVel kappa ω F G

theorem metriplecticPairingVel_diag (hκ : 0 < kappa) (ω : CoadjointOrbit) (F : Functional) :
    MetriplecticPairingVel kappa ω F F = TetherKernelVel kappa ω F F ∧
      TetherKernelVel kappa ω F F ≤ 0 :=
  ⟨by simp [MetriplecticPairingVel, kksSymplecticForm_self_zero],
    tetherKernelVel_diag_nonpos hκ F ω⟩

/-- Tethered bracket with the velocity-slot tether. -/
noncomputable def TetheredBracketVel (kappa : ℝ) (F G : Functional) (ω : CoadjointOrbit) : ℝ :=
  ClassicalBracket F G ω + TetherKernelVel kappa ω F G

/-- On the energy Hamiltonian the velocity-slot bracket is the classical Euler bracket. -/
theorem tetheredBracketVel_energy (F : Functional) (ω : CoadjointOrbit)
    (hcurl : KineticEnergyCurlIdentity ω)
    (hInt : Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) NavierStokes3D.volume) :
    TetheredBracketVel kappa F KineticEnergyHamiltonian ω =
      ClassicalBracket F KineticEnergyHamiltonian ω := by
  simp [TetheredBracketVel, tetherKernelVel_C2_at F ω hcurl hInt]

/-! ## Product theorem -/

/-- `P1` for the velocity slot: uniqueness, degree 2, Step 5. -/
def P1Vel (kappa : ℝ) : Prop :=
  (∀ B : CoadjointOrbit → Functional → Functional → ℝ,
    ProducesControllableNegativeFeedbackVel kappa B → FeedbackAtMostVel kappa B →
    Polarizes B → Polarizes (TetherKernelVel kappa) →
    ∀ ω F G, B ω F G = TetherKernelVel kappa ω F G) ∧
  (∀ (F G : Functional) (ω : CoadjointOrbit) (c : ℝ), c ≠ 0 →
    FunctionalDerivative F (scaleOrbit c ω) = FunctionalDerivative F ω →
    FunctionalDerivative G (scaleOrbit c ω) = FunctionalDerivative G ω →
    TetherKernelVel kappa (scaleOrbit c ω) F G = c ^ 2 * TetherKernelVel kappa ω F G) ∧
  (∀ (F G : Functional) (c : ℝ), 1 < |c| →
    (∀ ω, FunctionalDerivative F (scaleOrbit c ω) = FunctionalDerivative F ω) →
    (∀ ω, FunctionalDerivative G (scaleOrbit c ω) = FunctionalDerivative G ω) →
    ∀ (B R : CoadjointOrbit → ℝ) (n : ℕ), 3 ≤ n →
    (∀ ω, B ω = TetherKernelVel kappa ω F G + R ω) →
    (∀ ω, B (scaleOrbit c ω) = c ^ 2 * B ω) →
    (∀ ω, R (scaleOrbit c ω) = c ^ n * R ω) →
    ∀ ω, B ω = TetherKernelVel kappa ω F G)

/-- `P2` for the velocity slot: KKS skew and Jacobi, diagonal = tether ≤ 0, C2 / classical
Euler on `H`, Beltrami projection, strict pointwise damping. -/
def P2Vel (kappa : ℝ) : Prop :=
  (∀ (ω : CoadjointOrbit) (ξ₁ ξ₂ : VelocityField),
    kksSymplecticForm ω ξ₁ ξ₂ = -kksSymplecticForm ω ξ₂ ξ₁) ∧
  (∀ (ω : CoadjointOrbit) (ξ₁ ξ₂ ξ₃ : VelocityField) (x : T3),
    pairing (ω.val x) (cross (ξ₁ x) (cross (ξ₂ x) (ξ₃ x))) +
    pairing (ω.val x) (cross (ξ₂ x) (cross (ξ₃ x) (ξ₁ x))) +
    pairing (ω.val x) (cross (ξ₃ x) (cross (ξ₁ x) (ξ₂ x))) = 0) ∧
  (∀ ω F, MetriplecticPairingVel kappa ω F F = TetherKernelVel kappa ω F F ∧
    TetherKernelVel kappa ω F F ≤ 0) ∧
  (∀ F ω, KineticEnergyCurlIdentity ω →
    Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) NavierStokes3D.volume →
    TetheredBracketVel kappa F KineticEnergyHamiltonian ω =
      ClassicalBracket F KineticEnergyHamiltonian ω) ∧
  (∀ (u : VelocityField) (lam : ℝ), (∫ y, ‖u y‖ ^ 2 ∂NavierStokes3D.volume) ≠ 0 →
    Pi_u u (fun x => lam • u x) = 0) ∧
  (∀ ω F x, ω.val x ≠ 0 → velSlot ω F x ≠ 0 → velPointwiseDensity kappa ω F x < 0)

/-- **Product theorem for the velocity-slot tether.** -/
theorem velocity_tether_product_theorem (hκ : 0 < kappa) :
    P1Vel kappa ∧ P2Vel kappa ∧ P3_QuarticYoungAbsorption kappa ∧
      P4_UnconditionalLyapunovCeiling := by
  obtain ⟨-, -, hP3, hP4⟩ :=
    frohmanian_metriplectic_system_canonical_uniqueness_and_global_regularity_product_theorem hκ
  refine ⟨⟨uniqueness_vel, fun F G ω c hc hF hG => step2_degree_vel F G ω c hc hF hG,
      fun F G c hc hF hG B R n hn => step5_tetherKernelVel F G c hc hF hG B R n hn⟩,
    ⟨kksSymplecticForm_skew, kksPointwise_cyclic_jacobi_identity,
      metriplecticPairingVel_diag hκ, fun F ω => tetheredBracketVel_energy F ω,
      beltrami_casimir_projection_zero, fun ω F x => velPointwiseDensity_strict_neg hκ ω F x⟩,
    hP3, hP4⟩

end FrohmanianTether
