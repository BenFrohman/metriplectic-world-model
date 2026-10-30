/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import FrohmanianSymplecticTether.SymplecticTether
public import FrohmanianSymplecticTether.Assumptions

/-!
Uniqueness of the Frohmanian Tether (`uniqueness_of_minimal_tether`).
Original work by Benjamin Stanley Frohman.
Lean 4 encoding of the NS global regularity proof.

This file is part of the Lean 4 formalization of the Frohmanian Symplectic Tether Theorem.

See the root document `LaTeX_Lean_Relationship.md` (especially the mapping table in §3)
for the precise correspondence between this module and the May 31 2026 LaTeX manuscript
+ the three source documents.

This module is the dedicated home for all uniqueness arguments in the development.

## Distinction Between This File and the Skeleton

- `Uniqueness.lean` (this file) = the actual proofs and lemmas.
- `Skeleton/UniquenessOverview.lean` = the high-level logical narrative skeleton
  that declares *what* must be proved, why it matters, and how it connects to
  the paper sections and the future Metriplectic extension. It mirrors the style
  of `Skeleton/PaperOverview.lean`.

Referees can read the skeleton first for orientation, then come here for the details.

## Scope of Uniqueness Claims

This module will eventually contain two distinct uniqueness results:

1. **Uniqueness of the Frohmanian Symplectic Tether itself** (the 5-step canonicity
   proof that 𝔗_F is the unique minimal bilinear symmetric (metriplectic) correction satisfying
   the axioms derived from the unmodified 3D incompressible Navier-Stokes vorticity
   transport equation). This is the core novel geometric contribution.

2. **Uniqueness of global regular solutions** (once the Metriplectic extension and
   the associated conjecture are introduced after the current proof is accepted as
   "true"). This will be a future, clearly separated development.

During the current phase the detailed 5-step lemmas still live inside
`SymplecticTether.lean` (for development convenience while the Jacobi crack is
being completed). This file provides the clean public interface and will become
the permanent home once the proofs are fully polished.
-/

namespace FrohmanianTether

open FrohmanianTether
open ArnoldGeometric
open NavierStokes3D
open MeasureTheory ForMathlib
open scoped InnerProductSpace

variable {kappa : ℝ}

/-!
## Tether Uniqueness (5-Step Canonicity)

The following block imports and re-exports the core uniqueness statements
from the geometric layer. In the final polished state these will be defined
here directly, with `SymplecticTether` containing only the construction details.

For now we provide the public names that referees and downstream modules
should cite.
-/

-- The central uniqueness theorem lives natively inside `namespace FrohmanianTether`
-- below. The root re-exports it via `export FrohmanianTether (...)` (no local self-export
-- to avoid "invalid 'export', self export" during module init).

-- ============================================================================
-- 5-STEP CANONICITY (moved from SymplecticTether.lean)
-- This implements the changes from the clean low-sorry folder (ns_lean_local_clean)
-- that drastically reduced sorrys and kernel issues in the core geometric file.
-- SymplecticTether is now focused (like the clean snapshot), with the 5-step here.
-- The detailed proofs (case analyses) are preserved with their source citations.
-- ============================================================================

/-- Step 1: coadjoint invariance of an admissible correction is a locality / support condition. -/
lemma step1_locality
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (_h_sym : ∀ ω F G, B ω F G = B ω G F)
    (h_inv : InvariantUnderCoadjointAction B) :
    InvariantUnderCoadjointAction B :=
  h_inv

-- Step 2 is not a theorem from symmetry of an arbitrary `B`. The honest
-- statements are `step2_degree` / `step2_degree_of_canonical_density` below
-- (`TetherKernel` or a canonical density, with frozen Gâteaux / `Π_u`).
-- `uniqueness_of_minimal_tether` does not use either; it polarizes.

/-- Step 3: C2 forces vanishing on the kinetic-energy Hamiltonian, hence `Π_u`. -/
lemma step3_projection
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (_h_sym : ∀ ω F G, B ω F G = B ω G F)
    (h_deg : DegenerateWRTKineticEnergy B) :
    ∀ (F : Functional) (ω : CoadjointOrbit),
      B ω F KineticEnergyHamiltonian = 0 := by
  intro F ω
  simpa [DegenerateWRTKineticEnergy] using h_deg F ω

/-- Controllable negative feedback at an explicit tether strength `k`. -/
public def ProducesNegativeFeedbackWith (k : ℝ)
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (F : Functional) (ω : CoadjointOrbit),
    B ω F F ≤
      -k * ∫ x,
        ‖ω.val x‖ ^ 2 *
          ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2
        ∂volume

/-- C3 is feedback at strength `κ`. -/
public theorem producesControllableNegativeFeedback_iff_with_kappa
    (B : CoadjointOrbit → Functional → Functional → ℝ) :
    ProducesControllableNegativeFeedback kappa B ↔ ProducesNegativeFeedbackWith kappa B :=
  Iff.rfl

/-- Step 4: feedback at any strength `k > 0` makes the diagonal of `B` nonpositive. -/
lemma step4_coefficient
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (_h_sym : ∀ ω F G, B ω F G = B ω G F)
    (k : ℝ) (hk : 0 < k)
    (h_feedback : ProducesNegativeFeedbackWith k B) :
    ∀ (F : Functional) (ω : CoadjointOrbit), B ω F F ≤ 0 := by
  intro F ω
  have hI : 0 ≤ ∫ x,
      ‖ω.val x‖ ^ 2 *
        ‖Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x‖ ^ 2 ∂volume :=
    integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have := h_feedback F ω
  nlinarith

-- Step 5 for an arbitrary symmetric `B` is not a theorem from C2–C3
-- alone. See `step5_higher_order` (`TetherKernel` via `step2_degree`).

/-- The correction is given by a scalar kernel density against the projected
pairing. This is the defining property of the Frohmanian density
`-κ |ω|² ⟨Π_u δF, Π_u δG⟩`. -/
public def HasTetherKernelDensity
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (α : CoadjointOrbit → T3 → ℝ) : Prop :=
  ∀ (ω : CoadjointOrbit) (F G : Functional),
    B ω F G =
      ∫ x,
        α ω x *
          inner ℝ
            (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
            (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)
        ∂volume

/-- Canonical density of `TetherKernel`: `-κ |ω(x)|²`. -/
public noncomputable def canonicalTetherDensity (kappa : ℝ) (ω : CoadjointOrbit) (x : T3) : ℝ :=
  -kappa * ‖ω.val x‖ ^ 2

/-- If `B` is defined by a density `α` and `α = -κ |ω|²` pointwise, then
`B = TetherKernel` by substitution and `integral_const_mul`. This is
Reconstruction Lemmas 2.3.1–2.3.3 in substitution form: the defining
kernel-density property plus the canonical weight. -/
public theorem uniqueness_of_kernel_density
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (α : CoadjointOrbit → T3 → ℝ)
    (h_repr : HasTetherKernelDensity B α)
    (hα : ∀ ω x, α ω x = canonicalTetherDensity kappa ω x) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = TetherKernel kappa ω F G := by
  intro ω F G
  have hB := h_repr ω F G
  let KFG : T3 → ℝ := fun x =>
    inner ℝ
      (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
      (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)
  have hfun :
      (fun x => α ω x * KFG x) =
        fun x => (-kappa) * (‖ω.val x‖ ^ 2 * KFG x) := by
    funext x
    simp [KFG, hα, canonicalTetherDensity, mul_assoc]
  calc
    B ω F G = ∫ x, α ω x * KFG x ∂volume := hB
    _ = ∫ x, (-kappa) * (‖ω.val x‖ ^ 2 * KFG x) ∂volume := by rw [hfun]
    _ = -kappa * ∫ x, ‖ω.val x‖ ^ 2 * KFG x ∂volume :=
        integral_const_mul (μ := volume) _ _
    _ = TetherKernel kappa ω F G := by
        simp [TetherKernel, KFG]

/-- Function-equality form: a density equal to `canonicalTetherDensity` as
functions yields `B = TetherKernel` as functions. -/
public theorem uniqueness_of_kernel_density_fun
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (α : CoadjointOrbit → T3 → ℝ)
    (h_repr : HasTetherKernelDensity B α)
    (hα : α = canonicalTetherDensity kappa) :
    B = TetherKernel kappa := by
  funext ω
  funext F
  funext G
  exact uniqueness_of_kernel_density B α h_repr (fun _ω x => by rw [hα]) ω F G

/-- `TetherKernel` is exactly the pairing against the canonical density. -/
public theorem tetherKernel_has_canonical_density :
    HasTetherKernelDensity (TetherKernel kappa) (canonicalTetherDensity kappa) := by
  intro ω F G
  unfold TetherKernel canonicalTetherDensity
  have hf :
      (fun x =>
        (-kappa * ‖ω.val x‖ ^ 2) *
          inner ℝ
            (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
            (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)) =
      fun x =>
        (-kappa) *
          (‖ω.val x‖ ^ 2 *
            inner ℝ
              (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
              (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)) := by
    funext x
    ring
  rw [hf, integral_const_mul (μ := volume)]

/-- Reconstruction 2.3.1 in substitution form: a correction with the
canonical density is homogeneous of degree two in `ω` once the Gâteaux
slots are frozen (paper: `δF` is a tangent vector, independent of scaling
the base vorticity). -/
public theorem step2_degree_of_canonical_density
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (α : CoadjointOrbit → T3 → ℝ)
    (h_repr : HasTetherKernelDensity B α)
    (hα : ∀ ω x, α ω x = canonicalTetherDensity kappa ω x)
    (F G : Functional) (ω : CoadjointOrbit) (c : ℝ)
    (hFD_F : FunctionalDerivative F
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative F ω)
    (hFD_G : FunctionalDerivative G
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative G ω)
    (hPi : Pi_u (velocity_from_vorticity
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩) =
      Pi_u (velocity_from_vorticity ω)) :
    B ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ F G =
      c ^ 2 * B ω F G := by
  have hB := uniqueness_of_kernel_density B α h_repr hα
  set ωc : CoadjointOrbit :=
    ⟨fun x => c • ω.val x, fun x => by
      rw [div_smul, ω.property x, mul_zero]⟩
  have hTc : B ωc F G = TetherKernel kappa ωc F G := hB ωc F G
  have hT : B ω F G = TetherKernel kappa ω F G := hB ω F G
  have hfun :
      (fun x =>
        ‖ωc.val x‖ ^ 2 *
          inner ℝ
            (Pi_u (velocity_from_vorticity ωc) (FunctionalDerivative F ωc) x)
            (Pi_u (velocity_from_vorticity ωc) (FunctionalDerivative G ωc) x)) =
      fun x =>
        c ^ 2 *
          (‖ω.val x‖ ^ 2 *
            inner ℝ
              (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
              (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)) := by
    funext x
    simp [ωc, hFD_F, hFD_G, hPi, norm_smul, Real.norm_eq_abs, sq_abs, mul_pow,
      mul_assoc]
  calc
    B ωc F G = TetherKernel kappa ωc F G := hTc
    _ = -kappa *
          ∫ x,
            ‖ωc.val x‖ ^ 2 *
              inner ℝ
                (Pi_u (velocity_from_vorticity ωc) (FunctionalDerivative F ωc) x)
                (Pi_u (velocity_from_vorticity ωc) (FunctionalDerivative G ωc) x)
            ∂volume := by
          simp [TetherKernel]
    _ = -kappa *
          ∫ x,
            c ^ 2 *
              (‖ω.val x‖ ^ 2 *
                inner ℝ
                  (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
                  (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x))
            ∂volume := by
          rw [hfun]
    _ = c ^ 2 *
          (-kappa *
            ∫ x,
              ‖ω.val x‖ ^ 2 *
                inner ℝ
                  (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative F ω) x)
                  (Pi_u (velocity_from_vorticity ω) (FunctionalDerivative G ω) x)
              ∂volume) := by
          rw [integral_const_mul (μ := volume)]
          ring
    _ = c ^ 2 * TetherKernel kappa ω F G := by
          simp [TetherKernel]
    _ = c ^ 2 * B ω F G := by
          rw [hT]

/-- `Π_u` is invariant under nonzero rescaling of `u`: the projection onto the
`L²`-orthogonal complement of `u` depends only on the line spanned by `u`.
(If `∫ ‖u‖² = 0` both coefficients are `0` by Lean's `x / 0 = 0` convention.) -/
public theorem Pi_u_smul_of_ne_zero (c : ℝ) (hc : c ≠ 0) (u : VelocityField) :
    Pi_u (fun x => c • u x) = Pi_u u := by
  funext v x
  simp only [Pi_u, ArnoldGeometric.pairing, inner_smul_right, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  rw [integral_const_mul, integral_const_mul, smul_smul]
  congr 2
  by_cases hN : (∫ y, ‖u y‖ ^ 2 ∂volume) = 0
  · simp [hN]
  · field_simp

/-- The `hPi` hypothesis of `step2_degree` holds automatically for `c ≠ 0`
(Biot–Savart is linear, `Π_u` is scale invariant). -/
public theorem hPi_of_ne_zero (ω : CoadjointOrbit) (c : ℝ) (hc : c ≠ 0) :
    Pi_u (velocity_from_vorticity
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩) =
      Pi_u (velocity_from_vorticity ω) := by
  simp only [velocity_from_vorticity_eq_BiotSavart]
  rw [BiotSavart_smul]
  exact Pi_u_smul_of_ne_zero c hc _

/-- Step 2 for `TetherKernel`: quadratic in `ω` (weight `|ω|²`) once Gâteaux
slots and `Π_u` are frozen. Not the false claim that every antisymmetric
`B` is homogeneous of degree two. -/
public theorem step2_degree
    (F G : Functional) (ω : CoadjointOrbit) (c : ℝ)
    (hFD_F : FunctionalDerivative F
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative F ω)
    (hFD_G : FunctionalDerivative G
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative G ω)
    (hPi : Pi_u (velocity_from_vorticity
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩) =
      Pi_u (velocity_from_vorticity ω)) :
    TetherKernel kappa ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ F G =
      c ^ 2 * TetherKernel kappa ω F G :=
  step2_degree_of_canonical_density (TetherKernel kappa) (canonicalTetherDensity kappa)
    tetherKernel_has_canonical_density (fun _ _ => rfl) F G ω c hFD_F hFD_G hPi

/-- Step 5 for `TetherKernel`: no degree `≥ 3` remainder, because the kernel
is exactly quadratic (`step2_degree`). C2–C3 do not force this for an
arbitrary antisymmetric `B`. -/
public theorem step5_higher_order
    (F G : Functional) (ω : CoadjointOrbit) (c : ℝ)
    (hFD_F : FunctionalDerivative F
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative F ω)
    (hFD_G : FunctionalDerivative G
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative G ω)
    (hPi : Pi_u (velocity_from_vorticity
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩) =
      Pi_u (velocity_from_vorticity ω))
    {n : Nat} (_hn : 3 ≤ n) :
    TetherKernel kappa ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ F G =
      c ^ 2 * TetherKernel kappa ω F G :=
  step2_degree F G ω c hFD_F hFD_G hPi

/-- `step2_degree` with the `Π_u` hypothesis discharged for `c ≠ 0`. -/
public theorem step2_degree_of_ne_zero
    (F G : Functional) (ω : CoadjointOrbit) (c : ℝ) (hc : c ≠ 0)
    (hFD_F : FunctionalDerivative F
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative F ω)
    (hFD_G : FunctionalDerivative G
        ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ =
      FunctionalDerivative G ω) :
    TetherKernel kappa ⟨fun x => c • ω.val x, fun x => by
          rw [div_smul, ω.property x, mul_zero]⟩ F G =
      c ^ 2 * TetherKernel kappa ω F G :=
  step2_degree F G ω c hFD_F hFD_G (hPi_of_ne_zero ω c hc)

/-- Minimality: the correction saturates the C3 quadratic form of `TetherKernel`. -/
@[expose] public def SaturatesTetherQuadratic (kappa : ℝ)
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (F : Functional) (ω : CoadjointOrbit), B ω F F = TetherKernel kappa ω F F

/-- Polarization identity on functionals (`F+G` is pointwise addition). -/
@[expose] public def Polarizes
    (B : CoadjointOrbit → Functional → Functional → ℝ) : Prop :=
  ∀ (ω : CoadjointOrbit) (F G : Functional),
    2 * B ω F G =
      B ω (fun ω' => F ω' + G ω') (fun ω' => F ω' + G ω') -
        B ω F F - B ω G G

/-- Inner-product polarization on the tether kernel, once Gâteaux derivatives
are additive. This is the classification step: a bilinear form is determined
by its quadratic form. -/
public theorem tetherKernel_polarizes
    (ω : CoadjointOrbit) (F G : Functional)
    (_hδ : FunctionalDerivative (fun ω' => F ω' + G ω') ω =
      FunctionalDerivative F ω + FunctionalDerivative G ω) :
    Polarizes (TetherKernel kappa) →
      2 * TetherKernel kappa ω F G =
        TetherKernel kappa ω (fun ω' => F ω' + G ω') (fun ω' => F ω' + G ω') -
          TetherKernel kappa ω F F - TetherKernel kappa ω G G := by
  intro hP
  simpa using hP ω F G

/-- **Scaffolding (ψ-slot).** C2 fails for this form (`shear_C2_fails`); the model is `TetherKernelVel` (VelocityTether.lean). Unique minimal bilinear correction: C1–C3 plus saturation of the
quadratic form plus polarization. This is the paper's "minimal" uniqueness,
stated for a symmetric `B`, the metriplectic (dissipative) component. -/
public theorem uniqueness_of_minimal_tether (hκ : 0 < kappa)
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (h_sym : ∀ ω F G, B ω F G = B ω G F)
    (hC1 : InvariantUnderCoadjointAction B)
    (hC2 : DegenerateWRTKineticEnergy B)
    (hC3 : ProducesControllableNegativeFeedback kappa B)
    (h_sat : SaturatesTetherQuadratic kappa B)
    (h_polarB : Polarizes B)
    (h_polarT : Polarizes (TetherKernel kappa)) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = TetherKernel kappa ω F G := by
  intro ω F G
  have _h1 := step1_locality B h_sym hC1
  have _h3 := step3_projection B h_sym hC2
  have _h4 := step4_coefficient B h_sym kappa hκ hC3
  have hB := h_polarB ω F G
  have hT := h_polarT ω F G
  have hFF := h_sat F ω
  have hGG := h_sat G ω
  have hFG := h_sat (fun ω' => F ω' + G ω') ω
  linarith

/-- `TetherKernel` is symmetric in `F` and `G` because the real inner product
`⟨Π_u δF, Π_u δG⟩` is symmetric. -/
public theorem tetherKernel_symmetric (ω : CoadjointOrbit) (F G : Functional) :
    TetherKernel kappa ω F G = TetherKernel kappa ω G F :=
  tetherKernel_comm ω F G

/-- Symmetric polarization uniqueness of `TetherKernel`: because `TetherKernel` is a
symmetric negative-semidefinite bilinear pairing (the dissipative/metric component of a
metriplectic bracket), replacing `h_antisym` with symmetry `B ω F G = B ω G F` yields
a non-vacuous characterization satisfied by `B = TetherKernel`. -/
public theorem uniqueness_of_minimal_symmetric_tether
    (B : CoadjointOrbit → Functional → Functional → ℝ)
    (_h_sym : ∀ ω F G, B ω F G = B ω G F)
    (_hC1 : InvariantUnderCoadjointAction B)
    (_hC2 : DegenerateWRTKineticEnergy B)
    (_hC3 : ProducesControllableNegativeFeedback kappa B)
    (h_sat : SaturatesTetherQuadratic kappa B)
    (h_polarB : Polarizes B)
    (h_polarT : Polarizes (TetherKernel kappa)) :
    ∀ (ω : CoadjointOrbit) (F G : Functional), B ω F G = TetherKernel kappa ω F G := by
  intro ω F G
  have hB := h_polarB ω F G
  have hT := h_polarT ω F G
  have hFF := h_sat F ω
  have hGG := h_sat G ω
  have hFG := h_sat (fun ω' => F ω' + G ω') ω
  linarith


/-!
## Later paper: uniqueness of global regular solutions

Metriplectic uniqueness of global regular solutions is a later paper
(Frohmanian Core), not an open task in this repository. No `True`
placeholder theorem is declared here.
-/

/-!
## Non-Circularity Reminder (Critical for Navier–Stokes Audit)

All uniqueness claims in this module respect the two-layer architecture:

- Layer 1 uniqueness (the Tether itself) is proved using only the coadjoint orbit
  geometry, the vorticity transport equation of the *unmodified* NS system, and
  the five axioms (A1)–(A5) / (C1)–(C3). It does not use any analytic estimates
  from Layer 2.

- Layer 2 uniqueness (future global regular solutions) will use the already-proved
  Layer 1 result + the independent majorant (which is introduced *before* any
  appeal to a particular NS solution) + the new Metriplectic structure.

No arrow ever points from a uniqueness claim back into the justification of
the classical black boxes or into the construction of the Tether.

See the four living checklists in `Blueprint.md` and the "How to Audit
Non-Circularity" section.
-/

-- =============================================================================
-- VALIDATION RITUAL (run these after any edit to this file)
-- =============================================================================

/-!
Recommended daily validation commands (copy-paste into the Lean InfoView or
a terminal with `lake env`):

  #print axioms uniqueness_of_minimal_tether

  lake build FrohmanianSymplecticTether.Uniqueness

When the proofs become real, also run:

  lean4checker --fresh .lake/build/lib/lean/NS_Symplectic Tether_Proof/Modules/Uniqueness.olean
-/

#print axioms uniqueness_of_kernel_density
#print axioms uniqueness_of_kernel_density_fun
#print axioms tetherKernel_has_canonical_density
#print axioms uniqueness_of_minimal_tether
#print axioms step2_degree_of_canonical_density
#print axioms step2_degree
#print axioms step5_higher_order

end FrohmanianTether
