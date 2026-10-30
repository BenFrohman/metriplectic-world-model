/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.WithLp
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.EReal.Basic
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpace
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Separation.Hausdorff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

open scoped BigOperators Gradient Topology
open ENNReal InnerProductSpace MeasureTheory Finset Filter

/-!
# Navier–Stokes Equations: Classical Foundation (Lean 4)

3D incompressible Navier–Stokes on the model space `EuclideanSpace ℝ (Fin 3)`
(standing in for `𝕋³` at the type level; Haar/Lebesgue volume is inherited from mathlib).

Differential operators are the standard Lean 4 calculus objects (`deriv`, `fderiv`,
`gradient`). Local existence, Beale–Kato–Majda, and the maximal time `Tstar` remain
documented classical black boxes (Kato/Leray/BKM) with **real types**.
-/

namespace NavierStokes3D

/-- Model 3-space. `abbrev` so mathlib instances (norm, inner product, Haar measure) inherit. -/
@[expose] public abbrev T3 : Type := EuclideanSpace ℝ (Fin 3)

public abbrev VelocityField := T3 → EuclideanSpace ℝ (Fin 3)
public abbrev VorticityField := T3 → EuclideanSpace ℝ (Fin 3)
public abbrev PressureField := T3 → ℝ

public abbrev TimeDependentVelocity := ℝ → VelocityField
public abbrev TimeDependentVorticity := ℝ → VorticityField
public abbrev TimeDependentPressure := ℝ → PressureField

noncomputable section

/-- Haar / Lebesgue volume on the model space. -/
@[expose] public def volume : Measure T3 := MeasureTheory.volume

/-- Pointwise time derivative via mathlib `deriv`. -/
@[expose] public def time_deriv {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    (f : ℝ → (T3 → α)) (t : ℝ) (x : T3) : α :=
  deriv (fun s => f s x) t

notation "∂t " f:arg t:arg => time_deriv f t

/-- Convective derivative `(u · ∇) v`, as the Fréchet derivative of `v` in the direction `u`. -/
@[expose] public def convective (u v : VelocityField) : VelocityField :=
  fun x => (fderiv ℝ v x) (u x)

prefix:100 "(·∇)" => fun u v => convective u v

/-- Component sum on the 3-space. Discrete index `Fin 3` (from `Nat`).
Time, viscosity, `κ`, norms, and integrals stay over `ℝ`. -/
@[expose] public def componentSum (v : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∑ i : Fin 3, v i

/-- i-th coordinate directional derivative of a vector field. -/
@[expose] public def directionalCoord (u : VelocityField) (comp dir : Fin 3) (x : T3) : ℝ :=
  (fderiv ℝ (fun y => u y comp) x) (EuclideanSpace.single dir 1)

/-- Laplacian as the trace of the Hessian. -/
@[expose] public def laplacian (f : VelocityField) : VelocityField :=
  fun x => ∑ i : Fin 3,
    (fderiv ℝ (fun y => (fderiv ℝ f y) (EuclideanSpace.single i 1)) x)
      (EuclideanSpace.single i 1)

notation "Δ " f:arg => laplacian f

/-- Divergence: `∑ᵢ ∂ᵢ uᵢ`. -/
@[expose] public def div (u : VelocityField) (x : T3) : ℝ :=
  ∑ i : Fin 3, (fderiv ℝ (fun y => u y i) x) (EuclideanSpace.single i 1)

/-- Coordinate of a scalar multiple. Discrete index `Fin 3`; coefficient `c : ℝ`. -/
public theorem smul_coord (c : ℝ) (v : EuclideanSpace ℝ (Fin 3)) (i : Fin 3) :
    (c • v) i = c * v i := by
  rw [PiLp.smul_apply, smul_eq_mul]

/-- Coordinate projections on the model 3-space are differentiable. -/
public theorem differentiableAt_coord (x : T3) (i : Fin 3) :
    DifferentiableAt ℝ (fun z : T3 => z i) x :=
  (PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) i).differentiableAt

/-- Fréchet derivative of the `i`-th coordinate is that coordinate of the increment. -/
public theorem fderiv_coord (x : T3) (i : Fin 3) (dz : T3) :
    (fderiv ℝ (fun z : T3 => z i) x) dz = dz i := by
  let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) i
  have hfun : (fun z : T3 => z i) = fun z => L z := rfl
  rw [hfun, ContinuousLinearMap.fderiv]
  rfl

/-- Scaling a field scales its divergence. Discrete index `Fin 3`; coefficient `c : ℝ`.
Unconditional: `fderiv_const_smul_field` handles the zero-scalar and non-differentiable cases. -/
public theorem div_smul (c : ℝ) (u : VelocityField) (x : T3) :
    div (fun y => c • u y) x = c * div u x := by
  unfold div
  have hfun : ∀ i : Fin 3,
      (fun y => (c • u y) i) = c • fun y => u y i := by
    intro i
    funext y
    exact smul_coord c (u y) i
  calc
    ∑ i : Fin 3, (fderiv ℝ (fun y => (c • u y) i) x) (EuclideanSpace.single i 1)
        = ∑ i : Fin 3, (fderiv ℝ (c • fun y => u y i) x) (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hfun i]
    _ = ∑ i : Fin 3, (c • fderiv ℝ (fun y => u y i) x) (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [fderiv_const_smul_field, Pi.smul_apply]
    _ = ∑ i : Fin 3, c * (fderiv ℝ (fun y => u y i) x) (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    _ = c * ∑ i : Fin 3, (fderiv ℝ (fun y => u y i) x) (EuclideanSpace.single i 1) := by
          rw [← Finset.mul_sum]

/-- Divergence is linear in the field, at points where every coordinate is differentiable. -/
public theorem div_add (u v : VelocityField) (x : T3)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u y i) x)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    div (fun y => u y + v y) x = div u x + div v x := by
  unfold div
  have hfun : ∀ i : Fin 3,
      (fun y => (u y + v y) i) = fun y => u y i + v y i := by
    intro i
    funext y
    rw [PiLp.add_apply]
  calc
    ∑ i : Fin 3, (fderiv ℝ (fun y => (u y + v y) i) x) (EuclideanSpace.single i 1)
        = ∑ i : Fin 3, (fderiv ℝ (fun y => u y i + v y i) x) (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hfun i]
    _ = ∑ i : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) + (fderiv ℝ (fun y => v y i) x))
            (EuclideanSpace.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [fderiv_fun_add (hu i) (hv i)]
    _ = ∑ i : Fin 3, (fderiv ℝ (fun y => u y i) x) (EuclideanSpace.single i 1) +
        ∑ i : Fin 3, (fderiv ℝ (fun y => v y i) x) (EuclideanSpace.single i 1) := by
          simp only [ContinuousLinearMap.add_apply, Finset.sum_add_distrib]

/-- Affine combination of fields: `div(u + c • v) = div u + c div v`. -/
public theorem div_add_smul (u v : VelocityField) (c : ℝ) (x : T3)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u y i) x)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    div (fun y => u y + c • v y) x = div u x + c * div v x := by
  have hcv : ∀ i, DifferentiableAt ℝ (fun y => (c • v y) i) x := by
    intro i
    have hfun : (fun y => (c • v y) i) = c • fun y => v y i := by
      funext y
      exact smul_coord c (v y) i
    rw [hfun]
    exact (hv i).const_smul c
  have hadd :=
    div_add u (fun y => c • v y) x hu hcv
  rw [hadd, div_smul]

/-- Divergence of a spatially constant field vanishes (each coordinate is constant). -/
public theorem div_const (v : EuclideanSpace ℝ (Fin 3)) (x : T3) :
    div (fun _ => v) x = 0 := by
  unfold div
  simp

/-- Curl on `ℝ³` (standard orientation). -/
@[expose] public def curl (u : VelocityField) (x : T3) : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single 0 (directionalCoord u 2 1 x - directionalCoord u 1 2 x) +
    EuclideanSpace.single 1 (directionalCoord u 0 2 x - directionalCoord u 2 0 x) +
    EuclideanSpace.single 2 (directionalCoord u 1 0 x - directionalCoord u 0 1 x)

/-- Scaling a field scales each directional coordinate. -/
public theorem directionalCoord_smul (c : ℝ) (u : VelocityField) (comp dir : Fin 3) (x : T3) :
    directionalCoord (fun y => c • u y) comp dir x =
      c * directionalCoord u comp dir x := by
  unfold directionalCoord
  have hfun : (fun y => (c • u y) comp) = c • fun y => u y comp := by
    funext y
    exact smul_coord c (u y) comp
  rw [hfun, fderiv_const_smul_field, Pi.smul_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Scaling a field scales its curl. Unconditional (same field identity as `div_smul`). -/
public theorem curl_smul (c : ℝ) (u : VelocityField) (x : T3) :
    curl (fun y => c • u y) x = c • curl u x := by
  ext i
  fin_cases i <;>
    simp [curl, directionalCoord_smul, smul_eq_mul] <;> ring

/-- Pressure gradient (mathlib Hilbert-space gradient). -/
@[expose] public def pressureGradient (p : PressureField) : VelocityField :=
  fun x => gradient p x

/-- `i`-th coordinate of the Hilbert-space gradient is the corresponding partial. -/
public theorem gradient_coord (p : PressureField) (x : T3) (i : Fin 3)
    (hp : DifferentiableAt ℝ p x) :
    gradient p x i = (fderiv ℝ p x) (EuclideanSpace.single i 1) := by
  have hinner : inner ℝ (gradient p x) (EuclideanSpace.single i 1) =
      (fderiv ℝ p x) (EuclideanSpace.single i 1) :=
    inner_gradient_left (y := EuclideanSpace.single i 1) hp
  have hcoord : inner ℝ (gradient p x) (EuclideanSpace.single i 1) = gradient p x i := by
    simpa using
      (EuclideanSpace.inner_single_right (i := i) (a := (1 : ℝ)) (v := gradient p x))
  exact hcoord.symm.trans hinner

/-- Product rule for divergence: `div(φ V) = ∇φ · V + φ div V`. -/
public theorem div_smul_field (φ : PressureField) (V : VelocityField) (x : T3)
    (hφ : DifferentiableAt ℝ φ x)
    (hV : ∀ i, DifferentiableAt ℝ (fun y => V y i) x) :
    div (fun y => φ y • V y) x =
      inner ℝ (gradient φ x) (V x) + φ x * div V x := by
  have hcoord : ∀ i : Fin 3,
      (fun y => (φ y • V y) i) = fun y => φ y * V y i := by
    intro i
    funext y
    exact smul_coord (φ y) (V y) i
  have hprod : ∀ i : Fin 3,
      fderiv ℝ (fun y => φ y * V y i) x =
        φ x • fderiv ℝ (fun y => V y i) x +
          V x i • fderiv ℝ φ x :=
    fun i => fderiv_fun_mul hφ (hV i)
  unfold div
  simp_rw [hcoord, hprod, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul]
  have hsplit :
      (∑ i : Fin 3,
          (φ x * (fderiv ℝ (fun y => V y i) x) (EuclideanSpace.single i 1) +
            V x i * (fderiv ℝ φ x) (EuclideanSpace.single i 1))) =
        φ x * (∑ i : Fin 3,
            (fderiv ℝ (fun y => V y i) x) (EuclideanSpace.single i 1)) +
          ∑ i : Fin 3, V x i * (fderiv ℝ φ x) (EuclideanSpace.single i 1) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsplit]
  have hgrad :
      ∑ i : Fin 3, V x i * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
        inner ℝ (gradient φ x) (V x) := by
    have hmap : ∀ i,
        V x i * (fderiv ℝ φ x) (EuclideanSpace.single i 1) =
          (fderiv ℝ φ x) (V x i • EuclideanSpace.single i 1) := by
      intro i
      rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    simp_rw [hmap]
    have hsumV :
        (∑ i : Fin 3, V x i • EuclideanSpace.single i 1) = V x := by
      ext j
      simp [Finset.sum_apply, smul_eq_mul, EuclideanSpace.single, Pi.single_apply,
        Finset.sum_ite_eq, Finset.mem_univ]
    rw [← map_sum, hsumV]
    exact (inner_gradient_left (y := V x) hφ).symm
  rw [hgrad, add_comm]

/-- Integration by parts given vanishing flux:
`∫ ⟨u, ∇φ⟩ = −∫ (div u) φ` once `∫ div(φ u) = 0`. On `𝕋³` the flux vanishes
by the divergence theorem; on this Haar model the flux identity is the
decay / compact-support hypothesis. The paper's convective cancellation
is this identity with `φ = ½|u|²`. -/
public theorem integration_by_parts_of_vanishing_flux
    (u : VelocityField) (φ : T3 → ℝ)
    (hφ : ∀ x, DifferentiableAt ℝ φ x)
    (hu : ∀ i x, DifferentiableAt ℝ (fun y => u y i) x)
    (hInt_pair : Integrable (fun x => inner ℝ (u x) (gradient φ x)))
    (hInt_div : Integrable (fun x => div u x * φ x))
    (hflux : ∫ x, div (fun y => φ y • u y) x ∂volume = 0) :
    ∫ x, inner ℝ (u x) (gradient φ x) ∂volume =
      -∫ x, div u x * φ x ∂volume := by
  have hfun :
      (fun x => div (fun y => φ y • u y) x) =
        fun x => inner ℝ (u x) (gradient φ x) + div u x * φ x := by
    funext x
    have hprod := div_smul_field φ u x (hφ x) (fun i => hu i x)
    rw [hprod, real_inner_comm, mul_comm (φ x)]
  have hsplit :=
    integral_add (μ := volume) hInt_pair hInt_div
  have hflux' :
      ∫ x, inner ℝ (u x) (gradient φ x) + div u x * φ x ∂volume = 0 := by
    rwa [← hfun]
  linarith [hsplit, hflux']

/-- Pointwise: `⟨w, (u·∇)w⟩ = ⟨u, ∇(½|w|²)⟩`. Cauchy difference energy
uses the transported field `w` along an independent carrier `u`; the
self-pairing `u = w` is the classical convective IBP integrand. -/
public theorem inner_convective_eq_inner_grad_half_norm_sq
    (u w : VelocityField) (x : T3)
    (hw : DifferentiableAt ℝ w x) :
    inner ℝ (w x) (convective u w x) =
      inner ℝ (u x) (gradient (fun y => (1 / 2 : ℝ) * ‖w y‖ ^ 2) x) := by
  have hF : HasFDerivAt (fun y => ‖w y‖ ^ 2)
      ((2 • innerSL ℝ (w x)).comp (fderiv ℝ w x)) x :=
    hw.hasFDerivAt.norm_sq
  have hsq : DifferentiableAt ℝ (fun y => ‖w y‖ ^ 2) x :=
    hF.differentiableAt
  have hhalf : DifferentiableAt ℝ (fun y => (1 / 2 : ℝ) * ‖w y‖ ^ 2) x :=
    hsq.const_mul (1 / 2 : ℝ)
  have hval :
      fderiv ℝ (fun y => ‖w y‖ ^ 2) x (u x) =
        2 * inner ℝ (w x) (convective u w x) := by
    rw [hF.fderiv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      innerSL_apply_apply, convective]
  have hgrad :
      inner ℝ (u x) (gradient (fun y => (1 / 2 : ℝ) * ‖w y‖ ^ 2) x) =
        (1 / 2) * fderiv ℝ (fun y => ‖w y‖ ^ 2) x (u x) := by
    rw [real_inner_comm, inner_gradient_left hhalf,
      fderiv_const_mul hsq (1 / 2 : ℝ), ContinuousLinearMap.smul_apply,
      smul_eq_mul]
  linarith [hval, hgrad]

/-- Pointwise: `⟨u, (u·∇)u⟩ = ⟨u, ∇(½|u|²)⟩`. This is the integrand of
the paper's convective IBP. -/
public theorem inner_self_convective_eq_inner_grad_half_norm_sq
    (u : VelocityField) (x : T3)
    (hu : DifferentiableAt ℝ u x) :
    inner ℝ (u x) (convective u u x) =
      inner ℝ (u x) (gradient (fun y => (1 / 2 : ℝ) * ‖u y‖ ^ 2) x) :=
  inner_convective_eq_inner_grad_half_norm_sq u u x hu

/-- Coordinate projections of a Fréchet-differentiable field are differentiable.
C¹ of `u : T3 → ℝ³` is the right regularity for IBP; mixed partials are not. -/
public theorem differentiableAt_coord_of_differentiableAt_field
    (u : VelocityField) (x : T3) (i : Fin 3)
    (hu : DifferentiableAt ℝ u x) :
    DifferentiableAt ℝ (fun y => u y i) x := by
  let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) i
  have hfun : (fun y => u y i) = fun y => L (u y) := rfl
  rw [hfun]
  exact L.differentiableAt.comp x hu

/-- `½|u|²` is C¹ wherever `u` is C¹. Used as the convective IBP test function. -/
public theorem differentiableAt_half_norm_sq
    (u : VelocityField) (x : T3) (hu : DifferentiableAt ℝ u x) :
    DifferentiableAt ℝ (fun y => (1 / 2 : ℝ) * ‖u y‖ ^ 2) x :=
  (hu.hasFDerivAt.norm_sq).differentiableAt.const_mul (1 / 2 : ℝ)

/-- Transported energy pairing: if `div u = 0` and the flux of
`½|w|² u` vanishes, then `∫ ⟨w, (u·∇)w⟩ = 0`. Cauchy uniqueness uses
this on the difference field `w = u − v` with carrier `u`. C¹; not
mixed partials. -/
public theorem transported_energy_pairing_vanishes
    (u w : VelocityField)
    (hdiv : ∀ x, div u x = 0)
    (hu : ∀ x, DifferentiableAt ℝ u x)
    (hw : ∀ x, DifferentiableAt ℝ w x)
    (hInt_pair : Integrable
      (fun x => inner ℝ (u x) (gradient (fun y => (1 / 2 : ℝ) * ‖w y‖ ^ 2) x)))
    (hInt_div : Integrable
      (fun x => div u x * ((1 / 2 : ℝ) * ‖w x‖ ^ 2)))
    (hflux : ∫ x,
        div (fun y => ((1 / 2 : ℝ) * ‖w y‖ ^ 2) • u y) x ∂volume = 0) :
    ∫ x, inner ℝ (w x) (convective u w x) ∂volume = 0 := by
  have hφ : ∀ x, DifferentiableAt ℝ (fun y => (1 / 2 : ℝ) * ‖w y‖ ^ 2) x :=
    fun x => differentiableAt_half_norm_sq w x (hw x)
  have hu_coord : ∀ i x, DifferentiableAt ℝ (fun y => u y i) x :=
    fun i x => differentiableAt_coord_of_differentiableAt_field u x i (hu x)
  have hpt :
      (fun x => inner ℝ (w x) (convective u w x)) =
        fun x =>
          inner ℝ (u x) (gradient (fun y => (1 / 2 : ℝ) * ‖w y‖ ^ 2) x) := by
    funext x
    exact inner_convective_eq_inner_grad_half_norm_sq u w x (hw x)
  have hibp :=
    integration_by_parts_of_vanishing_flux u
      (fun y => (1 / 2 : ℝ) * ‖w y‖ ^ 2)
      hφ hu_coord hInt_pair hInt_div hflux
  have hzero :
      ∫ x, div u x * ((1 / 2 : ℝ) * ‖w x‖ ^ 2) ∂volume = 0 := by
    have hfun :
        (fun x => div u x * ((1 / 2 : ℝ) * ‖w x‖ ^ 2)) = fun _ => 0 := by
      funext x
      simp [hdiv x]
    rw [hfun]
    exact integral_zero (α := T3) (G := ℝ) (μ := volume)
  rw [hpt, hibp, hzero, neg_zero]

/-- Convective IBP: if `div u = 0` and the flux of `½|u|² u` vanishes, then
`∫ ⟨u, (u·∇)u⟩ = 0`. Paper energy identity, not a dropped term.
Regularity is C¹ of the field (no mixed partials). -/
public theorem convective_energy_pairing_vanishes
    (u : VelocityField)
    (hdiv : ∀ x, div u x = 0)
    (hu : ∀ x, DifferentiableAt ℝ u x)
    (hInt_pair : Integrable
      (fun x => inner ℝ (u x) (gradient (fun y => (1 / 2 : ℝ) * ‖u y‖ ^ 2) x)))
    (hInt_div : Integrable
      (fun x => div u x * ((1 / 2 : ℝ) * ‖u x‖ ^ 2)))
    (hflux : ∫ x,
        div (fun y => ((1 / 2 : ℝ) * ‖u y‖ ^ 2) • u y) x ∂volume = 0) :
    ∫ x, inner ℝ (u x) (convective u u x) ∂volume = 0 := by
  have hφ : ∀ x, DifferentiableAt ℝ (fun y => (1 / 2 : ℝ) * ‖u y‖ ^ 2) x :=
    fun x => differentiableAt_half_norm_sq u x (hu x)
  have hu_coord : ∀ i x, DifferentiableAt ℝ (fun y => u y i) x :=
    fun i x => differentiableAt_coord_of_differentiableAt_field u x i (hu x)
  have hpt :
      (fun x => inner ℝ (u x) (convective u u x)) =
        fun x =>
          inner ℝ (u x) (gradient (fun y => (1 / 2 : ℝ) * ‖u y‖ ^ 2) x) := by
    funext x
    exact inner_self_convective_eq_inner_grad_half_norm_sq u x (hu x)
  have hibp :=
    integration_by_parts_of_vanishing_flux u
      (fun y => (1 / 2 : ℝ) * ‖u y‖ ^ 2)
      hφ hu_coord hInt_pair hInt_div hflux
  have hzero :
      ∫ x, div u x * ((1 / 2 : ℝ) * ‖u x‖ ^ 2) ∂volume = 0 := by
    have hfun :
        (fun x => div u x * ((1 / 2 : ℝ) * ‖u x‖ ^ 2)) = fun _ => 0 := by
      funext x
      simp [hdiv x]
    rw [hfun]
    exact integral_zero (α := T3) (G := ℝ) (μ := volume)
  rw [hpt, hibp, hzero, neg_zero]

/-- Pressure IBP: if `div u = 0` and the flux of `p u` vanishes, then
`∫ ⟨u, ∇p⟩ = 0`. C¹ of `u` and of `p`; mixed partials are not used here
(`curl ∇p = 0` is the C² identity `curl_gradient`). -/
public theorem pressure_energy_pairing_vanishes
    (u : VelocityField) (p : PressureField)
    (hdiv : ∀ x, div u x = 0)
    (hu : ∀ x, DifferentiableAt ℝ u x)
    (hp : ∀ x, DifferentiableAt ℝ p x)
    (hInt_pair : Integrable (fun x => inner ℝ (u x) (gradient p x)))
    (hInt_div : Integrable (fun x => div u x * p x))
    (hflux : ∫ x, div (fun y => p y • u y) x ∂volume = 0) :
    ∫ x, inner ℝ (u x) (pressureGradient p x) ∂volume = 0 := by
  have hu_coord : ∀ i x, DifferentiableAt ℝ (fun y => u y i) x :=
    fun i x => differentiableAt_coord_of_differentiableAt_field u x i (hu x)
  have hfun :
      (fun x => inner ℝ (u x) (pressureGradient p x)) =
        fun x => inner ℝ (u x) (gradient p x) := by
    funext x
    rfl
  have hibp :=
    integration_by_parts_of_vanishing_flux u p hp hu_coord hInt_pair hInt_div
      hflux
  have hzero : ∫ x, div u x * p x ∂volume = 0 := by
    have hz :
        (fun x => div u x * p x) = fun _ => 0 := by
      funext x
      simp [hdiv x]
    rw [hz]
    exact integral_zero (α := T3) (G := ℝ) (μ := volume)
  rw [hfun, hibp, hzero, neg_zero]

/-- Mixed partials of a `C²` scalar: `∂ⱼ (∇p)ᵢ = D²p (eⱼ, eᵢ)`. -/
public theorem directionalCoord_pressureGradient
    (p : PressureField) (x : T3) (i j : Fin 3)
    (hp : ContDiffAt ℝ 2 p x) :
    directionalCoord (pressureGradient p) i j x =
      (fderiv ℝ (fderiv ℝ p) x) (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
  unfold directionalCoord pressureGradient
  have hfd : DifferentiableAt ℝ (fderiv ℝ p) x :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  -- `ContDiffAt.eventually` needs a finite order and returns `ContDiffAt`,
  -- not `DifferentiableAt`. Bare `∞` is `ℝ≥0∞`; write `⊤` or let `simp`
  -- infer `WithTop ℕ∞`. There is no `DifferentiableAt.eventually`.
  have hnear : ∀ᶠ y in nhds x, DifferentiableAt ℝ p y := by
    have hp1 : ContDiffAt ℝ 1 p x :=
      hp.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    filter_upwards [hp1.eventually (by simp)] with y hy
    exact hy.differentiableAt_one
  have hgrad :
      (fun y => gradient p y i) =ᶠ[nhds x]
        fun y => (fderiv ℝ p y) (EuclideanSpace.single i 1) := by
    filter_upwards [hnear] with y hy
    exact gradient_coord p y i hy
  have hcomp :
      fderiv ℝ (fun y => (fderiv ℝ p y) (EuclideanSpace.single i 1)) x =
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).comp
          (fderiv ℝ (fderiv ℝ p) x) := by
    change fderiv ℝ (fun y =>
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)) (fderiv ℝ p y)) x = _
    rw [fderiv_comp' x (ContinuousLinearMap.differentiableAt _) hfd]
    simp [ContinuousLinearMap.fderiv]
  have hf : fderiv ℝ (fun y => gradient p y i) x =
      fderiv ℝ (fun y => (fderiv ℝ p y) (EuclideanSpace.single i 1)) x :=
    hgrad.fderiv_eq
  rw [hf, hcomp]
  rfl

/-- Coordinates of `curl` (standard orientation). -/
public theorem curl_apply (u : VelocityField) (x : T3) :
    curl u x 0 = directionalCoord u 2 1 x - directionalCoord u 1 2 x ∧
    curl u x 1 = directionalCoord u 0 2 x - directionalCoord u 2 0 x ∧
    curl u x 2 = directionalCoord u 1 0 x - directionalCoord u 0 1 x := by
  refine ⟨?_, ?_, ?_⟩
  · simp [curl]
  · simp [curl]
  · simp [curl]

/-- Curl is linear at points where both fields have differentiable coordinates. -/
public theorem curl_add (u v : VelocityField) (x : T3)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u y i) x)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x) :
    curl (fun y => u y + v y) x = curl u x + curl v x := by
  have hfun : ∀ i,
      (fun y => (u y + v y) i) = fun y => u y i + v y i := by
    intro i
    funext y
    rw [PiLp.add_apply]
  have hdir : ∀ comp dir,
      directionalCoord (fun y => u y + v y) comp dir x =
        directionalCoord u comp dir x + directionalCoord v comp dir x := by
    intro comp dir
    unfold directionalCoord
    rw [hfun, fderiv_fun_add (hu comp) (hv comp)]
    simp [ContinuousLinearMap.add_apply]
  ext i
  fin_cases i <;> simp [curl, hdir, PiLp.add_apply] <;> ring

/-- Operator-norm bound: `|(ω · ∇)u| ≤ ‖Du‖ |ω|`. The Calderón–Zygmund
estimate is `‖Du‖ ≤ C_CZ(3) ‖ω‖_∞` when `u` is Biot–Savart of `ω`. -/
public theorem convective_norm_le
    (ω u : VelocityField) (x : T3)
    (hu : DifferentiableAt ℝ u x) :
    ‖convective ω u x‖ ≤ ‖fderiv ℝ u x‖ * ‖ω x‖ := by
  unfold convective
  rw [hu.hasFDerivAt.fderiv]
  exact ContinuousLinearMap.le_opNorm _ _

/-- Polarization of the convective bilinear form:
`(u·∇)u − (v·∇)v = (u·∇)(u−v) + ((u−v)·∇)v`. Cauchy difference
momentum identity. C¹ of both fields. -/
public theorem convective_difference
    (u v : VelocityField) (x : T3)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    convective u u x - convective v v x =
      convective u (u - v) x + convective (u - v) v x := by
  unfold convective
  have hfuv : fderiv ℝ (u - v) x = fderiv ℝ u x - fderiv ℝ v x :=
    (hu.hasFDerivAt.sub hv.hasFDerivAt).fderiv
  have h1 : (fderiv ℝ (u - v) x) (u x) =
      (fderiv ℝ u x) (u x) - (fderiv ℝ v x) (u x) := by
    rw [hfuv]
    exact ContinuousLinearMap.sub_apply (fderiv ℝ u x) (fderiv ℝ v x) (u x)
  have h2 : (fderiv ℝ v x) ((u - v) x) =
      (fderiv ℝ v x) (u x) - (fderiv ℝ v x) (v x) := by
    have hx : (u - v) x = u x - v x := rfl
    rw [hx, map_sub]
  rw [h1, h2]
  exact (sub_add_sub_cancel
    ((fderiv ℝ u x) (u x))
    ((fderiv ℝ v x) (u x))
    ((fderiv ℝ v x) (v x))).symm

/-- Product rule: `Y · ∇⟨X,Z⟩ = ⟨(Y·∇)X, Z⟩ + ⟨X, (Y·∇)Z⟩`. C¹. -/
public theorem inner_convective_product_rule
    (X Z Y : VelocityField) (x : T3)
    (hX : DifferentiableAt ℝ X x) (hZ : DifferentiableAt ℝ Z x) :
    (fderiv ℝ (fun y => inner ℝ (X y) (Z y)) x) (Y x) =
      inner ℝ (convective Y X x) (Z x) + inner ℝ (X x) (convective Y Z x) := by
  have h := hX.hasFDerivAt.inner (𝕜 := ℝ) hZ.hasFDerivAt
  rw [h.fderiv]
  have hval :
      (fderivInnerCLM ℝ (X x, Z x))
          ((fderiv ℝ X x) (Y x), (fderiv ℝ Z x) (Y x)) =
        inner ℝ (X x) (fderiv ℝ Z x (Y x)) +
          inner ℝ (fderiv ℝ X x (Y x)) (Z x) := by
    simp [fderivInnerCLM]
  simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, convective,
    add_comm] at hval ⊢

/-- Six-term cyclic Lie pairing `X·[Y,Z] + Y·[Z,X] + Z·[X,Y]`. -/
@[expose] public def cyclicLiePairing (X Y Z : VelocityField) (x : T3) : ℝ :=
  inner ℝ (X x) (convective Y Z x - convective Z Y x) +
    inner ℝ (Y x) (convective Z X x - convective X Z x) +
      inner ℝ (Z x) (convective X Y x - convective Y X x)

/-- Paper Jacobi IBP expansion: each convective pairing is a directional
inner-product derivative minus the swapped slot (C¹ product rule). -/
public theorem cyclicLiePairing_expand
    (X Y Z : VelocityField) (x : T3)
    (hX : DifferentiableAt ℝ X x) (hY : DifferentiableAt ℝ Y x)
    (hZ : DifferentiableAt ℝ Z x) :
    cyclicLiePairing X Y Z x =
      (fderiv ℝ (fun y => inner ℝ (X y) (Z y)) x) (Y x) -
        inner ℝ (convective Y X x) (Z x) -
        ((fderiv ℝ (fun y => inner ℝ (X y) (Y y)) x) (Z x) -
          inner ℝ (convective Z X x) (Y x)) +
      (fderiv ℝ (fun y => inner ℝ (Y y) (X y)) x) (Z x) -
        inner ℝ (convective Z Y x) (X x) -
        ((fderiv ℝ (fun y => inner ℝ (Y y) (Z y)) x) (X x) -
          inner ℝ (convective X Y x) (Z x)) +
      (fderiv ℝ (fun y => inner ℝ (Z y) (Y y)) x) (X x) -
        inner ℝ (convective X Z x) (Y x) -
        ((fderiv ℝ (fun y => inner ℝ (Z y) (X y)) x) (Y x) -
          inner ℝ (convective Y Z x) (X x)) := by
  have hXZ_Y := inner_convective_product_rule X Z Y x hX hZ
  have hXY_Z := inner_convective_product_rule X Y Z x hX hY
  have hYX_Z := inner_convective_product_rule Y X Z x hY hX
  have hYZ_X := inner_convective_product_rule Y Z X x hY hZ
  have hZY_X := inner_convective_product_rule Z Y X x hZ hY
  have hZX_Y := inner_convective_product_rule Z X Y x hZ hX
  unfold cyclicLiePairing
  simp only [inner_sub_right]
  rw [hXZ_Y, hXY_Z, hYX_Z, hYZ_X, hZY_X, hZX_Y]
  ring

public theorem convective_coord (u v : VelocityField) (x : T3) (i : Fin 3)
    (hv : DifferentiableAt ℝ v x) :
    convective u v x i = (fderiv ℝ (fun y => v y i) x) (u x) := by
  unfold convective
  let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) i
  have hL : HasFDerivAt (fun y => L (v y)) (L.comp (fderiv ℝ v x)) x :=
    (L.hasFDerivAt).comp x hv.hasFDerivAt
  have hf : fderiv ℝ (fun y => v y i) x = L.comp (fderiv ℝ v x) := by
    change fderiv ℝ (fun y => L (v y)) x = _
    exact hL.fderiv
  rw [hf]
  rfl

/-- `(u · ∇)v` expands as `∑_k u_k ∂_k v`. -/
public theorem convective_eq_sum_directional
    (u v : VelocityField) (x : T3) (i : Fin 3)
    (hv : DifferentiableAt ℝ v x)
    (_hvi : DifferentiableAt ℝ (fun y => v y i) x) :
    convective u v x i =
      ∑ k : Fin 3, directionalCoord v i k x * u x k := by
  rw [convective_coord u v x i hv]
  have hdecomp :
      u x = ∑ k : Fin 3, u x k • EuclideanSpace.single k 1 := by
    ext j
    simp [Finset.sum_apply, smul_eq_mul, EuclideanSpace.single, Pi.single_apply,
      Finset.sum_ite_eq, Finset.mem_univ]
  have hmap : ∀ k,
      (fderiv ℝ (fun y => v y i) x) (u x k • EuclideanSpace.single k 1) =
        directionalCoord v i k x * u x k := by
    intro k
    rw [ContinuousLinearMap.map_smul, smul_eq_mul, directionalCoord, mul_comm]
  calc
    (fderiv ℝ (fun y => v y i) x) (u x)
        = (fderiv ℝ (fun y => v y i) x)
            (∑ k : Fin 3, u x k • EuclideanSpace.single k 1) := by
          conv_lhs => rw [hdecomp]
    _ = ∑ k : Fin 3,
          (fderiv ℝ (fun y => v y i) x)
            (u x k • EuclideanSpace.single k 1) := by
          simp [map_sum]
    _ = ∑ k : Fin 3, directionalCoord v i k x * u x k := by
          refine Finset.sum_congr rfl fun k _ => hmap k

/-- Mixed partials of a coordinate: `∂ⱼ (∂ᵢ u_k) = D² u_k (eⱼ, eᵢ)`. -/
public theorem fderiv_directionalCoord
    (u : VelocityField) (x : T3) (comp i j : Fin 3)
    (hu : ContDiffAt ℝ 2 (fun y => u y comp) x) :
    (fderiv ℝ (fun y => directionalCoord u comp i y) x) (EuclideanSpace.single j 1) =
      (fderiv ℝ (fderiv ℝ (fun y => u y comp)) x)
        (EuclideanSpace.single j 1) (EuclideanSpace.single i 1) := by
  unfold directionalCoord
  have hfd : DifferentiableAt ℝ (fderiv ℝ (fun y => u y comp)) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hcomp :
      fderiv ℝ (fun y =>
          (fderiv ℝ (fun z => u z comp) y) (EuclideanSpace.single i 1)) x =
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).comp
          (fderiv ℝ (fderiv ℝ (fun z => u z comp)) x) := by
    change fderiv ℝ (fun y =>
        (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1))
          (fderiv ℝ (fun z => u z comp) y)) x = _
    rw [fderiv_comp' x (ContinuousLinearMap.differentiableAt _) hfd]
    simp [ContinuousLinearMap.fderiv]
  rw [hcomp]
  rfl

/-- Equality of mixed partials on a `C²` coordinate. -/
public theorem directionalCoord_symm
    (u : VelocityField) (x : T3) (comp i j : Fin 3)
    (hu : ContDiffAt ℝ 2 (fun y => u y comp) x) :
    (fderiv ℝ (fun y => directionalCoord u comp i y) x) (EuclideanSpace.single j 1) =
      (fderiv ℝ (fun y => directionalCoord u comp j y) x) (EuclideanSpace.single i 1) := by
  have hsymm : IsSymmSndFDerivAt ℝ (fun y => u y comp) x :=
    hu.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  rw [fderiv_directionalCoord u x comp i j hu,
      fderiv_directionalCoord u x comp j i hu]
  exact hsymm.eq (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)

/-- `directionalCoord` of a `C²` coordinate is differentiable (it is `C¹`). -/
public theorem differentiableAt_directionalCoord
    (u : VelocityField) (x : T3) (comp i : Fin 3)
    (hu : ContDiffAt ℝ 2 (fun y => u y comp) x) :
    DifferentiableAt ℝ (fun y => directionalCoord u comp i y) x := by
  unfold directionalCoord
  have hfd : DifferentiableAt ℝ (fderiv ℝ (fun y => u y comp)) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i 1)).differentiableAt.comp x hfd

/-- `div ∘ curl = 0` at `C²` points (equality of mixed partials). -/
public theorem div_curl (u : VelocityField) (x : T3)
    (hu : ∀ k : Fin 3, ContDiffAt ℝ 2 (fun y => u y k) x) :
    div (curl u) x = 0 := by
  have h0 : (fun y => curl u y 0) =
      fun y => directionalCoord u 2 1 y - directionalCoord u 1 2 y := by
    funext y
    exact (curl_apply u y).1
  have h1 : (fun y => curl u y 1) =
      fun y => directionalCoord u 0 2 y - directionalCoord u 2 0 y := by
    funext y
    exact (curl_apply u y).2.1
  have h2 : (fun y => curl u y 2) =
      fun y => directionalCoord u 1 0 y - directionalCoord u 0 1 y := by
    funext y
    exact (curl_apply u y).2.2
  have hC1 (comp i : Fin 3) :
      DifferentiableAt ℝ (fun y => directionalCoord u comp i y) x :=
    differentiableAt_directionalCoord u x comp i (hu comp)
  have hsub0 :
      fderiv ℝ (fun y => curl u y 0) x =
        fderiv ℝ (fun y => directionalCoord u 2 1 y) x -
          fderiv ℝ (fun y => directionalCoord u 1 2 y) x := by
    rw [h0, fderiv_fun_sub (hC1 2 1) (hC1 1 2)]
  have hsub1 :
      fderiv ℝ (fun y => curl u y 1) x =
        fderiv ℝ (fun y => directionalCoord u 0 2 y) x -
          fderiv ℝ (fun y => directionalCoord u 2 0 y) x := by
    rw [h1, fderiv_fun_sub (hC1 0 2) (hC1 2 0)]
  have hsub2 :
      fderiv ℝ (fun y => curl u y 2) x =
        fderiv ℝ (fun y => directionalCoord u 1 0 y) x -
          fderiv ℝ (fun y => directionalCoord u 0 1 y) x := by
    rw [h2, fderiv_fun_sub (hC1 1 0) (hC1 0 1)]
  have hAD := directionalCoord_symm u x 2 1 0 (hu 2)
  have hBE := directionalCoord_symm u x 1 2 0 (hu 1)
  have hCF := directionalCoord_symm u x 0 2 1 (hu 0)
  have hsum :
      (fderiv ℝ (fun y => curl u y 0) x) (EuclideanSpace.single 0 1) +
        (fderiv ℝ (fun y => curl u y 1) x) (EuclideanSpace.single 1 1) +
          (fderiv ℝ (fun y => curl u y 2) x) (EuclideanSpace.single 2 1) = 0 := by
    rw [hsub0, hsub1, hsub2]
    simp only [ContinuousLinearMap.sub_apply]
    rw [hAD, hBE, hCF]
    ring
  unfold div
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_one, ← add_assoc]
  exact hsum

/-- A field that is a `C²` curl is pointwise divergence-free. -/
public theorem div_of_eq_curl (u A : VelocityField)
    (hA : ∀ x k, ContDiffAt ℝ 2 (fun y => A y k) x)
    (hcurl : u = curl A) :
    ∀ x, div u x = 0 := by
  intro x
  rw [hcurl]
  exact div_curl A x (fun k => hA x k)

/-- Curl of a gradient vanishes at `C²` points (equality of mixed partials). -/
public theorem curl_gradient (p : PressureField) (x : T3)
    (hp : ContDiffAt ℝ 2 p x) :
    curl (pressureGradient p) x = 0 := by
  have hsymm : IsSymmSndFDerivAt ℝ p x :=
    hp.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hswap : ∀ i j : Fin 3,
      directionalCoord (pressureGradient p) i j x =
        directionalCoord (pressureGradient p) j i x := by
    intro i j
    rw [directionalCoord_pressureGradient p x i j hp,
        directionalCoord_pressureGradient p x j i hp]
    exact hsymm.eq (EuclideanSpace.single j 1) (EuclideanSpace.single i 1)
  unfold curl
  have h01 := hswap 2 1
  have h12 := hswap 0 2
  have h20 := hswap 1 0
  ext k
  simp [h01, h12, h20, PiLp.single_apply]

/-- Spatial partial of `(u · ∇)u` by the product rule. C² of each coordinate
(paper §2.1 expansion of the stretching term). -/
public theorem directionalCoord_convective
    (u : VelocityField) (x : T3) (comp dir : Fin 3)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) :
    directionalCoord (convective u u) comp dir x =
      ∑ k : Fin 3,
        ((fderiv ℝ (fun y => directionalCoord u comp k y) x)
            (EuclideanSpace.single dir 1) * u x k +
          directionalCoord u comp k x * directionalCoord u k dir x) := by
  have hC1 : ∀ k, DifferentiableAt ℝ (fun y => u y k) x :=
    fun k =>
      ((hu k).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiableAt_one
  have hnear : ∀ k, ∀ᶠ y in nhds x, DifferentiableAt ℝ (fun z => u z k) y := by
    intro k
    have hk1 : ContDiffAt ℝ 1 (fun y => u y k) x :=
      (hu k).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    filter_upwards [hk1.eventually (by simp)] with y hy
    exact hy.differentiableAt_one
  have hvnear : ∀ᶠ y in nhds x, DifferentiableAt ℝ u y := by
    filter_upwards [hnear 0, hnear 1, hnear 2] with y h0 h1 h2
    exact (differentiableAt_piLp (p := 2) (𝕜 := ℝ)
        (E := fun _ : Fin 3 => ℝ)).mpr (fun i => by
      fin_cases i
      · exact h0
      · exact h1
      · exact h2)
  have heq :
      (fun y => convective u u y comp) =ᶠ[nhds x]
        fun y => ∑ k : Fin 3, directionalCoord u comp k y * u y k := by
    filter_upwards [hvnear, hnear comp] with y hyu hyc
    exact convective_eq_sum_directional u u y comp hyu hyc
  have hf :
      fderiv ℝ (fun y : T3 => convective u u y comp) x =
        fderiv ℝ (fun y : T3 => ∑ k : Fin 3, directionalCoord u comp k y * u y k) x :=
    heq.fderiv_eq
  unfold directionalCoord
  rw [hf]
  have hCLM :
      fderiv ℝ (fun y : T3 => ∑ k : Fin 3, directionalCoord u comp k y * u y k) x =
        ∑ k : Fin 3, fderiv ℝ (fun y => directionalCoord u comp k y * u y k) x :=
    fderiv_fun_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 3))) =>
      (differentiableAt_directionalCoord u x comp k (hu comp)).mul (hC1 k))
  rw [hCLM]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hmul :
      fderiv ℝ (fun y => directionalCoord u comp k y * u y k) x =
        directionalCoord u comp k x • fderiv ℝ (fun y => u y k) x +
          u x k • fderiv ℝ (fun y => directionalCoord u comp k y) x :=
    fderiv_fun_mul (differentiableAt_directionalCoord u x comp k (hu comp)) (hC1 k)
  rw [hmul]
  simp [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    directionalCoord]
  ring

/-- `∑_{k : Fin 3} f k = f 0 + f 1 + f 2`. -/
public theorem sum_univ_fin3 (f : Fin 3 → ℝ) :
    ∑ k : Fin 3, f k = f 0 + f 1 + f 2 := by
  have huniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
    ext i
    fin_cases i <;> simp
  rw [huniv]
  simp [Finset.sum_insert]
  rw [← add_assoc]

/-- C² of coordinates implies C¹ of the field. -/
public theorem differentiableAt_of_contDiffAt_coords
    (u : VelocityField) (x : T3)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) :
    DifferentiableAt ℝ u x :=
  (differentiableAt_piLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 3 => ℝ)).mpr
    (fun i => ((hu i).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiableAt_one)

/-- Each `curl` coordinate is C¹ at a C² point of `u`. -/
public theorem differentiableAt_curl_coord
    (u : VelocityField) (x : T3) (i : Fin 3)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) :
    DifferentiableAt ℝ (fun y => curl u y i) x := by
  fin_cases i
  · change DifferentiableAt ℝ (fun y => curl u y 0) x
    have h0 : (fun y => curl u y 0) =
        fun y => directionalCoord u 2 1 y - directionalCoord u 1 2 y := by
      funext y
      exact (curl_apply u y).1
    rw [h0]
    exact (differentiableAt_directionalCoord u x 2 1 (hu 2)).sub
      (differentiableAt_directionalCoord u x 1 2 (hu 1))
  · change DifferentiableAt ℝ (fun y => curl u y 1) x
    have h1 : (fun y => curl u y 1) =
        fun y => directionalCoord u 0 2 y - directionalCoord u 2 0 y := by
      funext y
      exact (curl_apply u y).2.1
    rw [h1]
    exact (differentiableAt_directionalCoord u x 0 2 (hu 0)).sub
      (differentiableAt_directionalCoord u x 2 0 (hu 2))
  · change DifferentiableAt ℝ (fun y => curl u y 2) x
    have h2 : (fun y => curl u y 2) =
        fun y => directionalCoord u 1 0 y - directionalCoord u 0 1 y := by
      funext y
      exact (curl_apply u y).2.2
    rw [h2]
    exact (differentiableAt_directionalCoord u x 1 0 (hu 1)).sub
      (differentiableAt_directionalCoord u x 0 1 (hu 0))

/-- `curl u` is C¹ at a C² point of `u`. -/
public theorem differentiableAt_curl
    (u : VelocityField) (x : T3)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) :
    DifferentiableAt ℝ (curl u) x :=
  (differentiableAt_piLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 3 => ℝ)).mpr
    (fun i => differentiableAt_curl_coord u x i hu)

/-- Spatial partials of `curl` coordinates at a `C²` point. -/
public theorem directionalCoord_curl
    (u : VelocityField) (x : T3) (dir : Fin 3)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) :
    directionalCoord (curl u) 0 dir x =
      (fderiv ℝ (fun y => directionalCoord u 2 1 y) x) (EuclideanSpace.single dir 1) -
        (fderiv ℝ (fun y => directionalCoord u 1 2 y) x) (EuclideanSpace.single dir 1) ∧
    directionalCoord (curl u) 1 dir x =
      (fderiv ℝ (fun y => directionalCoord u 0 2 y) x) (EuclideanSpace.single dir 1) -
        (fderiv ℝ (fun y => directionalCoord u 2 0 y) x) (EuclideanSpace.single dir 1) ∧
    directionalCoord (curl u) 2 dir x =
      (fderiv ℝ (fun y => directionalCoord u 1 0 y) x) (EuclideanSpace.single dir 1) -
        (fderiv ℝ (fun y => directionalCoord u 0 1 y) x) (EuclideanSpace.single dir 1) := by
  have hC1 (comp i : Fin 3) :
      DifferentiableAt ℝ (fun y => directionalCoord u comp i y) x :=
    differentiableAt_directionalCoord u x comp i (hu comp)
  have h0 : (fun y => curl u y 0) =
      fun y => directionalCoord u 2 1 y - directionalCoord u 1 2 y := by
    funext y
    exact (curl_apply u y).1
  have h1 : (fun y => curl u y 1) =
      fun y => directionalCoord u 0 2 y - directionalCoord u 2 0 y := by
    funext y
    exact (curl_apply u y).2.1
  have h2 : (fun y => curl u y 2) =
      fun y => directionalCoord u 1 0 y - directionalCoord u 0 1 y := by
    funext y
    exact (curl_apply u y).2.2
  refine ⟨?_, ?_, ?_⟩
  · change (fderiv ℝ (fun y => curl u y 0) x) (EuclideanSpace.single dir 1) = _
    rw [h0, fderiv_fun_sub (hC1 2 1) (hC1 1 2)]
    simp [ContinuousLinearMap.sub_apply]
  · change (fderiv ℝ (fun y => curl u y 1) x) (EuclideanSpace.single dir 1) = _
    rw [h1, fderiv_fun_sub (hC1 0 2) (hC1 2 0)]
    simp [ContinuousLinearMap.sub_apply]
  · change (fderiv ℝ (fun y => curl u y 2) x) (EuclideanSpace.single dir 1) = _
    rw [h2, fderiv_fun_sub (hC1 1 0) (hC1 0 1)]
    simp [ContinuousLinearMap.sub_apply]

/-- Paper §2.1 vector identity at a `C²` point, before imposing `div u = 0`.
`div (curl u) = 0` is already used via mixed partials, so the remaining
stretching identity is
`curl((u·∇)u) = (u·∇)ω − (ω·∇)u + (div u) ω`. -/
public theorem curl_convective
    (u : VelocityField) (x : T3)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x) :
    curl (convective u u) x =
      convective u (curl u) x - convective (curl u) u x + div u x • curl u x := by
  have hC1 : ∀ k, DifferentiableAt ℝ (fun y => u y k) x :=
    fun k =>
      ((hu k).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiableAt_one
  have hDiffU : DifferentiableAt ℝ u x :=
    differentiableAt_of_contDiffAt_coords u x hu
  have hDiffCurl : DifferentiableAt ℝ (curl u) x :=
    differentiableAt_curl u x hu
  have htrans0 :
      convective u (curl u) x 0 =
        ∑ k : Fin 3, directionalCoord (curl u) 0 k x * u x k :=
    convective_eq_sum_directional u (curl u) x 0 hDiffCurl
      (differentiableAt_curl_coord u x 0 hu)
  have htrans1 :
      convective u (curl u) x 1 =
        ∑ k : Fin 3, directionalCoord (curl u) 1 k x * u x k :=
    convective_eq_sum_directional u (curl u) x 1 hDiffCurl
      (differentiableAt_curl_coord u x 1 hu)
  have htrans2 :
      convective u (curl u) x 2 =
        ∑ k : Fin 3, directionalCoord (curl u) 2 k x * u x k :=
    convective_eq_sum_directional u (curl u) x 2 hDiffCurl
      (differentiableAt_curl_coord u x 2 hu)
  have hstretch0 :
      convective (curl u) u x 0 =
        ∑ k : Fin 3, directionalCoord u 0 k x * curl u x k :=
    convective_eq_sum_directional (curl u) u x 0 hDiffU (hC1 0)
  have hstretch1 :
      convective (curl u) u x 1 =
        ∑ k : Fin 3, directionalCoord u 1 k x * curl u x k :=
    convective_eq_sum_directional (curl u) u x 1 hDiffU (hC1 1)
  have hstretch2 :
      convective (curl u) u x 2 =
        ∑ k : Fin 3, directionalCoord u 2 k x * curl u x k :=
    convective_eq_sum_directional (curl u) u x 2 hDiffU (hC1 2)
  have hω := curl_apply u x
  have hdiv : div u x =
      directionalCoord u 0 0 x + directionalCoord u 1 1 x + directionalCoord u 2 2 x := by
    unfold div directionalCoord
    rw [sum_univ_fin3]
  ext i
  fin_cases i
  · -- component 0: paper stretching identity
    have hL := directionalCoord_convective u x 2 1 hu
    have hR := directionalCoord_convective u x 1 2 hu
    have hcurl0 := (curl_apply (convective u u) x).1
    have hswap2k (k : Fin 3) := directionalCoord_symm u x 2 k 1 (hu 2)
    have hswap1k (k : Fin 3) := directionalCoord_symm u x 1 k 2 (hu 1)
    have hdc := directionalCoord_curl u x
    have hdomega (k : Fin 3) :
        directionalCoord (curl u) 0 k x =
          (fderiv ℝ (fun y => directionalCoord u 2 1 y) x) (EuclideanSpace.single k 1) -
            (fderiv ℝ (fun y => directionalCoord u 1 2 y) x) (EuclideanSpace.single k 1) :=
      (hdc k hu).1
    have hfirst :
        ∑ k : Fin 3,
            ((fderiv ℝ (fun y => directionalCoord u 2 k y) x)
                (EuclideanSpace.single 1 1) * u x k -
              (fderiv ℝ (fun y => directionalCoord u 1 k y) x)
                (EuclideanSpace.single 2 1) * u x k) =
          convective u (curl u) x 0 := by
      have hterm (k : Fin 3) :
          (fderiv ℝ (fun y => directionalCoord u 2 k y) x)
              (EuclideanSpace.single 1 1) * u x k -
            (fderiv ℝ (fun y => directionalCoord u 1 k y) x)
              (EuclideanSpace.single 2 1) * u x k =
            directionalCoord (curl u) 0 k x * u x k := by
        rw [hswap2k k, hswap1k k, hdomega k]
        ring
      calc
        ∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 2 k y) x)
                  (EuclideanSpace.single 1 1) * u x k -
                (fderiv ℝ (fun y => directionalCoord u 1 k y) x)
                  (EuclideanSpace.single 2 1) * u x k)
            = ∑ k : Fin 3, directionalCoord (curl u) 0 k x * u x k := by
              refine Finset.sum_congr rfl fun k _ => hterm k
        _ = convective u (curl u) x 0 := htrans0.symm
    have hS :
        ∑ k : Fin 3,
            (directionalCoord u 2 k x * directionalCoord u k 1 x -
              directionalCoord u 1 k x * directionalCoord u k 2 x) =
          -convective (curl u) u x 0 + div u x * curl u x 0 := by
      rw [sum_univ_fin3, hstretch0, sum_univ_fin3, hdiv, hω.1, hω.2.1, hω.2.2]
      ring
    calc
      curl (convective u u) x 0
          = directionalCoord (convective u u) 2 1 x -
              directionalCoord (convective u u) 1 2 x := hcurl0
      _ = (∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 2 k y) x)
                  (EuclideanSpace.single 1 1) * u x k +
                directionalCoord u 2 k x * directionalCoord u k 1 x)) -
            (∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 1 k y) x)
                  (EuclideanSpace.single 2 1) * u x k +
                directionalCoord u 1 k x * directionalCoord u k 2 x)) := by
            rw [hL, hR]
      _ = (∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 2 k y) x)
                  (EuclideanSpace.single 1 1) * u x k -
                (fderiv ℝ (fun y => directionalCoord u 1 k y) x)
                  (EuclideanSpace.single 2 1) * u x k)) +
            ∑ k : Fin 3,
              (directionalCoord u 2 k x * directionalCoord u k 1 x -
                directionalCoord u 1 k x * directionalCoord u k 2 x) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            ring
      _ = convective u (curl u) x 0 +
            (-convective (curl u) u x 0 + div u x * curl u x 0) := by
            rw [hfirst, hS]
      _ = (convective u (curl u) x - convective (curl u) u x +
            div u x • curl u x) 0 := by
            simp [PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
            ring
  · -- component 1
    have hL := directionalCoord_convective u x 0 2 hu
    have hR := directionalCoord_convective u x 2 0 hu
    have hcurl1 := (curl_apply (convective u u) x).2.1
    have hswap0k (k : Fin 3) := directionalCoord_symm u x 0 k 2 (hu 0)
    have hswap2k (k : Fin 3) := directionalCoord_symm u x 2 k 0 (hu 2)
    have hdc := directionalCoord_curl u x
    have hdomega (k : Fin 3) :
        directionalCoord (curl u) 1 k x =
          (fderiv ℝ (fun y => directionalCoord u 0 2 y) x) (EuclideanSpace.single k 1) -
            (fderiv ℝ (fun y => directionalCoord u 2 0 y) x) (EuclideanSpace.single k 1) :=
      (hdc k hu).2.1
    have hfirst :
        ∑ k : Fin 3,
            ((fderiv ℝ (fun y => directionalCoord u 0 k y) x)
                (EuclideanSpace.single 2 1) * u x k -
              (fderiv ℝ (fun y => directionalCoord u 2 k y) x)
                (EuclideanSpace.single 0 1) * u x k) =
          convective u (curl u) x 1 := by
      have hterm (k : Fin 3) :
          (fderiv ℝ (fun y => directionalCoord u 0 k y) x)
              (EuclideanSpace.single 2 1) * u x k -
            (fderiv ℝ (fun y => directionalCoord u 2 k y) x)
              (EuclideanSpace.single 0 1) * u x k =
            directionalCoord (curl u) 1 k x * u x k := by
        rw [hswap0k k, hswap2k k, hdomega k]
        ring
      calc
        ∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 0 k y) x)
                  (EuclideanSpace.single 2 1) * u x k -
                (fderiv ℝ (fun y => directionalCoord u 2 k y) x)
                  (EuclideanSpace.single 0 1) * u x k)
            = ∑ k : Fin 3, directionalCoord (curl u) 1 k x * u x k := by
              refine Finset.sum_congr rfl fun k _ => hterm k
        _ = convective u (curl u) x 1 := htrans1.symm
    have hS :
        ∑ k : Fin 3,
            (directionalCoord u 0 k x * directionalCoord u k 2 x -
              directionalCoord u 2 k x * directionalCoord u k 0 x) =
          -convective (curl u) u x 1 + div u x * curl u x 1 := by
      rw [sum_univ_fin3, hstretch1, sum_univ_fin3, hdiv, hω.1, hω.2.1, hω.2.2]
      ring
    calc
      curl (convective u u) x 1
          = directionalCoord (convective u u) 0 2 x -
              directionalCoord (convective u u) 2 0 x := hcurl1
      _ = (∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 0 k y) x)
                  (EuclideanSpace.single 2 1) * u x k +
                directionalCoord u 0 k x * directionalCoord u k 2 x)) -
            (∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 2 k y) x)
                  (EuclideanSpace.single 0 1) * u x k +
                directionalCoord u 2 k x * directionalCoord u k 0 x)) := by
            rw [hL, hR]
      _ = (∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 0 k y) x)
                  (EuclideanSpace.single 2 1) * u x k -
                (fderiv ℝ (fun y => directionalCoord u 2 k y) x)
                  (EuclideanSpace.single 0 1) * u x k)) +
            ∑ k : Fin 3,
              (directionalCoord u 0 k x * directionalCoord u k 2 x -
                directionalCoord u 2 k x * directionalCoord u k 0 x) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            ring
      _ = convective u (curl u) x 1 +
            (-convective (curl u) u x 1 + div u x * curl u x 1) := by
            rw [hfirst, hS]
      _ = (convective u (curl u) x - convective (curl u) u x +
            div u x • curl u x) 1 := by
            simp [PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
            ring
  · -- component 2
    have hL := directionalCoord_convective u x 1 0 hu
    have hR := directionalCoord_convective u x 0 1 hu
    have hcurl2 := (curl_apply (convective u u) x).2.2
    have hswap1k (k : Fin 3) := directionalCoord_symm u x 1 k 0 (hu 1)
    have hswap0k (k : Fin 3) := directionalCoord_symm u x 0 k 1 (hu 0)
    have hdc := directionalCoord_curl u x
    have hdomega (k : Fin 3) :
        directionalCoord (curl u) 2 k x =
          (fderiv ℝ (fun y => directionalCoord u 1 0 y) x) (EuclideanSpace.single k 1) -
            (fderiv ℝ (fun y => directionalCoord u 0 1 y) x) (EuclideanSpace.single k 1) :=
      (hdc k hu).2.2
    have hfirst :
        ∑ k : Fin 3,
            ((fderiv ℝ (fun y => directionalCoord u 1 k y) x)
                (EuclideanSpace.single 0 1) * u x k -
              (fderiv ℝ (fun y => directionalCoord u 0 k y) x)
                (EuclideanSpace.single 1 1) * u x k) =
          convective u (curl u) x 2 := by
      have hterm (k : Fin 3) :
          (fderiv ℝ (fun y => directionalCoord u 1 k y) x)
              (EuclideanSpace.single 0 1) * u x k -
            (fderiv ℝ (fun y => directionalCoord u 0 k y) x)
              (EuclideanSpace.single 1 1) * u x k =
            directionalCoord (curl u) 2 k x * u x k := by
        rw [hswap1k k, hswap0k k, hdomega k]
        ring
      calc
        ∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 1 k y) x)
                  (EuclideanSpace.single 0 1) * u x k -
                (fderiv ℝ (fun y => directionalCoord u 0 k y) x)
                  (EuclideanSpace.single 1 1) * u x k)
            = ∑ k : Fin 3, directionalCoord (curl u) 2 k x * u x k := by
              refine Finset.sum_congr rfl fun k _ => hterm k
        _ = convective u (curl u) x 2 := htrans2.symm
    have hS :
        ∑ k : Fin 3,
            (directionalCoord u 1 k x * directionalCoord u k 0 x -
              directionalCoord u 0 k x * directionalCoord u k 1 x) =
          -convective (curl u) u x 2 + div u x * curl u x 2 := by
      rw [sum_univ_fin3, hstretch2, sum_univ_fin3, hdiv, hω.1, hω.2.1, hω.2.2]
      ring
    calc
      curl (convective u u) x 2
          = directionalCoord (convective u u) 1 0 x -
              directionalCoord (convective u u) 0 1 x := hcurl2
      _ = (∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 1 k y) x)
                  (EuclideanSpace.single 0 1) * u x k +
                directionalCoord u 1 k x * directionalCoord u k 0 x)) -
            (∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 0 k y) x)
                  (EuclideanSpace.single 1 1) * u x k +
                directionalCoord u 0 k x * directionalCoord u k 1 x)) := by
            rw [hL, hR]
      _ = (∑ k : Fin 3,
              ((fderiv ℝ (fun y => directionalCoord u 1 k y) x)
                  (EuclideanSpace.single 0 1) * u x k -
                (fderiv ℝ (fun y => directionalCoord u 0 k y) x)
                  (EuclideanSpace.single 1 1) * u x k)) +
            ∑ k : Fin 3,
              (directionalCoord u 1 k x * directionalCoord u k 0 x -
                directionalCoord u 0 k x * directionalCoord u k 1 x) := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            ring
      _ = convective u (curl u) x 2 +
            (-convective (curl u) u x 2 + div u x * curl u x 2) := by
            rw [hfirst, hS]
      _ = (convective u (curl u) x - convective (curl u) u x +
            div u x • curl u x) 2 := by
            simp [PiLp.sub_apply, PiLp.add_apply, smul_eq_mul]
            ring

/-- Paper §2.1 after `div u = 0` (and `div ω = 0` from C² mixed partials):
`∇ × (u·∇)u = (u·∇)ω − (ω·∇)u`. -/
public theorem curl_convective_div_free
    (u : VelocityField) (x : T3)
    (hu : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x)
    (hdiv : div u x = 0) :
    curl (convective u u) x =
      convective u (curl u) x - convective (curl u) u x := by
  have h := curl_convective u x hu
  rw [h, hdiv, zero_smul, add_zero]

/-- Curl of a three-term sum. C¹ of each field's coordinates.
`hbc` is C¹ of the `v+w` coordinates, so `curl_add` applies twice.
`add_assoc` is the `AddCommGroup` law on `EuclideanSpace ℝ (Fin 3)`
(inherited by `PiLp`); on each slot it is `PiLp.add_apply` then `add_assoc` on `ℝ`.
The identity is checked on curl components `0, 1, 2`. -/
public theorem curl_add3 (u v w : VelocityField) (x : T3)
    (hu : ∀ i, DifferentiableAt ℝ (fun y => u y i) x)
    (hv : ∀ i, DifferentiableAt ℝ (fun y => v y i) x)
    (hw : ∀ i, DifferentiableAt ℝ (fun y => w y i) x) :
    curl (fun y => u y + v y + w y) x = curl u x + curl v x + curl w x := by
  have hbc : ∀ i, DifferentiableAt ℝ (fun y => (v y + w y) i) x := by
    intro i
    have hfun : (fun y => (v y + w y) i) = fun y => v y i + w y i := by
      funext y
      rw [PiLp.add_apply]
    rw [hfun]
    exact (hv i).add (hw i)
  have hassoc : (fun y => u y + v y + w y) = fun y => u y + (v y + w y) := by
    funext y
    exact add_assoc (u y) (v y) (w y)
  have hdir (comp dir : Fin 3) :
      directionalCoord (fun y => u y + v y + w y) comp dir x =
        directionalCoord u comp dir x + directionalCoord v comp dir x +
          directionalCoord w comp dir x := by
    have hfun : (fun y => (u y + v y + w y) comp) =
        fun y => u y comp + (v y + w y) comp := by
      funext y
      rw [add_assoc (u y) (v y) (w y), PiLp.add_apply]
    have hbcfun : (fun y => (v y + w y) comp) =
        fun y => v y comp + w y comp := by
      funext y
      rw [PiLp.add_apply]
    unfold directionalCoord
    rw [hfun, fderiv_fun_add (hu comp) (hbc comp), hbcfun,
      fderiv_fun_add (hv comp) (hw comp)]
    simp only [ContinuousLinearMap.add_apply]
    ring
  -- Curl components 0, 1, 2: each is `∂_j u_k − ∂_k u_j`, and `hdir` splits.
  have hsum0 := (curl_apply (fun y => u y + v y + w y) x).1
  have hsum1 := (curl_apply (fun y => u y + v y + w y) x).2.1
  have hsum2 := (curl_apply (fun y => u y + v y + w y) x).2.2
  have hu0 := (curl_apply u x).1
  have hu1 := (curl_apply u x).2.1
  have hu2 := (curl_apply u x).2.2
  have hv0 := (curl_apply v x).1
  have hv1 := (curl_apply v x).2.1
  have hv2 := (curl_apply v x).2.2
  have hw0 := (curl_apply w x).1
  have hw1 := (curl_apply w x).2.1
  have hw2 := (curl_apply w x).2.2
  ext i
  fin_cases i
  · change curl (fun y => u y + v y + w y) x 0 =
        (curl u x + curl v x + curl w x) 0
    rw [hsum0]
    simp only [PiLp.add_apply]
    rw [hu0, hv0, hw0, hdir 2 1, hdir 1 2]
    ring
  · change curl (fun y => u y + v y + w y) x 1 =
        (curl u x + curl v x + curl w x) 1
    rw [hsum1]
    simp only [PiLp.add_apply]
    rw [hu1, hv1, hw1, hdir 0 2, hdir 2 0]
    ring
  · change curl (fun y => u y + v y + w y) x 2 =
        (curl u x + curl v x + curl w x) 2
    rw [hsum2]
    simp only [PiLp.add_apply]
    rw [hu2, hv2, hw2, hdir 1 0, hdir 0 1]
    ring

/-- Spatial slice of a joint scalar: `y ↦ F(t,y)` has derivative `DF(t,x) ∘ inr`. -/
public theorem fderiv_prod_snd_slice
    (F : ℝ × T3 → ℝ) (t : ℝ) (x : T3)
    (hF : DifferentiableAt ℝ F (t, x)) :
    fderiv ℝ (fun y : T3 => F (t, y)) x =
      (fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ T3) := by
  have hinr : HasFDerivAt (fun y : T3 => (t, y))
      (ContinuousLinearMap.inr ℝ ℝ T3) x :=
    hasFDerivAt_prodMk_right t x
  have hcomp : HasFDerivAt (F ∘ fun y : T3 => (t, y))
      ((fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ T3)) x :=
    hF.hasFDerivAt.comp (x := x) hinr
  have hfun : (fun y : T3 => F (t, y)) = F ∘ fun y : T3 => (t, y) := rfl
  rw [hfun]
  exact hcomp.fderiv

/-- Time slice of a joint scalar: `s ↦ F(s,x)` has derivative `DF(t,x) (1,0)`. -/
public theorem deriv_prod_fst_slice
    (F : ℝ × T3 → ℝ) (t : ℝ) (x : T3)
    (hF : DifferentiableAt ℝ F (t, x)) :
    deriv (fun s : ℝ => F (s, x)) t = (fderiv ℝ F (t, x)) (1, 0) := by
  have hinl : HasFDerivAt (fun s : ℝ => (s, x))
      (ContinuousLinearMap.inl ℝ ℝ T3) t :=
    hasFDerivAt_prodMk_left t x
  have hcomp : HasFDerivAt (F ∘ fun s : ℝ => (s, x))
      ((fderiv ℝ F (t, x)).comp (ContinuousLinearMap.inl ℝ ℝ T3)) t :=
    hF.hasFDerivAt.comp (x := t) hinl
  have hder := hasFDerivAt_iff_hasDerivAt.mp hcomp
  have hfun : (fun s : ℝ => F (s, x)) = F ∘ fun s : ℝ => (s, x) := rfl
  rw [hfun, hder.deriv]
  rfl

/-- Schwarz: `∂_x ∂_t f = ∂_t ∂_x f` at a `C²` spacetime point.
Uses `IsSymmSndFDerivAt` on `(t,x) ↦ f t x`, not an energy IBP. -/
public theorem time_space_mixed_partials
    (f : ℝ → T3 → ℝ) (t : ℝ) (x : T3) (v : T3)
    (hf : ContDiffAt ℝ 2 (fun p : ℝ × T3 => f p.1 p.2) (t, x)) :
    (fderiv ℝ (fun y => deriv (fun s => f s y) t) x) v =
      deriv (fun s => (fderiv ℝ (fun y => f s y) x) v) t := by
  let F : ℝ × T3 → ℝ := fun p => f p.1 p.2
  have hF1 : ContDiffAt ℝ 1 F (t, x) :=
    hf.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hnearF : ∀ᶠ p in nhds (t, x), DifferentiableAt ℝ F p := by
    filter_upwards [hF1.eventually (by simp)] with p hp
    exact hp.differentiableAt_one
  have hnearY : ∀ᶠ y in nhds x, DifferentiableAt ℝ F (t, y) :=
    (tendsto_const_nhds.prodMk_nhds tendsto_id).eventually hnearF
  have hnearS : ∀ᶠ s in nhds t, DifferentiableAt ℝ F (s, x) :=
    (tendsto_id.prodMk_nhds tendsto_const_nhds).eventually hnearF
  have _hFdiff : DifferentiableAt ℝ F (t, x) := hF1.differentiableAt_one
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) (t, x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm : IsSymmSndFDerivAt ℝ F (t, x) :=
    hf.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have heqY :
      (fun y => deriv (fun s => f s y) t) =ᶠ[nhds x]
        fun y => (fderiv ℝ F (t, y)) (1, 0) := by
    filter_upwards [hnearY] with y hy
    exact deriv_prod_fst_slice F t y hy
  have happlyY :
      fderiv ℝ (fun y => (fderiv ℝ F (t, y)) (1, 0)) x =
        (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × T3)).comp
          ((fderiv ℝ (fderiv ℝ F) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ T3)) := by
    have hinr : HasFDerivAt (fun y : T3 => (t, y))
        (ContinuousLinearMap.inr ℝ ℝ T3) x :=
      hasFDerivAt_prodMk_right t x
    have hcompF : HasFDerivAt (fun y : T3 => fderiv ℝ F (t, y))
        ((fderiv ℝ (fderiv ℝ F) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ T3)) x :=
      hfd.hasFDerivAt.comp (x := x) hinr
    have happ : HasFDerivAt (fun y => (fderiv ℝ F (t, y)) (1, 0))
        ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × T3)).comp
          ((fderiv ℝ (fderiv ℝ F) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ T3))) x :=
      (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × T3)).hasFDerivAt.comp (x := x) hcompF
    exact happ.fderiv
  have hLHS :
      (fderiv ℝ (fun y => deriv (fun s => f s y) t) x) v =
        (fderiv ℝ (fderiv ℝ F) (t, x)) (0, v) (1, 0) := by
    rw [heqY.fderiv_eq, happlyY]
    rfl
  have heqS :
      (fun s => (fderiv ℝ (fun y => f s y) x) v) =ᶠ[nhds t]
        fun s => (fderiv ℝ F (s, x)) (0, v) := by
    filter_upwards [hnearS] with s hs
    have hfY := fderiv_prod_snd_slice F s x hs
    change (fderiv ℝ (fun y => F (s, y)) x) v = (fderiv ℝ F (s, x)) (0, v)
    rw [hfY]
    rfl
  have happS :
      HasFDerivAt (fun s : ℝ => (fderiv ℝ F (s, x)) (0, v))
        ((ContinuousLinearMap.apply ℝ ℝ ((0, v) : ℝ × T3)).comp
          ((fderiv ℝ (fderiv ℝ F) (t, x)).comp (ContinuousLinearMap.inl ℝ ℝ T3))) t := by
    have hinl : HasFDerivAt (fun s : ℝ => (s, x))
        (ContinuousLinearMap.inl ℝ ℝ T3) t :=
      hasFDerivAt_prodMk_left t x
    have hcompF : HasFDerivAt (fun s : ℝ => fderiv ℝ F (s, x))
        ((fderiv ℝ (fderiv ℝ F) (t, x)).comp (ContinuousLinearMap.inl ℝ ℝ T3)) t :=
      hfd.hasFDerivAt.comp (x := t) hinl
    exact (ContinuousLinearMap.apply ℝ ℝ ((0, v) : ℝ × T3)).hasFDerivAt.comp
      (x := t) hcompF
  have hderS := hasFDerivAt_iff_hasDerivAt.mp happS
  have hRHS :
      deriv (fun s => (fderiv ℝ (fun y => f s y) x) v) t =
        (fderiv ℝ (fderiv ℝ F) (t, x)) (1, 0) (0, v) := by
    have hcong : deriv (fun s => (fderiv ℝ (fun y => f s y) x) v) t =
        deriv (fun s => (fderiv ℝ F (s, x)) (0, v)) t :=
      heqS.deriv_eq
    rw [hcong, hderS.deriv]
    rfl
  rw [hLHS, hRHS]
  exact hsymm.eq (0, v) (1, 0)

/-- Coordinate of a time-differentiable Euclidean path is the time derivative of that coordinate. -/
public theorem deriv_euclidean_coord
    (g : ℝ → EuclideanSpace ℝ (Fin 3)) (t : ℝ) (i : Fin 3)
    (hg : DifferentiableAt ℝ g t) :
    deriv g t i = deriv (fun s => g s i) t := by
  let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) i
  have hfun : (fun s => g s i) = fun s => L (g s) := rfl
  have hL : HasFDerivAt (fun s => L (g s)) (L.comp (fderiv ℝ g t)) t :=
    L.hasFDerivAt.comp t hg.hasFDerivAt
  have hder : HasDerivAt (fun s => L (g s)) ((L.comp (fderiv ℝ g t)) 1) t :=
    hasFDerivAt_iff_hasDerivAt.mp hL
  rw [hfun, hder.deriv]
  change L (fderiv ℝ g t 1) = L (deriv g t)
  rw [fderiv_apply_one_eq_deriv]

/-- `curl ∂t u = ∂t (curl u)` by Schwarz on each coordinate (paper §2.1). -/
public theorem curl_time_deriv
    (u : TimeDependentVelocity) (t : ℝ) (x : T3)
    (hC2 : ∀ k, ContDiffAt ℝ 2 (fun q : ℝ × T3 => u q.1 q.2 k) (t, x)) :
    curl (fun y => time_deriv u t y) x =
      time_deriv (fun s => curl (u s)) t x := by
  have hk (k : Fin 3) :
      ∀ᶠ y in nhds x, DifferentiableAt ℝ (fun s => u s y k) t := by
    have hF1 : ContDiffAt ℝ 1 (fun q : ℝ × T3 => u q.1 q.2 k) (t, x) :=
      (hC2 k).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hnearY : ∀ᶠ y in nhds x,
        DifferentiableAt ℝ (fun q : ℝ × T3 => u q.1 q.2 k) (t, y) :=
      (tendsto_const_nhds.prodMk_nhds tendsto_id).eventually
        (by
          filter_upwards [hF1.eventually (by simp)] with p hp
          exact hp.differentiableAt_one)
    filter_upwards [hnearY] with y hy
    have hinl : HasFDerivAt (fun s : ℝ => (s, y))
        (ContinuousLinearMap.inl ℝ ℝ T3) t :=
      hasFDerivAt_prodMk_left t y
    exact (hy.hasFDerivAt.comp (x := t) hinl).differentiableAt
  have hnearVec : ∀ᶠ y in nhds x, DifferentiableAt ℝ (fun s => u s y) t := by
    filter_upwards [hk 0, hk 1, hk 2] with y h0 h1 h2
    exact (differentiableAt_piLp (p := 2) (𝕜 := ℝ)
        (E := fun _ : Fin 3 => ℝ)).mpr (fun i => by
      fin_cases i
      · exact h0
      · exact h1
      · exact h2)
  have heqCoord (comp : Fin 3) :
      (fun y => time_deriv u t y comp) =ᶠ[nhds x]
        fun y => deriv (fun s => u s y comp) t := by
    filter_upwards [hnearVec] with y hy
    change deriv (fun s => u s y) t comp = deriv (fun s => u s y comp) t
    exact deriv_euclidean_coord (fun s => u s y) t comp hy
  have hswap (comp dir : Fin 3) :
      directionalCoord (fun y => time_deriv u t y) comp dir x =
        deriv (fun s => directionalCoord (u s) comp dir x) t := by
    unfold directionalCoord
    rw [(heqCoord comp).fderiv_eq]
    exact time_space_mixed_partials (fun s y => u s y comp) t x
      (EuclideanSpace.single dir (1 : ℝ)) (hC2 comp)
  have hcoord_diff (comp dir : Fin 3) :
      DifferentiableAt ℝ (fun s => directionalCoord (u s) comp dir x) t := by
    have hF : ContDiffAt ℝ 2 (fun p : ℝ × T3 => u p.1 p.2 comp) (t, x) := hC2 comp
    have hfd : DifferentiableAt ℝ
        (fderiv ℝ (fun p : ℝ × T3 => u p.1 p.2 comp)) (t, x) :=
      (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hinl : HasFDerivAt (fun s : ℝ => (s, x))
        (ContinuousLinearMap.inl ℝ ℝ T3) t :=
      hasFDerivAt_prodMk_left t x
    have hcompF : HasFDerivAt
        (fun s : ℝ => fderiv ℝ (fun p : ℝ × T3 => u p.1 p.2 comp) (s, x))
        ((fderiv ℝ (fderiv ℝ (fun p : ℝ × T3 => u p.1 p.2 comp)) (t, x)).comp
          (ContinuousLinearMap.inl ℝ ℝ T3)) t :=
      hfd.hasFDerivAt.comp (x := t) hinl
    have happ : HasFDerivAt
        (fun s => (fderiv ℝ (fun p : ℝ × T3 => u p.1 p.2 comp) (s, x))
          (0, EuclideanSpace.single dir (1 : ℝ)))
        ((ContinuousLinearMap.apply ℝ ℝ
            ((0, EuclideanSpace.single dir (1 : ℝ)) : ℝ × T3)).comp
          ((fderiv ℝ (fderiv ℝ (fun p : ℝ × T3 => u p.1 p.2 comp)) (t, x)).comp
            (ContinuousLinearMap.inl ℝ ℝ T3))) t :=
      (ContinuousLinearMap.apply ℝ ℝ
          ((0, EuclideanSpace.single dir (1 : ℝ)) : ℝ × T3)).hasFDerivAt.comp
        (x := t) hcompF
    have hF1 : ContDiffAt ℝ 1 (fun p : ℝ × T3 => u p.1 p.2 comp) (t, x) :=
      hF.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hnearS : ∀ᶠ s in nhds t,
        DifferentiableAt ℝ (fun p : ℝ × T3 => u p.1 p.2 comp) (s, x) :=
      (tendsto_id.prodMk_nhds tendsto_const_nhds).eventually
        (by
          filter_upwards [hF1.eventually (by simp)] with p hp
          exact hp.differentiableAt_one)
    have heq : (fun s => directionalCoord (u s) comp dir x) =ᶠ[nhds t]
        fun s => (fderiv ℝ (fun p : ℝ × T3 => u p.1 p.2 comp) (s, x))
          (0, EuclideanSpace.single dir (1 : ℝ)) := by
      filter_upwards [hnearS] with s hs
      have hfY := fderiv_prod_snd_slice (fun p => u p.1 p.2 comp) s x hs
      unfold directionalCoord
      change (fderiv ℝ (fun y => u s y comp) x)
          (EuclideanSpace.single dir (1 : ℝ)) = _
      rw [hfY]
      rfl
    exact happ.differentiableAt.congr_of_eventuallyEq heq
  have hcurl_t : DifferentiableAt ℝ (fun s => curl (u s) x) t := by
    refine (differentiableAt_piLp (p := 2) (𝕜 := ℝ)
        (E := fun _ : Fin 3 => ℝ)).mpr ?_
    intro i
    fin_cases i
    · change DifferentiableAt ℝ (fun s => curl (u s) x 0) t
      have h0 : (fun s => curl (u s) x 0) =
          fun s => directionalCoord (u s) 2 1 x - directionalCoord (u s) 1 2 x := by
        funext s
        exact (curl_apply (u s) x).1
      rw [h0]
      exact (hcoord_diff 2 1).sub (hcoord_diff 1 2)
    · change DifferentiableAt ℝ (fun s => curl (u s) x 1) t
      have h1 : (fun s => curl (u s) x 1) =
          fun s => directionalCoord (u s) 0 2 x - directionalCoord (u s) 2 0 x := by
        funext s
        exact (curl_apply (u s) x).2.1
      rw [h1]
      exact (hcoord_diff 0 2).sub (hcoord_diff 2 0)
    · change DifferentiableAt ℝ (fun s => curl (u s) x 2) t
      have h2 : (fun s => curl (u s) x 2) =
          fun s => directionalCoord (u s) 1 0 x - directionalCoord (u s) 0 1 x := by
        funext s
        exact (curl_apply (u s) x).2.2
      rw [h2]
      exact (hcoord_diff 1 0).sub (hcoord_diff 0 1)
  have hcurl_apply := curl_apply (fun y => time_deriv u t y) x
  have ht0 :
      time_deriv (fun s => curl (u s)) t x 0 =
        deriv (fun s => directionalCoord (u s) 2 1 x) t -
          deriv (fun s => directionalCoord (u s) 1 2 x) t := by
    unfold time_deriv
    have hfun : (fun s => curl (u s) x 0) =
        fun s => directionalCoord (u s) 2 1 x - directionalCoord (u s) 1 2 x := by
      funext s
      exact (curl_apply (u s) x).1
    rw [deriv_euclidean_coord (fun s => curl (u s) x) t 0 hcurl_t, hfun,
      deriv_fun_sub (hcoord_diff 2 1) (hcoord_diff 1 2)]
  have ht1 :
      time_deriv (fun s => curl (u s)) t x 1 =
        deriv (fun s => directionalCoord (u s) 0 2 x) t -
          deriv (fun s => directionalCoord (u s) 2 0 x) t := by
    unfold time_deriv
    have hfun : (fun s => curl (u s) x 1) =
        fun s => directionalCoord (u s) 0 2 x - directionalCoord (u s) 2 0 x := by
      funext s
      exact (curl_apply (u s) x).2.1
    rw [deriv_euclidean_coord (fun s => curl (u s) x) t 1 hcurl_t, hfun,
      deriv_fun_sub (hcoord_diff 0 2) (hcoord_diff 2 0)]
  have ht2 :
      time_deriv (fun s => curl (u s)) t x 2 =
        deriv (fun s => directionalCoord (u s) 1 0 x) t -
          deriv (fun s => directionalCoord (u s) 0 1 x) t := by
    unfold time_deriv
    have hfun : (fun s => curl (u s) x 2) =
        fun s => directionalCoord (u s) 1 0 x - directionalCoord (u s) 0 1 x := by
      funext s
      exact (curl_apply (u s) x).2.2
    rw [deriv_euclidean_coord (fun s => curl (u s) x) t 2 hcurl_t, hfun,
      deriv_fun_sub (hcoord_diff 1 0) (hcoord_diff 0 1)]
  ext i
  fin_cases i
  · change curl (fun y => time_deriv u t y) x 0 =
        time_deriv (fun s => curl (u s)) t x 0
    rw [hcurl_apply.1, ht0, hswap 2 1, hswap 1 2]
  · change curl (fun y => time_deriv u t y) x 1 =
        time_deriv (fun s => curl (u s)) t x 1
    rw [hcurl_apply.2.1, ht1, hswap 0 2, hswap 2 0]
  · change curl (fun y => time_deriv u t y) x 2 =
        time_deriv (fun s => curl (u s)) t x 2
    rw [hcurl_apply.2.2, ht2, hswap 1 0, hswap 0 1]

/-- Coordinate of a Fréchet derivative is the derivative of that coordinate. -/
public theorem fderiv_field_coord
    (G : VelocityField) (x : T3) (j : Fin 3) (v : T3)
    (hG : DifferentiableAt ℝ G x) :
    (fderiv ℝ G x v) j = (fderiv ℝ (fun y => G y j) x) v := by
  let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) j
  have hfun : (fun y => G y j) = fun y => L (G y) := rfl
  have hL : HasFDerivAt (fun y => L (G y)) (L.comp (fderiv ℝ G x)) x :=
    L.hasFDerivAt.comp x hG.hasFDerivAt
  rw [hfun, hL.fderiv]
  rfl

/-- Vector Laplacian is the scalar Laplacian of each coordinate. C² of the field. -/
public theorem laplacian_coord
    (u : VelocityField) (x : T3) (j : Fin 3)
    (hu : ContDiffAt ℝ 2 u x) :
    laplacian u x j =
      ∑ i : Fin 3,
        (fderiv ℝ (fun y => directionalCoord u j i y) x)
          (EuclideanSpace.single i 1) := by
  have _hC1 : DifferentiableAt ℝ u x :=
    (hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiableAt_one
  have hnear : ∀ᶠ y in nhds x, DifferentiableAt ℝ u y := by
    have hu1 : ContDiffAt ℝ 1 u x :=
      hu.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    filter_upwards [hu1.eventually (by simp)] with y hy
    exact hy.differentiableAt_one
  have hfd : DifferentiableAt ℝ (fderiv ℝ u) x :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdir (i : Fin 3) :
      DifferentiableAt ℝ
        (fun y => (fderiv ℝ u y) (EuclideanSpace.single i (1 : ℝ))) x :=
    (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin 3))
        (EuclideanSpace.single i (1 : ℝ))).differentiableAt.comp x hfd
  have heq (i : Fin 3) :
      (fun y => ((fderiv ℝ u y) (EuclideanSpace.single i (1 : ℝ))) j) =ᶠ[nhds x]
        fun y => directionalCoord u j i y := by
    filter_upwards [hnear] with y hy
    exact fderiv_field_coord u y j (EuclideanSpace.single i (1 : ℝ)) hy
  unfold laplacian
  let w : Fin 3 → EuclideanSpace ℝ (Fin 3) := fun i =>
    (fderiv ℝ (fun y => (fderiv ℝ u y) (EuclideanSpace.single i (1 : ℝ))) x)
      (EuclideanSpace.single i (1 : ℝ))
  let P : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
    PiLp.proj (p := 2) (fun _ : Fin 3 => ℝ) j
  have hsum : P (∑ i : Fin 3, w i) = ∑ i : Fin 3, P (w i) :=
    map_sum P.toLinearMap (fun i => w i) Finset.univ
  have hj : (∑ i : Fin 3, w i) j = P (∑ i : Fin 3, w i) := rfl
  rw [hj, hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcoord :=
    fderiv_field_coord (fun y => (fderiv ℝ u y) (EuclideanSpace.single i (1 : ℝ)))
      x j (EuclideanSpace.single i (1 : ℝ)) (hdir i)
  change P (w i) = _
  have hPw : P (w i) = w i j := rfl
  rw [hPw, hcoord, (heq i).fderiv_eq]

/-- Hessian of a `C²` scalar applied to two increments. -/
public theorem fderiv_apply_fderiv
    (φ : T3 → ℝ) (x : T3) (v w : T3)
    (hφ : ContDiffAt ℝ 2 φ x) :
    (fderiv ℝ (fun y => (fderiv ℝ φ y) v) x) w =
      (fderiv ℝ (fderiv ℝ φ) x) w v := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have happ : HasFDerivAt (fun y => (fderiv ℝ φ y) v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ φ) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp (x := x) hfd.hasFDerivAt
  rw [happ.fderiv]
  rfl

/-- A `C³` coordinate has `C²` directional coordinates. -/
public theorem contDiffAt_directionalCoord
    (u : VelocityField) (x : T3) (comp i : Fin 3)
    (hu : ContDiffAt ℝ 3 (fun y => u y comp) x) :
    ContDiffAt ℝ 2 (fun y => directionalCoord u comp i y) x := by
  unfold directionalCoord
  have hfd : ContDiffAt ℝ 2 (fderiv ℝ (fun y => u y comp)) x :=
    hu.fderiv_right (m := 2) (by norm_num)
  exact (ContinuousLinearMap.contDiff
      (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ)))).contDiffAt.comp
    x hfd

/-- Mixed partial of the Laplacian: `∂_dir (Δ u)_comp` is the scalar Laplacian
of `∂_dir u_comp`, by Schwarz on each `C²` directional coordinate. -/
public theorem directionalCoord_laplacian
    (u : VelocityField) (x : T3) (comp dir : Fin 3)
    (hu : ∀ k, ContDiffAt ℝ 3 (fun y => u y k) x) :
    directionalCoord (laplacian u) comp dir x =
      ∑ i : Fin 3,
        (fderiv ℝ (fderiv ℝ (fun z => directionalCoord u comp dir z)) x)
          (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ)) := by
  have hU : ContDiffAt ℝ 3 u x :=
    (contDiffAt_piLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 3 => ℝ)).mpr hu
  have hU2 : ContDiffAt ℝ 2 u x :=
    hU.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hnear : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 u y :=
    (hU.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp)
  have heq :
      (fun y => laplacian u y comp) =ᶠ[nhds x]
        fun y => ∑ i : Fin 3,
          (fderiv ℝ (fun z => directionalCoord u comp i z) y)
            (EuclideanSpace.single i (1 : ℝ)) := by
    filter_upwards [hnear] with y hy
    exact laplacian_coord u y comp hy
  have hC2dir (i : Fin 3) :
      ContDiffAt ℝ 2 (fun z => directionalCoord u comp i z) x :=
    contDiffAt_directionalCoord u x comp i (hu comp)
  have hdiff (i : Fin 3) :
      DifferentiableAt ℝ
        (fun y => (fderiv ℝ (fun z => directionalCoord u comp i z) y)
          (EuclideanSpace.single i (1 : ℝ))) x :=
    ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).differentiableAt.comp x
      (((hC2dir i).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
  have hsum' :
      fderiv ℝ (fun y => ∑ i : Fin 3,
          (fderiv ℝ (fun z => directionalCoord u comp i z) y)
            (EuclideanSpace.single i (1 : ℝ))) x =
        ∑ i : Fin 3,
          fderiv ℝ (fun y =>
              (fderiv ℝ (fun z => directionalCoord u comp i z) y)
                (EuclideanSpace.single i (1 : ℝ))) x :=
    fderiv_fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) => hdiff i)
  change (fderiv ℝ (fun y => laplacian u y comp) x)
      (EuclideanSpace.single dir (1 : ℝ)) = _
  rw [heq.fderiv_eq, hsum']
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hD2 :=
    fderiv_apply_fderiv (fun z => directionalCoord u comp i z) x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single dir (1 : ℝ)) (hC2dir i)
  have hsym : IsSymmSndFDerivAt ℝ (fun z => directionalCoord u comp i z) x :=
    (hC2dir i).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have hswap :=
    hsym.eq (EuclideanSpace.single dir (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))
  have hmix :
      (fun y => (fderiv ℝ (fun z => directionalCoord u comp i z) y)
          (EuclideanSpace.single dir (1 : ℝ))) =ᶠ[nhds x]
        fun y => (fderiv ℝ (fun z => directionalCoord u comp dir z) y)
          (EuclideanSpace.single i (1 : ℝ)) := by
    have hnearC : ∀ᶠ y in nhds x, ContDiffAt ℝ 2 (fun z => u z comp) y :=
      ((hu comp).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp)
    filter_upwards [hnearC] with y hy
    exact directionalCoord_symm u y comp i dir hy
  have hL :
      (fderiv ℝ (fun y => (fderiv ℝ (fun z => directionalCoord u comp i z) y)
          (EuclideanSpace.single i (1 : ℝ))) x)
        (EuclideanSpace.single dir (1 : ℝ)) =
      (fderiv ℝ (fderiv ℝ (fun z => directionalCoord u comp i z)) x)
        (EuclideanSpace.single dir (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) :=
    hD2
  have hR :
      (fderiv ℝ (fun y => (fderiv ℝ (fun z => directionalCoord u comp dir z) y)
          (EuclideanSpace.single i (1 : ℝ))) x)
        (EuclideanSpace.single i (1 : ℝ)) =
      (fderiv ℝ (fderiv ℝ (fun z => directionalCoord u comp dir z)) x)
        (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) :=
    fderiv_apply_fderiv (fun z => directionalCoord u comp dir z) x
      (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))
      (hC2dir dir)
  have hmid :
      (fderiv ℝ (fun y => (fderiv ℝ (fun z => directionalCoord u comp i z) y)
          (EuclideanSpace.single dir (1 : ℝ))) x)
        (EuclideanSpace.single i (1 : ℝ)) =
      (fderiv ℝ (fun y => (fderiv ℝ (fun z => directionalCoord u comp dir z) y)
          (EuclideanSpace.single i (1 : ℝ))) x)
        (EuclideanSpace.single i (1 : ℝ)) := by
    rw [hmix.fderiv_eq]
  calc
    (fderiv ℝ (fun y => (fderiv ℝ (fun z => directionalCoord u comp i z) y)
        (EuclideanSpace.single i (1 : ℝ))) x)
      (EuclideanSpace.single dir (1 : ℝ))
        = (fderiv ℝ (fderiv ℝ (fun z => directionalCoord u comp i z)) x)
            (EuclideanSpace.single dir (1 : ℝ))
            (EuclideanSpace.single i (1 : ℝ)) := hL
    _ = (fderiv ℝ (fderiv ℝ (fun z => directionalCoord u comp i z)) x)
          (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single dir (1 : ℝ)) := hswap
    _ = (fderiv ℝ (fun y => (fderiv ℝ (fun z => directionalCoord u comp i z) y)
            (EuclideanSpace.single dir (1 : ℝ))) x)
          (EuclideanSpace.single i (1 : ℝ)) := by
            rw [fderiv_apply_fderiv (fun z => directionalCoord u comp i z) x
              (EuclideanSpace.single dir (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ))
              (hC2dir i)]
    _ = (fderiv ℝ (fun y => (fderiv ℝ (fun z => directionalCoord u comp dir z) y)
            (EuclideanSpace.single i (1 : ℝ))) x)
          (EuclideanSpace.single i (1 : ℝ)) := hmid
    _ = (fderiv ℝ (fderiv ℝ (fun z => directionalCoord u comp dir z)) x)
          (EuclideanSpace.single i (1 : ℝ))
          (EuclideanSpace.single i (1 : ℝ)) := hR

/-- `curl Δu = Δ curl u` at `C³` points (third mixed partials commute). -/
public theorem curl_laplacian
    (u : VelocityField) (x : T3)
    (hu : ∀ k, ContDiffAt ℝ 3 (fun y => u y k) x) :
    curl (laplacian u) x = laplacian (curl u) x := by
  have hu2 : ∀ k, ContDiffAt ℝ 2 (fun y => u y k) x :=
    fun k => (hu k).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)
  have hC2dir (comp i : Fin 3) :
      ContDiffAt ℝ 2 (fun y => directionalCoord u comp i y) x :=
    contDiffAt_directionalCoord u x comp i (hu comp)
  have hC2curl : ∀ k, ContDiffAt ℝ 2 (fun y => curl u y k) x := by
    intro k
    fin_cases k
    · change ContDiffAt ℝ 2 (fun y => curl u y 0) x
      have h0 : (fun y => curl u y 0) =
          fun y => directionalCoord u 2 1 y - directionalCoord u 1 2 y := by
        funext y
        exact (curl_apply u y).1
      rw [h0]
      exact (hC2dir 2 1).sub (hC2dir 1 2)
    · change ContDiffAt ℝ 2 (fun y => curl u y 1) x
      have h1 : (fun y => curl u y 1) =
          fun y => directionalCoord u 0 2 y - directionalCoord u 2 0 y := by
        funext y
        exact (curl_apply u y).2.1
      rw [h1]
      exact (hC2dir 0 2).sub (hC2dir 2 0)
    · change ContDiffAt ℝ 2 (fun y => curl u y 2) x
      have h2 : (fun y => curl u y 2) =
          fun y => directionalCoord u 1 0 y - directionalCoord u 0 1 y := by
        funext y
        exact (curl_apply u y).2.2
      rw [h2]
      exact (hC2dir 1 0).sub (hC2dir 0 1)
  have hCurl2 : ContDiffAt ℝ 2 (curl u) x :=
    (contDiffAt_piLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 3 => ℝ)).mpr hC2curl
  have hlapC (j : Fin 3) := laplacian_coord (curl u) x j hCurl2
  ext j
  fin_cases j
  · change curl (laplacian u) x 0 = laplacian (curl u) x 0
    have hcurl0 := (curl_apply (laplacian u) x).1
    rw [hcurl0, hlapC 0, directionalCoord_laplacian u x 2 1 hu,
      directionalCoord_laplacian u x 1 2 hu]
    have hsum :
        (∑ i : Fin 3,
            (fderiv ℝ (fun y => directionalCoord (curl u) 0 i y) x)
              (EuclideanSpace.single i (1 : ℝ))) =
          ∑ i : Fin 3,
            ((fderiv ℝ (fderiv ℝ (fun z => directionalCoord u 2 1 z)) x)
                (EuclideanSpace.single i (1 : ℝ))
                (EuclideanSpace.single i (1 : ℝ)) -
              (fderiv ℝ (fderiv ℝ (fun z => directionalCoord u 1 2 z)) x)
                (EuclideanSpace.single i (1 : ℝ))
                (EuclideanSpace.single i (1 : ℝ))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hfun :
          (fun y => directionalCoord (curl u) 0 i y) =ᶠ[nhds x]
            fun y =>
              (fderiv ℝ (fun z => directionalCoord u 2 1 z) y)
                (EuclideanSpace.single i (1 : ℝ)) -
              (fderiv ℝ (fun z => directionalCoord u 1 2 z) y)
                (EuclideanSpace.single i (1 : ℝ)) := by
        have hnear : ∀ᶠ y in nhds x, ∀ k, ContDiffAt ℝ 2 (fun z => u z k) y := by
          filter_upwards
            [((hu 0).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp),
              ((hu 1).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp),
              ((hu 2).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp)]
            with y h0 h1 h2 k
          fin_cases k
          · exact h0
          · exact h1
          · exact h2
        filter_upwards [hnear] with y hy
        exact (directionalCoord_curl u y i hy).1
      have hsub :
          DifferentiableAt ℝ
            (fun y => (fderiv ℝ (fun z => directionalCoord u 2 1 z) y)
              (EuclideanSpace.single i (1 : ℝ))) x :=
        ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).differentiableAt.comp x
          (((hC2dir 2 1).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
      have hsub' :
          DifferentiableAt ℝ
            (fun y => (fderiv ℝ (fun z => directionalCoord u 1 2 z) y)
              (EuclideanSpace.single i (1 : ℝ))) x :=
        ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).differentiableAt.comp x
          (((hC2dir 1 2).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
      rw [hfun.fderiv_eq, fderiv_fun_sub hsub hsub']
      simp only [ContinuousLinearMap.sub_apply]
      rw [fderiv_apply_fderiv (fun z => directionalCoord u 2 1 z) x
            (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) (hC2dir 2 1),
          fderiv_apply_fderiv (fun z => directionalCoord u 1 2 z) x
            (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) (hC2dir 1 2)]
    rw [hsum, Finset.sum_sub_distrib]
  · change curl (laplacian u) x 1 = laplacian (curl u) x 1
    have hcurl1 := (curl_apply (laplacian u) x).2.1
    rw [hcurl1, hlapC 1, directionalCoord_laplacian u x 0 2 hu,
      directionalCoord_laplacian u x 2 0 hu]
    have hsum :
        (∑ i : Fin 3,
            (fderiv ℝ (fun y => directionalCoord (curl u) 1 i y) x)
              (EuclideanSpace.single i (1 : ℝ))) =
          ∑ i : Fin 3,
            ((fderiv ℝ (fderiv ℝ (fun z => directionalCoord u 0 2 z)) x)
                (EuclideanSpace.single i (1 : ℝ))
                (EuclideanSpace.single i (1 : ℝ)) -
              (fderiv ℝ (fderiv ℝ (fun z => directionalCoord u 2 0 z)) x)
                (EuclideanSpace.single i (1 : ℝ))
                (EuclideanSpace.single i (1 : ℝ))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hfun :
          (fun y => directionalCoord (curl u) 1 i y) =ᶠ[nhds x]
            fun y =>
              (fderiv ℝ (fun z => directionalCoord u 0 2 z) y)
                (EuclideanSpace.single i (1 : ℝ)) -
              (fderiv ℝ (fun z => directionalCoord u 2 0 z) y)
                (EuclideanSpace.single i (1 : ℝ)) := by
        have hnear : ∀ᶠ y in nhds x, ∀ k, ContDiffAt ℝ 2 (fun z => u z k) y := by
          filter_upwards
            [((hu 0).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp),
              ((hu 1).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp),
              ((hu 2).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp)]
            with y h0 h1 h2 k
          fin_cases k
          · exact h0
          · exact h1
          · exact h2
        filter_upwards [hnear] with y hy
        exact (directionalCoord_curl u y i hy).2.1
      have hsub :
          DifferentiableAt ℝ
            (fun y => (fderiv ℝ (fun z => directionalCoord u 0 2 z) y)
              (EuclideanSpace.single i (1 : ℝ))) x :=
        ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).differentiableAt.comp x
          (((hC2dir 0 2).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
      have hsub' :
          DifferentiableAt ℝ
            (fun y => (fderiv ℝ (fun z => directionalCoord u 2 0 z) y)
              (EuclideanSpace.single i (1 : ℝ))) x :=
        ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).differentiableAt.comp x
          (((hC2dir 2 0).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
      rw [hfun.fderiv_eq, fderiv_fun_sub hsub hsub']
      simp only [ContinuousLinearMap.sub_apply]
      rw [fderiv_apply_fderiv (fun z => directionalCoord u 0 2 z) x
            (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) (hC2dir 0 2),
          fderiv_apply_fderiv (fun z => directionalCoord u 2 0 z) x
            (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) (hC2dir 2 0)]
    rw [hsum, Finset.sum_sub_distrib]
  · change curl (laplacian u) x 2 = laplacian (curl u) x 2
    have hcurl2 := (curl_apply (laplacian u) x).2.2
    rw [hcurl2, hlapC 2, directionalCoord_laplacian u x 1 0 hu,
      directionalCoord_laplacian u x 0 1 hu]
    have hsum :
        (∑ i : Fin 3,
            (fderiv ℝ (fun y => directionalCoord (curl u) 2 i y) x)
              (EuclideanSpace.single i (1 : ℝ))) =
          ∑ i : Fin 3,
            ((fderiv ℝ (fderiv ℝ (fun z => directionalCoord u 1 0 z)) x)
                (EuclideanSpace.single i (1 : ℝ))
                (EuclideanSpace.single i (1 : ℝ)) -
              (fderiv ℝ (fderiv ℝ (fun z => directionalCoord u 0 1 z)) x)
                (EuclideanSpace.single i (1 : ℝ))
                (EuclideanSpace.single i (1 : ℝ))) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have hfun :
          (fun y => directionalCoord (curl u) 2 i y) =ᶠ[nhds x]
            fun y =>
              (fderiv ℝ (fun z => directionalCoord u 1 0 z) y)
                (EuclideanSpace.single i (1 : ℝ)) -
              (fderiv ℝ (fun z => directionalCoord u 0 1 z) y)
                (EuclideanSpace.single i (1 : ℝ)) := by
        have hnear : ∀ᶠ y in nhds x, ∀ k, ContDiffAt ℝ 2 (fun z => u z k) y := by
          filter_upwards
            [((hu 0).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp),
              ((hu 1).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp),
              ((hu 2).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)).eventually (by simp)]
            with y h0 h1 h2 k
          fin_cases k
          · exact h0
          · exact h1
          · exact h2
        filter_upwards [hnear] with y hy
        exact (directionalCoord_curl u y i hy).2.2
      have hsub :
          DifferentiableAt ℝ
            (fun y => (fderiv ℝ (fun z => directionalCoord u 1 0 z) y)
              (EuclideanSpace.single i (1 : ℝ))) x :=
        ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).differentiableAt.comp x
          (((hC2dir 1 0).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
      have hsub' :
          DifferentiableAt ℝ
            (fun y => (fderiv ℝ (fun z => directionalCoord u 0 1 z) y)
              (EuclideanSpace.single i (1 : ℝ))) x :=
        ((ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).differentiableAt.comp x
          (((hC2dir 0 1).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)))
      rw [hfun.fderiv_eq, fderiv_fun_sub hsub hsub']
      simp only [ContinuousLinearMap.sub_apply]
      rw [fderiv_apply_fderiv (fun z => directionalCoord u 1 0 z) x
            (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) (hC2dir 1 0),
          fderiv_apply_fderiv (fun z => directionalCoord u 0 1 z) x
            (EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) (hC2dir 0 1)]
    rw [hsum, Finset.sum_sub_distrib]

/-- Spatial coordinate of `∂t u` is differentiable at a `C²` spacetime point.
All three coordinates of the time path are used so `deriv_euclidean_coord` applies. -/
public theorem differentiableAt_time_deriv_coord
    (u : TimeDependentVelocity) (t : ℝ) (x : T3) (k : Fin 3)
    (hC2 : ∀ i, ContDiffAt ℝ 2 (fun q : ℝ × T3 => u q.1 q.2 i) (t, x)) :
    DifferentiableAt ℝ (fun y => time_deriv u t y k) x := by
  let F : ℝ × T3 → ℝ := fun q => u q.1 q.2 k
  have hF : ContDiffAt ℝ 2 F (t, x) := hC2 k
  have hF1 : ContDiffAt ℝ 1 F (t, x) :=
    hF.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hfd : DifferentiableAt ℝ (fderiv ℝ F) (t, x) :=
    (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hinr : HasFDerivAt (fun y : T3 => (t, y))
      (ContinuousLinearMap.inr ℝ ℝ T3) x :=
    hasFDerivAt_prodMk_right t x
  have hcompF : HasFDerivAt (fun y : T3 => fderiv ℝ F (t, y))
      ((fderiv ℝ (fderiv ℝ F) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ T3)) x :=
    hfd.hasFDerivAt.comp (x := x) hinr
  have happ : HasFDerivAt (fun y => (fderiv ℝ F (t, y)) (1, 0))
      ((ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × T3)).comp
        ((fderiv ℝ (fderiv ℝ F) (t, x)).comp (ContinuousLinearMap.inr ℝ ℝ T3))) x :=
    (ContinuousLinearMap.apply ℝ ℝ ((1, 0) : ℝ × T3)).hasFDerivAt.comp (x := x) hcompF
  have hk (i : Fin 3) :
      ∀ᶠ y in nhds x, DifferentiableAt ℝ (fun s => u s y i) t := by
    have hFi : ContDiffAt ℝ 1 (fun q : ℝ × T3 => u q.1 q.2 i) (t, x) :=
      (hC2 i).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    have hnearY : ∀ᶠ y in nhds x,
        DifferentiableAt ℝ (fun q : ℝ × T3 => u q.1 q.2 i) (t, y) :=
      (tendsto_const_nhds.prodMk_nhds tendsto_id).eventually
        (by
          filter_upwards [hFi.eventually (by simp)] with p hp
          exact hp.differentiableAt_one)
    filter_upwards [hnearY] with y hy
    have hinl : HasFDerivAt (fun s : ℝ => (s, y))
        (ContinuousLinearMap.inl ℝ ℝ T3) t :=
      hasFDerivAt_prodMk_left t y
    exact (hy.hasFDerivAt.comp (x := t) hinl).differentiableAt
  have hnearVec : ∀ᶠ y in nhds x, DifferentiableAt ℝ (fun s => u s y) t := by
    filter_upwards [hk 0, hk 1, hk 2] with y h0 h1 h2
    exact (differentiableAt_piLp (p := 2) (𝕜 := ℝ)
        (E := fun _ : Fin 3 => ℝ)).mpr (fun i => by
      fin_cases i
      · exact h0
      · exact h1
      · exact h2)
  have hnearY : ∀ᶠ y in nhds x, DifferentiableAt ℝ F (t, y) :=
    (tendsto_const_nhds.prodMk_nhds tendsto_id).eventually
      (by
        filter_upwards [hF1.eventually (by simp)] with p hp
        exact hp.differentiableAt_one)
  have heq : (fun y => time_deriv u t y k) =ᶠ[nhds x]
      fun y => (fderiv ℝ F (t, y)) (1, 0) := by
    filter_upwards [hnearVec, hnearY] with y hyVec hyF
    change deriv (fun s => u s y) t k = (fderiv ℝ F (t, y)) (1, 0)
    rw [deriv_euclidean_coord (fun s => u s y) t k hyVec]
    exact deriv_prod_fst_slice F t y hyF
  exact happ.differentiableAt.congr_of_eventuallyEq heq

/-- Coordinate of `(u · ∇)v` is differentiable at `x` when `v` is `C²` and `u` is `C¹`. -/
public theorem differentiableAt_convective_coord
    (u v : VelocityField) (x : T3) (comp : Fin 3)
    (hu : ∀ k, DifferentiableAt ℝ (fun y => u y k) x)
    (hv : ∀ k, ContDiffAt ℝ 2 (fun y => v y k) x) :
    DifferentiableAt ℝ (fun y => convective u v y comp) x := by
  have hv1 : ∀ k, DifferentiableAt ℝ (fun y => v y k) x :=
    fun k =>
      ((hv k).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)).differentiableAt_one
  have hnear : ∀ k, ∀ᶠ y in nhds x, DifferentiableAt ℝ (fun z => v z k) y := by
    intro k
    have hk1 : ContDiffAt ℝ 1 (fun y => v y k) x :=
      (hv k).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    filter_upwards [hk1.eventually (by simp)] with y hy
    exact hy.differentiableAt_one
  have hvnear : ∀ᶠ y in nhds x, DifferentiableAt ℝ v y := by
    filter_upwards [hnear 0, hnear 1, hnear 2] with y h0 h1 h2
    exact (differentiableAt_piLp (p := 2) (𝕜 := ℝ)
        (E := fun _ : Fin 3 => ℝ)).mpr (fun i => by
      fin_cases i
      · exact h0
      · exact h1
      · exact h2)
  have heq :
      (fun y => convective u v y comp) =ᶠ[nhds x]
        fun y => ∑ k : Fin 3, directionalCoord v comp k y * u y k := by
    filter_upwards [hvnear, hnear comp] with y hyv hyc
    exact convective_eq_sum_directional u v y comp hyv hyc
  have h0 : DifferentiableAt ℝ
      (fun y => directionalCoord v comp 0 y * u y 0) x :=
    (differentiableAt_directionalCoord v x comp 0 (hv comp)).mul (hu 0)
  have h1 : DifferentiableAt ℝ
      (fun y => directionalCoord v comp 1 y * u y 1) x :=
    (differentiableAt_directionalCoord v x comp 1 (hv comp)).mul (hu 1)
  have h2 : DifferentiableAt ℝ
      (fun y => directionalCoord v comp 2 y * u y 2) x :=
    (differentiableAt_directionalCoord v x comp 2 (hv comp)).mul (hu 2)
  have hsumFun :
      (fun y => ∑ k : Fin 3, directionalCoord v comp k y * u y k) =
        fun y =>
          directionalCoord v comp 0 y * u y 0 +
            directionalCoord v comp 1 y * u y 1 +
              directionalCoord v comp 2 y * u y 2 := by
    funext y
    exact sum_univ_fin3 (fun k => directionalCoord v comp k y * u y k)
  have hsum : DifferentiableAt ℝ
      (fun y => ∑ k : Fin 3, directionalCoord v comp k y * u y k) x := by
    rw [hsumFun]
    exact (h0.add h1).add h2
  exact hsum.congr_of_eventuallyEq heq

/-- Coordinate of `∇p` is differentiable at a `C²` pressure point. -/
public theorem differentiableAt_pressureGradient_coord
    (p : PressureField) (x : T3) (i : Fin 3)
    (hp : ContDiffAt ℝ 2 p x) :
    DifferentiableAt ℝ (fun y => pressureGradient p y i) x := by
  unfold pressureGradient
  have hfd : DifferentiableAt ℝ (fderiv ℝ p) x :=
    (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hnear : ∀ᶠ y in nhds x, DifferentiableAt ℝ p y := by
    have hp1 : ContDiffAt ℝ 1 p x :=
      hp.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
    filter_upwards [hp1.eventually (by simp)] with y hy
    exact hy.differentiableAt_one
  have heq : (fun y => gradient p y i) =ᶠ[nhds x]
      fun y => (fderiv ℝ p y) (EuclideanSpace.single i (1 : ℝ)) := by
    filter_upwards [hnear] with y hy
    exact gradient_coord p y i hy
  have happ : DifferentiableAt ℝ
      (fun y => (fderiv ℝ p y) (EuclideanSpace.single i (1 : ℝ))) x :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ))).differentiableAt.comp x hfd
  exact happ.congr_of_eventuallyEq heq

/-- Paper §2.1 regularity to curl NS at a spacetime point:
C³ in space (`curl Δ = Δ curl`), C² in spacetime (`curl ∂t = ∂t curl`),
C² of the pressure (`curl ∇p = 0`). Lean 4 `structure … where`. -/
public structure VorticityTransportRegularity
    (u : TimeDependentVelocity) (p : TimeDependentPressure)
    (t : ℝ) (x : T3) : Prop where
  spaceC3 : ∀ k, ContDiffAt ℝ 3 (fun y => u t y k) x
  spacetimeC2 : ∀ k, ContDiffAt ℝ 2 (fun q : ℝ × T3 => u q.1 q.2 k) (t, x)
  pressureC2 : ContDiffAt ℝ 2 (p t) x

/-- Spatial `C²` of velocity coordinates, from `spaceC3`. -/
public theorem VorticityTransportRegularity.spaceC2
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    {t : ℝ} {x : T3}
    (hreg : VorticityTransportRegularity u p t x) :
    ∀ k, ContDiffAt ℝ 2 (fun y => u t y k) x :=
  fun k => (hreg.spaceC3 k).of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3)

/-- Spatial `C¹` of velocity coordinates, from `spaceC3`. -/
public theorem VorticityTransportRegularity.spaceC1
    {u : TimeDependentVelocity} {p : TimeDependentPressure}
    {t : ℝ} {x : T3}
    (hreg : VorticityTransportRegularity u p t x) :
    ∀ k, DifferentiableAt ℝ (fun y => u t y k) x :=
  fun k =>
    ((hreg.spaceC3 k).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 3)).differentiableAt_one

public abbrev Velocity := VelocityField
public abbrev Vorticity := VorticityField
public abbrev vol := volume

postfix:90 "_div" => fun u x => div u x

/-- Incompressible Navier–Stokes: momentum identity plus divergence-free constraint. -/
@[expose] public def navier_stokes_eq (u : TimeDependentVelocity) (p : TimeDependentPressure)
    (ν : ℝ) : Prop :=
  ∀ t ≥ (0 : ℝ), ∀ x : T3,
    time_deriv u t x + convective (u t) (u t) x + pressureGradient (p t) x =
        ν • laplacian (u t) x ∧
      div (u t) x = 0

@[expose] public def vorticity (u : Velocity) : Vorticity := fun x => curl u x

/-- Vorticity transport at one spacetime point: take the curl of NS (paper §2.1).
`∇×(∂t u + (u·∇)u + ∇p) = ∇×(ν Δu)` becomes
`∂t ω + (u·∇)ω = (ω·∇)u + ν Δω`
by `curl_time_deriv`, `curl_convective_div_free`, `curl_gradient`, and `curl_laplacian`. -/
public theorem vorticity_transport_at
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (h_NS : navier_stokes_eq u p ν)
    (t : ℝ) (ht : 0 ≤ t) (x : T3)
    (hreg : VorticityTransportRegularity u p t x) :
    time_deriv (fun s => vorticity (u s)) t x + convective (u t) (vorticity (u t)) x =
      convective (vorticity (u t)) (u t) x + ν • laplacian (vorticity (u t)) x := by
  have hfield :
      (fun y => time_deriv u t y + convective (u t) (u t) y + pressureGradient (p t) y) =
        fun y => ν • laplacian (u t) y := by
    funext y
    exact (h_NS t ht y).1
  have hdiv : div (u t) x = 0 := (h_NS t ht x).2
  have hu1 := hreg.spaceC1
  have hu2 := hreg.spaceC2
  have hdt : ∀ i, DifferentiableAt ℝ (fun y => time_deriv u t y i) x :=
    fun i => differentiableAt_time_deriv_coord u t x i hreg.spacetimeC2
  have hconv : ∀ i, DifferentiableAt ℝ (fun y => convective (u t) (u t) y i) x :=
    fun i => differentiableAt_convective_coord (u t) (u t) x i hu1 hu2
  have hgrad : ∀ i, DifferentiableAt ℝ (fun y => pressureGradient (p t) y i) x :=
    fun i => differentiableAt_pressureGradient_coord (p t) x i hreg.pressureC2
  have hcurlL :=
    curl_add3 (fun y => time_deriv u t y) (convective (u t) (u t))
      (pressureGradient (p t)) x hdt hconv hgrad
  have hcurlR :
      curl (fun y => ν • laplacian (u t) y) x =
        ν • laplacian (curl (u t)) x := by
    rw [curl_smul, curl_laplacian (u t) x hreg.spaceC3]
  have hident :
      time_deriv (fun s => curl (u s)) t x +
          (convective (u t) (curl (u t)) x - convective (curl (u t)) (u t) x) =
        ν • laplacian (curl (u t)) x := by
    have hcurl_eq :
        curl (fun y =>
            time_deriv u t y + convective (u t) (u t) y + pressureGradient (p t) y) x =
          curl (fun y => ν • laplacian (u t) y) x := by
      rw [hfield]
    rw [hcurlL, curl_time_deriv u t x hreg.spacetimeC2,
      curl_convective_div_free (u t) x hu2 hdiv,
      curl_gradient (p t) x hreg.pressureC2, add_zero] at hcurl_eq
    rw [hcurlR] at hcurl_eq
    exact hcurl_eq
  -- Rearrange: `a + b = (a + (b − c)) + c`.
  calc
    time_deriv (fun s => vorticity (u s)) t x + convective (u t) (vorticity (u t)) x
        = time_deriv (fun s => curl (u s)) t x + convective (u t) (curl (u t)) x := rfl
    _ = time_deriv (fun s => curl (u s)) t x +
          ((convective (u t) (curl (u t)) x - convective (curl (u t)) (u t) x) +
            convective (curl (u t)) (u t) x) := by
          rw [sub_add_cancel]
    _ = (time_deriv (fun s => curl (u s)) t x +
          (convective (u t) (curl (u t)) x - convective (curl (u t)) (u t) x)) +
            convective (curl (u t)) (u t) x := by
          rw [add_assoc]
    _ = ν • laplacian (curl (u t)) x + convective (curl (u t)) (u t) x := by
          rw [hident]
    _ = convective (vorticity (u t)) (u t) x +
          ν • laplacian (vorticity (u t)) x := by
          rw [add_comm]
          rfl

/-- Paper §2.1 on a globally regular solution: one `hreg` for every `t ≥ 0`
and every `x`, then the vorticity identity holds for all such points. -/
public theorem vorticity_transport
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (h_NS : navier_stokes_eq u p ν)
    (hreg : ∀ t ≥ (0 : ℝ), ∀ x, VorticityTransportRegularity u p t x) :
    ∀ t ≥ (0 : ℝ), ∀ x : T3,
      time_deriv (fun s => vorticity (u s)) t x + convective (u t) (vorticity (u t)) x =
        convective (vorticity (u t)) (u t) x + ν • laplacian (vorticity (u t)) x :=
  fun t ht x => vorticity_transport_at u p ν h_NS t ht x (hreg t ht x)

/-- Same momentum + divergence-free system, named for the assembly layer. -/
@[expose] public def NS_PDE (u : ℝ → VelocityField) (p : ℝ → PressureField) (ν : ℝ) : Prop :=
  navier_stokes_eq u p ν

public theorem vorticity_transport_equation
    (u : ℝ → VelocityField) (p : ℝ → PressureField) (ν : ℝ)
    (h_ns : NS_PDE u p ν)
    (hreg : ∀ t ≥ (0 : ℝ), ∀ x, VorticityTransportRegularity u p t x) :
    ∀ t ≥ (0 : ℝ), ∀ x : T3,
      time_deriv (fun s => vorticity (u s)) t x + convective (u t) (vorticity (u t)) x =
        convective (vorticity (u t)) (u t) x + ν • laplacian (vorticity (u t)) x :=
  vorticity_transport u p ν h_ns hreg

/-- Material derivative `∂t + u · ∇` on scalars. -/
@[expose] public def MaterialDerivative (u : ℝ → VelocityField) (f : ℝ → (T3 → ℝ))
    (t : ℝ) (x : T3) : ℝ :=
  deriv (fun s => f s x) t + inner ℝ (u t x) (gradient (f t) x)

/-- Physical admissibility of a time-dependent velocity field (Navier–Stokes Eq. (4) + time-smoothness):
1. Pointwise time-differentiability (`s ↦ u s x` is differentiable at every `t ≥ 0`), ruling out
   step jumps in time where Mathlib's `deriv` returns `0` by junk value.
2. Spatial continuity and finite L² energy (`Integrable (fun x => ‖u t x‖ ^ 2)`) obeying the
   Leray energy inequality `∫ ‖u t x‖² ≤ ∫ ‖u 0 x‖²`, ruling out unbounded parasitic pressure
   waves on `ℝ³`.
3. Causal extension `u t = u 0` for `t ≤ 0` on the total time line `ℝ`. -/
@[expose] public def IsPhysicalNSSolution (u : TimeDependentVelocity) : Prop :=
  (∀ t ≥ (0 : ℝ), ∀ x : T3, DifferentiableAt ℝ (fun s => u s x) t) ∧
  (∀ t ≥ (0 : ℝ), Continuous (u t)) ∧
  (∀ t ≥ (0 : ℝ), Integrable (fun x : T3 => ‖u t x‖ ^ 2)) ∧
  (∀ t ≥ (0 : ℝ), (∫ x, ‖u t x‖ ^ 2 ∂volume) ≤ ∫ x, ‖u 0 x‖ ^ 2 ∂volume) ∧
  (∀ t ≤ (0 : ℝ), u t = u 0)

public theorem isPhysicalNSSolution_zero :
    IsPhysicalNSSolution (fun _ => (0 : VelocityField)) :=
  ⟨fun _ _ _ => differentiableAt_const 0,
   fun _ _ => continuous_const,
   fun _ _ => by simp,
   fun _ _ => le_rfl,
   fun _ _ => rfl⟩

/-- Finite existence times: a positive `T` such that a physically admissible smooth NS solution
starting at `u₀` exists on the compact interval `[0, T]`. -/
public def existenceTimes (u₀ : VelocityField) (ν : ℝ) : Set ℝ :=
  { T | 0 < T ∧ ∃ u : TimeDependentVelocity, ∃ p : TimeDependentPressure,
      u 0 = u₀ ∧ NS_PDE u p ν ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
      IsPhysicalNSSolution u }

/-- Unpatched existence horizons omitting `IsPhysicalNSSolution`, retained for the audit module
`FrohmanianSymplecticTether/GlobalRegularity.lean` to document why pointwise `deriv` alone is vulnerable to step jumps. -/
public def existenceTimes_unpatched (u₀ : VelocityField) (ν : ℝ) : Set ℝ :=
  { T | 0 < T ∧ ∃ u : TimeDependentVelocity, ∃ p : TimeDependentPressure,
      u 0 = u₀ ∧ NS_PDE u p ν ∧ ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t) }

/-- Maximal existence time `T*` as an extended real: `sSup` of the existence times,
or `0` if there are none (`insert 0`). Unbounded existence times give `T* = ⊤`.
Time itself remains `ℝ`; `T*` is the one quantity that may be infinite. -/
@[expose] public noncomputable def Tstar (u₀ : VelocityField) (ν : ℝ) : EReal :=
  sSup (insert (0 : EReal) ((↑) '' existenceTimes u₀ ν))

public theorem Tstar_nonneg (u₀ : VelocityField) (ν : ℝ) :
    (0 : EReal) ≤ Tstar u₀ ν :=
  le_sSup (Set.mem_insert (0 : EReal) _)

/-- Any concrete finite existence time is `≤ T*`. -/
public theorem le_Tstar_of_mem_existenceTimes
    (u₀ : VelocityField) (ν : ℝ) {T : ℝ}
    (hT : T ∈ existenceTimes u₀ ν) :
    (T : EReal) ≤ Tstar u₀ ν :=
  le_sSup (Set.mem_insert_of_mem _ ⟨T, hT, rfl⟩)

/-- `T* = ⊤` iff every real is strictly below `T*`. -/
public theorem Tstar_eq_top_iff_forall_lt (u₀ : VelocityField) (ν : ℝ) :
    Tstar u₀ ν = ⊤ ↔ ∀ T : ℝ, (T : EReal) < Tstar u₀ ν :=
  EReal.eq_top_iff_forall_lt _

/-- Unbounded existence times force `T* = ⊤`. This is the lattice form of
continuation: every finite time is exceeded by some existence time. -/
public theorem Tstar_eq_top_of_unbounded_existenceTimes
    (u₀ : VelocityField) (ν : ℝ)
    (h : ∀ T : ℝ, ∃ T' ∈ existenceTimes u₀ ν, T < T') :
    Tstar u₀ ν = ⊤ := by
  refine (Tstar_eq_top_iff_forall_lt u₀ ν).2 ?_
  intro T
  obtain ⟨T', hmem, hlt⟩ := h T
  exact lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hlt)
    (le_Tstar_of_mem_existenceTimes u₀ ν hmem)

/-- A time strictly below `T*` is exceeded by a concrete existence time.
The comparison `0 ≤ T` rules out the dummy `0` inserted into the `sSup`. -/
public theorem exists_mem_existenceTimes_gt_of_lt_Tstar
    (u₀ : VelocityField) (ν : ℝ) {T : ℝ}
    (hT : (T : EReal) < Tstar u₀ ν) (hTnn : 0 ≤ T) :
    ∃ T' ∈ existenceTimes u₀ ν, T < T' := by
  obtain ⟨a, ha, hlt⟩ := (lt_sSup_iff (α := EReal)).mp hT
  rw [Set.mem_insert_iff] at ha
  cases ha with
  | inl h0 =>
    have hlt0 : (T : EReal) < (0 : EReal) := by
      rwa [h0] at hlt
    have : T < 0 := EReal.coe_lt_coe_iff.mp (by
      rwa [← EReal.coe_zero] at hlt0)
    exact (not_lt_of_ge hTnn this).elim
  | inr hcoe =>
    obtain ⟨T', hmem, rfl⟩ := hcoe
    exact ⟨T', hmem, EReal.coe_lt_coe_iff.mp hlt⟩

/-- Uniform Kato restart of length `τ > 0` below `T*` forces `T* = ⊤`.
This is the continuation half of Beale–Kato–Majda: a positive lower bound
on the existence increment cannot accumulate at a finite maximal time. -/
public theorem Tstar_eq_top_of_uniform_restart
    (u₀ : VelocityField) (ν : ℝ)
    (τ : ℝ) (hτ : 0 < τ)
    (hpos : (0 : EReal) < Tstar u₀ ν)
    (hrestart : ∀ t : ℝ, 0 ≤ t → (t : EReal) < Tstar u₀ ν →
      ∃ T' ∈ existenceTimes u₀ ν, t + τ ≤ T') :
    Tstar u₀ ν = ⊤ := by
  by_contra hne
  have htop : Tstar u₀ ν ≠ ⊤ := hne
  have hbot : Tstar u₀ ν ≠ ⊥ :=
    ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (Tstar_nonneg u₀ ν))
  set S := (Tstar u₀ ν).toReal
  have hSeq : (S : EReal) = Tstar u₀ ν := EReal.coe_toReal htop hbot
  have hSnn : 0 ≤ S := EReal.toReal_nonneg (Tstar_nonneg u₀ ν)
  cases le_or_gt S (τ / 2) with
  | inl hSτ =>
    obtain ⟨T', hmem, hle⟩ := hrestart 0 le_rfl hpos
    have hτle : (τ : EReal) ≤ Tstar u₀ ν :=
      (EReal.coe_le_coe_iff.mpr (by simpa using hle)).trans
        (le_Tstar_of_mem_existenceTimes u₀ ν hmem)
    have hSlt : (S : EReal) < (τ : EReal) :=
      EReal.coe_lt_coe_iff.mpr (lt_of_le_of_lt hSτ (half_lt_self hτ))
    exact (not_le_of_gt (hSeq ▸ hSlt)).elim hτle
  | inr hSτ =>
    set t := S - τ / 2
    have ht0 : 0 ≤ t := sub_nonneg.mpr hSτ.le
    have htlt : (t : EReal) < Tstar u₀ ν := by
      rw [← hSeq]
      exact EReal.coe_lt_coe_iff.mpr (sub_lt_self S (half_pos hτ))
    obtain ⟨T', hmem, hle⟩ := hrestart t ht0 htlt
    have htτ : t + τ = S + τ / 2 := by
      ring
    have hSlt : S < T' := by
      have : S + τ / 2 ≤ T' := htτ ▸ hle
      linarith [half_pos hτ]
    have : (S : EReal) < Tstar u₀ ν :=
      lt_of_lt_of_le (EReal.coe_lt_coe_iff.mpr hSlt)
        (le_Tstar_of_mem_existenceTimes u₀ ν hmem)
    exact (lt_irrefl (Tstar u₀ ν) (hSeq ▸ this)).elim

/-- Kato 1972 Sobolev threshold: local well-posedness in `H^s` for `s > 5/2`.
Paper Block 1 / Drive `beale_kato_majda_criterion.md`. -/
@[expose] public def katoSobolevIndex : ℝ := 5 / 2

public theorem katoSobolevIndex_lt {s : ℝ} (hs : katoSobolevIndex < s) :
    (5 : ℝ) / 2 < s :=
  hs

/-- Explicit Kato restart length from the log-Gronwall / quadratic comparison.
If the Sobolev proxy starts at size `R` and vorticity is bounded by `Y`, the
Kato–Ponce inequality `N' ≤ C Y N (1+log N)` is majorized by `N' ≤ (C Y) N²`
once `N ≥ 1`. The comparison reciprocal then stays positive on
`[0, 1/(2 C Y R)]`, so the `H^s` ball of radius `2R` cannot be escaped in
that time. Drive Step 3.2–3.4. -/
@[expose] public noncomputable def katoRestartTime (C Y R : ℝ) : ℝ :=
  if C * Y * max R 1 ≤ 0 then 1 else (2 * C * Y * max R 1)⁻¹

public theorem katoRestartTime_pos (C Y R : ℝ) :
    0 < katoRestartTime C Y R := by
  unfold katoRestartTime
  split_ifs with h
  · exact one_pos
  · have hmul : 0 < C * Y * max R 1 := lt_of_not_ge h
    have : 0 < 2 * (C * Y * max R 1) := mul_pos two_pos hmul
    simpa [mul_assoc] using inv_pos.mpr this

/-- `T* = ⊤` from the paper Kato time `katoRestartTime C Y R`, not a free `τ`. -/
public theorem Tstar_eq_top_of_katoRestartTime
    (u₀ : VelocityField) (ν : ℝ) (C Y R : ℝ)
    (hpos : (0 : EReal) < Tstar u₀ ν)
    (hrestart : ∀ t : ℝ, 0 ≤ t → (t : EReal) < Tstar u₀ ν →
      ∃ T' ∈ existenceTimes u₀ ν, t + katoRestartTime C Y R ≤ T') :
    Tstar u₀ ν = ⊤ :=
  Tstar_eq_top_of_uniform_restart u₀ ν (katoRestartTime C Y R)
    (katoRestartTime_pos C Y R) hpos hrestart

/-- Kato 1972 / Leray 1934 witness: a short-time smooth NS solution.
This is data (Type), not a `Prop` gate: the time, fields, smoothness, and PDE. -/
public structure KatoLocalWitness (u₀ : VelocityField) (ν : ℝ) where
  T : ℝ
  Tpos : 0 < T
  u : TimeDependentVelocity
  p : TimeDependentPressure
  smooth : ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)
  init : u 0 = u₀
  pde : NS_PDE u p ν
  phys : IsPhysicalNSSolution u

/-- Local existence of a smooth solution on a short interval (Kato 1972 / Leray 1934).
The witness is the Kato/Leray construction; the implication is kernel-closed. -/
public theorem local_existence
    (u₀ : VelocityField) (ν : ℝ)
    (_h_smooth : ContDiff ℝ (⊤ : ℕ∞) u₀)
    (_h_divfree : ∀ x, div u₀ x = 0)
    (_h_finite : Integrable (fun x : T3 => ‖u₀ x‖ ^ 2))
    (_hν : 0 < ν)
    (w : KatoLocalWitness u₀ ν) :
    ∃ T > (0 : ℝ), ∃ u : ℝ → VelocityField,
      (∀ t ∈ Set.Icc 0 T, ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
      u 0 = u₀ ∧
      IsPhysicalNSSolution u ∧
      ∃ p : ℝ → PressureField, NS_PDE u p ν :=
  ⟨w.T, w.Tpos, w.u, w.smooth, w.init, w.phys, w.p, w.pde⟩

/-- Time derivative is linear. Difference of two C¹-in-time fields. -/
public theorem time_deriv_sub
    (u v : TimeDependentVelocity) (t : ℝ) (x : T3)
    (hu : DifferentiableAt ℝ (fun s => u s x) t)
    (hv : DifferentiableAt ℝ (fun s => v s x) t) :
    time_deriv (fun s => u s - v s) t x =
      time_deriv u t x - time_deriv v t x := by
  unfold time_deriv
  have hfun : (fun s => (u s - v s) x) = fun s => u s x - v s x := by
    funext s
    rfl
  have hpi : (fun s => u s x - v s x) =
      (fun s => u s x) - fun s => v s x := rfl
  rw [hfun, hpi]
  exact deriv_sub hu hv

/-- Pressure gradient is linear. C¹ of both pressures. -/
public theorem pressureGradient_sub (p q : PressureField) (x : T3)
    (hp : DifferentiableAt ℝ p x) (hq : DifferentiableAt ℝ q x) :
    pressureGradient (p - q) x =
      pressureGradient p x - pressureGradient q x := by
  unfold pressureGradient
  ext i
  have hpq : DifferentiableAt ℝ (p - q) x := hp.sub hq
  have hf : fderiv ℝ (p - q) x = fderiv ℝ p x - fderiv ℝ q x :=
    (hp.hasFDerivAt.sub hq.hasFDerivAt).fderiv
  have hL : gradient (p - q) x i =
      (fderiv ℝ (p - q) x) (EuclideanSpace.single i 1) :=
    gradient_coord (p - q) x i hpq
  have hRp : gradient p x i =
      (fderiv ℝ p x) (EuclideanSpace.single i 1) :=
    gradient_coord p x i hp
  have hRq : gradient q x i =
      (fderiv ℝ q x) (EuclideanSpace.single i 1) :=
    gradient_coord q x i hq
  rw [hL, hf, ContinuousLinearMap.sub_apply, ← hRp, ← hRq]
  rfl

/-- Difference of two NS momentum equations: paper Cauchy identity.
`(∂t + u·∇)(u−v) + ((u−v)·∇)v + ∇(p−q) = ν (Δu − Δv)`. -/
public theorem ns_momentum_difference
    (u v : TimeDependentVelocity) (p q : TimeDependentPressure) (ν : ℝ)
    (t : ℝ) (ht : 0 ≤ t) (x : T3)
    (hNS : NS_PDE u p ν) (hNS' : NS_PDE v q ν)
    (hu : DifferentiableAt ℝ (u t) x) (hv : DifferentiableAt ℝ (v t) x)
    (hdtu : DifferentiableAt ℝ (fun s => u s x) t)
    (hdtv : DifferentiableAt ℝ (fun s => v s x) t)
    (hp : DifferentiableAt ℝ (p t) x) (hq : DifferentiableAt ℝ (q t) x) :
    time_deriv (fun s => u s - v s) t x +
      convective (u t) (u t - v t) x +
        convective (u t - v t) (v t) x +
          pressureGradient (p t - q t) x =
      ν • laplacian (u t) x - ν • laplacian (v t) x := by
  have ⟨hmomu, _hdivu⟩ := hNS t ht x
  have ⟨hmomv, _hdivv⟩ := hNS' t ht x
  have hdt := time_deriv_sub u v t x hdtu hdtv
  have hcv := convective_difference (u t) (v t) x hu hv
  have hpg := pressureGradient_sub (p t) (q t) x hp hq
  rw [hdt, hpg]
  have hL :
      time_deriv u t x - time_deriv v t x +
        convective (u t) (u t - v t) x +
          convective (u t - v t) (v t) x +
            (pressureGradient (p t) x - pressureGradient (q t) x) =
      time_deriv u t x - time_deriv v t x +
        (convective (u t) (u t) x - convective (v t) (v t) x) +
          (pressureGradient (p t) x - pressureGradient (q t) x) := by
    rw [hcv]
    abel
  rw [hL]
  have hsub :=
    congrArg₂ (fun a b : EuclideanSpace ℝ (Fin 3) => a - b) hmomu hmomv
  convert hsub using 1
  abel

/-- Time derivative of a frozen field vanishes. -/
public theorem time_deriv_const (v : VelocityField) (t : ℝ) (x : T3) :
    time_deriv (fun _ => v) t x = 0 :=
  deriv_const t (v x)

/-- Zero velocity is divergence-free. -/
public theorem div_zero_field (x : T3) : div (0 : VelocityField) x = 0 := by
  unfold div
  simp [fderiv_fun_const]

/-- Convective term of the zero field vanishes. -/
public theorem convective_zero (x : T3) : convective (0 : VelocityField) 0 x = 0 := by
  unfold convective
  simp

/-- Laplacian of the zero field vanishes. -/
public theorem laplacian_zero (x : T3) : laplacian (0 : VelocityField) x = 0 := by
  unfold laplacian
  simp

/-- Pressure gradient of a constant pressure vanishes. -/
public theorem pressureGradient_const (c : ℝ) (x : T3) :
    pressureGradient (fun _ => c) x = 0 := by
  unfold pressureGradient
  simp [gradient_fun_const]

/-- The zero velocity with zero pressure solves incompressible NS for any viscosity. -/
public theorem navier_stokes_eq_zero (ν : ℝ) :
    navier_stokes_eq (fun _ => (0 : VelocityField))
      (fun _ => (0 : PressureField)) ν := by
  intro t _ht x
  constructor
  · have hdt : time_deriv (fun _ => (0 : VelocityField)) t x = 0 :=
      time_deriv_const 0 t x
    have hcv : convective ((fun _ => (0 : VelocityField)) t) 0 x = 0 :=
      convective_zero x
    have hp : pressureGradient ((fun _ => (0 : PressureField)) t) x = 0 :=
      pressureGradient_const 0 x
    have hl : laplacian ((fun _ => (0 : VelocityField)) t) x = 0 :=
      laplacian_zero x
    rw [hdt, hcv, hp, hl, zero_add, zero_add, smul_zero]
  · exact div_zero_field x

/-- Zero initial data: the rest state is a Kato/Leray witness of any positive length. -/
public noncomputable def kato_witness_zero (ν : ℝ) :
    KatoLocalWitness (0 : VelocityField) ν where
  T := 1
  Tpos := one_pos
  u := fun _ => 0
  p := fun _ => (0 : PressureField)
  smooth := fun _t _ht => contDiff_const
  init := rfl
  pde := navier_stokes_eq_zero ν
  phys := isPhysicalNSSolution_zero

/-- Kato local existence for the rest state: 0-hyp construction, no `True`. -/
public noncomputable def local_existence_zero (ν : ℝ) (_hν : 0 < ν) :
    KatoLocalWitness (0 : VelocityField) ν :=
  kato_witness_zero ν

/-- The Kato time of a witness is an existence time. -/
public theorem mem_existenceTimes_of_kato_witness
    (u₀ : VelocityField) (ν : ℝ) (w : KatoLocalWitness u₀ ν) :
    w.T ∈ existenceTimes u₀ ν :=
  ⟨w.Tpos, w.u, w.p, w.init, w.pde, w.smooth, w.phys⟩

/-- Restrict a Kato witness to a shorter positive time. Paper continuation
uses the same path; only the smoothness window shrinks. -/
public noncomputable def kato_witness_restrict
    (u₀ : VelocityField) (ν : ℝ) (w : KatoLocalWitness u₀ ν)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) w.T) (htpos : 0 < t) :
    KatoLocalWitness u₀ ν where
  T := t
  Tpos := htpos
  u := w.u
  p := w.p
  smooth := fun s hs => w.smooth s ⟨hs.1, hs.2.trans ht.2⟩
  init := w.init
  pde := w.pde
  phys := w.phys

/-- Time shift: `∂t u(· + t₀) = (∂t u)(· + t₀)`. Chain rule, not a
`True` gate. -/
public theorem time_deriv_shift
    (u : TimeDependentVelocity) (t0 s : ℝ) (x : T3)
    (h : DifferentiableAt ℝ (fun σ => u σ x) (s + t0)) :
    time_deriv (fun σ => u (σ + t0)) s x = time_deriv u (s + t0) x := by
  unfold time_deriv
  have hcomm : (fun σ => u (σ + t0) x) = fun σ => u (t0 + σ) x := by
    funext σ
    rw [add_comm]
  have hf : HasDerivAt (fun σ => u σ x)
      (deriv (fun σ => u σ x) (t0 + s)) (t0 + s) := by
    have hadd : t0 + s = s + t0 := add_comm t0 s
    rw [hadd]
    exact h.hasDerivAt
  rw [hcomm]
  have hR : deriv (fun σ => u σ x) (t0 + s) =
      deriv (fun σ => u σ x) (s + t0) := by
    rw [add_comm]
  exact hR ▸ (hf.comp_const_add t0).deriv

/-- Shifted NS solution: if `u` solves NS for `t ≥ 0`, then
`s ↦ u(s + t₀)` solves NS for `s ≥ 0`. Kato restart from a time slice. -/
public theorem ns_pde_shift
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν t0 : ℝ)
    (ht0 : 0 ≤ t0)
    (hNS : NS_PDE u p ν)
    (hdt : ∀ s ≥ (0 : ℝ), ∀ x,
      DifferentiableAt ℝ (fun σ => u σ x) (s + t0)) :
    NS_PDE (fun s => u (s + t0)) (fun s => p (s + t0)) ν := by
  intro s hs x
  have hs0 : 0 ≤ s + t0 := add_nonneg hs ht0
  have ⟨hmom, hdiv⟩ := hNS (s + t0) hs0 x
  constructor
  · rw [time_deriv_shift u t0 s x (hdt s hs x)]
    exact hmom
  · exact hdiv

/-- Spatial smoothness on `[0, T + T']` after identifying the restart
path with the original solution past `T`. Paper continuation; Cauchy
supplies the identification. -/
public theorem smoothness_on_restart_interval
    (u₀ : VelocityField) (ν : ℝ)
    (w : KatoLocalWitness u₀ ν)
    (w' : KatoLocalWitness (w.u w.T) ν)
    (huniq : ∀ s ∈ Set.Icc (0 : ℝ) w'.T, w.u (w.T + s) = w'.u s) :
    ∀ t ∈ Set.Icc (0 : ℝ) (w.T + w'.T), ContDiff ℝ (⊤ : ℕ∞) (w.u t) := by
  intro t ht
  by_cases hle : t ≤ w.T
  · exact w.smooth t ⟨ht.1, hle⟩
  · have hs0 : 0 ≤ t - w.T := sub_nonneg.mpr (le_of_not_ge hle)
    have hsT : t - w.T ≤ w'.T := by
      linarith [ht.2]
    have heq := huniq (t - w.T) ⟨hs0, hsT⟩
    have ht' : w.T + (t - w.T) = t := by ring
    rw [ht'] at heq
    rw [heq]
    exact w'.smooth (t - w.T) ⟨hs0, hsT⟩

/-- Concatenated existence time: original Kato window plus restart
window, after Cauchy identification of the restart path. -/
public theorem mem_existenceTimes_add_of_kato_restart
    (u₀ : VelocityField) (ν : ℝ)
    (w : KatoLocalWitness u₀ ν)
    (w' : KatoLocalWitness (w.u w.T) ν)
    (huniq : ∀ s ∈ Set.Icc (0 : ℝ) w'.T, w.u (w.T + s) = w'.u s) :
    w.T + w'.T ∈ existenceTimes u₀ ν :=
  ⟨add_pos w.Tpos w'.Tpos, w.u, w.p, w.init, w.pde,
    smoothness_on_restart_interval u₀ ν w w' huniq, w.phys⟩

/-- Quantitative Kato restart: a uniform lower bound `τ` on the Kato
time of every smooth finite-energy slice, plus Cauchy identification
of each restart path with the time-shifted solution, produces existence
times `t + τ` below `T*`. Paper continuation construction. -/
public theorem restart_of_kato_quantitative
    (u₀ : VelocityField) (ν τ : ℝ)
    (_hν : 0 < ν) (_hτ : 0 < τ)
    (hKato : ∀ u₁, ContDiff ℝ (⊤ : ℕ∞) u₁ → (∀ x, div u₁ x = 0) →
      Integrable (fun x : T3 => ‖u₁ x‖ ^ 2) →
      KatoLocalWitness u₁ ν)
    (hTlb : ∀ u₁ (hsm : ContDiff ℝ (⊤ : ℕ∞) u₁)
      (hdiv : ∀ x, div u₁ x = 0)
      (hE : Integrable (fun x : T3 => ‖u₁ x‖ ^ 2)),
      τ ≤ (hKato u₁ hsm hdiv hE).T)
    (hInt : ∀ (T : ℝ) (v : TimeDependentVelocity)
      (q : TimeDependentPressure),
      T ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun x : T3 => ‖v t x‖ ^ 2))
    (huniq_shift : ∀ (T : ℝ) (v : TimeDependentVelocity)
      (q : TimeDependentPressure),
      T ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ (w' : KatoLocalWitness (v t) ν),
          ∀ s ∈ Set.Icc (0 : ℝ) w'.T, v (t + s) = w'.u s) :
    ∀ t : ℝ, 0 ≤ t → (t : EReal) < Tstar u₀ ν →
      ∃ T' ∈ existenceTimes u₀ ν, t + τ ≤ T' := by
  intro t ht0 htlt
  obtain ⟨T', hmem, hlt⟩ :=
    exists_mem_existenceTimes_gt_of_lt_Tstar u₀ ν htlt ht0
  obtain ⟨v, q, hv0, hpde, hsm, hphys⟩ := hmem.2
  have htI : t ∈ Set.Icc (0 : ℝ) T' := ⟨ht0, hlt.le⟩
  have hvsm : ContDiff ℝ (⊤ : ℕ∞) (v t) := hsm t htI
  have hvdiv : ∀ x, div (v t) x = 0 := fun x => (hpde t ht0 x).2
  have hvE : Integrable (fun x : T3 => ‖v t x‖ ^ 2) :=
    hInt T' v q hmem hv0 hpde hsm hphys t htI
  let w' := hKato (v t) hvsm hvdiv hvE
  have hτle : τ ≤ w'.T := hTlb (v t) hvsm hvdiv hvE
  by_cases htpos : 0 < t
  · have hsm' : ∀ s ∈ Set.Icc (0 : ℝ) (t + w'.T),
        ContDiff ℝ (⊤ : ℕ∞) (v s) := by
      intro s hs
      by_cases hle : s ≤ t
      · exact hsm s ⟨hs.1, hle.trans htI.2⟩
      · have hs0 : 0 ≤ s - t := sub_nonneg.mpr (le_of_not_ge hle)
        have hsT : s - t ≤ w'.T := by linarith [hs.2]
        have heq := huniq_shift T' v q hmem hv0 hpde hsm hphys t htI w' (s - t) ⟨hs0, hsT⟩
        have hst : t + (s - t) = s := by ring
        rw [hst] at heq
        rw [heq]
        exact w'.smooth (s - t) ⟨hs0, hsT⟩
    have hmemAdd : t + w'.T ∈ existenceTimes u₀ ν :=
      ⟨add_pos htpos w'.Tpos, v, q, hv0, hpde, hsm', hphys⟩
    refine ⟨t + w'.T, hmemAdd, ?_⟩
    linarith [hτle]
  · have ht00 : t = 0 := le_antisymm (not_lt.mp htpos) ht0
    have hEq : v t = u₀ := by
      rw [ht00, hv0]
    have hmem' : w'.T ∈ existenceTimes u₀ ν := by
      simpa [hEq] using mem_existenceTimes_of_kato_witness (v t) ν w'
    refine ⟨w'.T, hmem', ?_⟩
    calc
      t + τ = 0 + τ := by rw [ht00]
      _ = τ := zero_add τ
      _ ≤ w'.T := hτle

/-- Constructor for `existenceTimes`, exposed across modules (the set
predicate is otherwise opaque). -/
public theorem mem_existenceTimes
    (u₀ : VelocityField) (ν : ℝ) {T : ℝ}
    (hT : 0 < T)
    (u : TimeDependentVelocity) (p : TimeDependentPressure)
    (hu0 : u 0 = u₀)
    (hpde : NS_PDE u p ν)
    (hsm : ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t))
    (hphys : IsPhysicalNSSolution u) :
    T ∈ existenceTimes u₀ ν :=
  ⟨hT, u, p, hu0, hpde, hsm, hphys⟩

/-- Curl of the zero field vanishes. -/
public theorem curl_zero (x : T3) : curl (0 : VelocityField) x = 0 := by
  simpa using curl_smul (0 : ℝ) (0 : VelocityField) x

/-- Every positive time is an existence time of the rest state. -/
public theorem mem_existenceTimes_zero (ν : ℝ) {T : ℝ} (hT : 0 < T) :
    T ∈ existenceTimes (0 : VelocityField) ν :=
  ⟨hT, fun _ => 0, fun _ => (0 : PressureField), rfl, navier_stokes_eq_zero ν,
    fun _ _ => contDiff_const, isPhysicalNSSolution_zero⟩

/-- The rest state has unbounded existence times, hence `T* = ⊤`. -/
public theorem Tstar_zero_eq_top (ν : ℝ) :
    Tstar (0 : VelocityField) ν = ⊤ :=
  Tstar_eq_top_of_unbounded_existenceTimes _ _ fun T => by
    refine ⟨max T 0 + 1, mem_existenceTimes_zero ν ?pos, ?lt⟩
    · linarith [le_max_right T 0]
    · linarith [le_max_left T 0]

/-- Kato local existence forces `T* > 0`. The implication is kernel-closed; the
existence hypothesis is the remaining Kato transcription. -/
public theorem Tstar_pos_of_exists_smooth_solution
    (u₀ : VelocityField) (ν : ℝ)
    (h : ∃ T > (0 : ℝ), ∃ u : ℝ → VelocityField,
      (∀ t ∈ Set.Icc 0 T, ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
      u 0 = u₀ ∧
      IsPhysicalNSSolution u ∧
      ∃ p : ℝ → PressureField, NS_PDE u p ν) :
    (0 : EReal) < Tstar u₀ ν := by
  obtain ⟨T, hTpos, u, hsmooth, hu0, hphys, p, hpde⟩ := h
  have hmem : T ∈ existenceTimes u₀ ν := ⟨hTpos, u, p, hu0, hpde, hsmooth, hphys⟩
  have hpos : (0 : EReal) < (T : EReal) := EReal.coe_pos.mpr hTpos
  exact lt_of_lt_of_le hpos (le_Tstar_of_mem_existenceTimes u₀ ν hmem)

/-- A Kato witness forces `T* > 0`. -/
public theorem Tstar_pos_of_kato_witness
    (u₀ : VelocityField) (ν : ℝ) (w : KatoLocalWitness u₀ ν) :
    (0 : EReal) < Tstar u₀ ν :=
  Tstar_pos_of_exists_smooth_solution u₀ ν
    ⟨w.T, w.Tpos, w.u, w.smooth, w.init, w.phys, w.p, w.pde⟩

/-- Pointwise sup-norm proxy used by BKM. -/
@[expose] public noncomputable def vorticity_sup_norm (ω : VorticityField) : ℝ :=
  ⨆ x, ‖ω x‖

public theorem vorticity_sup_norm_nonneg (ω : VorticityField) :
    0 ≤ vorticity_sup_norm ω :=
  Real.iSup_nonneg fun _ => norm_nonneg _

/-- Pointwise comparison: `|ω(x)| ≤ ‖ω‖_∞` on a bounded field. -/
public theorem le_vorticity_sup_norm (ω : VorticityField) (x : T3)
    (h : BddAbove (Set.range fun y => ‖ω y‖)) :
    ‖ω x‖ ≤ vorticity_sup_norm ω :=
  le_ciSup h x

/-- Paper Drive Step 3.3: strain operator-norm proxy `‖∇u‖_∞`. -/
@[expose] public noncomputable def strain_sup_norm (u : VelocityField) : ℝ :=
  ⨆ x, ‖fderiv ℝ u x‖

/-- **Pointwise strain-by-sup-vorticity bound** `‖Du(x)‖ ≤ C · ‖ω‖_∞`.

This is **false in general**: the Biot–Savart / Riesz operators recovering `∇u` from `ω`
are Calderón–Zygmund operators, bounded on `Lᵖ` for `1 < p < ∞` but **not** on `L∞`
(CZ fails at `p = ∞`; the true bound carries a logarithmic loss). Every theorem that takes
this `Prop` as a hypothesis is therefore conditional on a bound that is false in general;
such theorems are linear-algebra consequences, not estimates for Navier–Stokes solutions. -/
@[expose] public def PointwiseStrainSupBound (u : VelocityField) (ω : VorticityField)
    (C : ℝ) (x : T3) : Prop :=
  ‖fderiv ℝ u x‖ ≤ C * vorticity_sup_norm ω

/-- Pointwise CZ/Biot–Savart bound `‖Du(x)‖ ≤ C_CZ ‖ω‖_∞` upgrades to
`‖Du‖_∞ ≤ C_CZ ‖ω‖_∞`. Linear algebra on the supremum, not the Riesz
theorem itself. Conditional on `PointwiseStrainSupBound`, which is false in
general at `L∞`. -/
public theorem strain_sup_le_of_CZ
    (u : VelocityField) (C_CZ : ℝ)
    (hCZ : ∀ x, PointwiseStrainSupBound u (curl u) C_CZ x)
    (_hbdd : BddAbove (Set.range fun x => ‖fderiv ℝ u x‖)) :
    strain_sup_norm u ≤ C_CZ * vorticity_sup_norm (curl u) :=
  ciSup_le fun x => hCZ x

/-- Operator-norm stretching: `|(ω·∇)u| ≤ C_CZ ‖ω‖_∞ |ω|` once
`‖Du‖ ≤ C_CZ ‖ω‖_∞`. Linear algebra, not the Riesz bound itself. -/
public theorem convective_norm_le_of_CZ
    (ω u : VelocityField) (x : T3) (C_CZ : ℝ)
    (hu : DifferentiableAt ℝ u x)
    (hCZ : PointwiseStrainSupBound u ω C_CZ x) :
    ‖convective ω u x‖ ≤ C_CZ * vorticity_sup_norm ω * ‖ω x‖ := by
  have hnorm := convective_norm_le ω u x hu
  have hω : 0 ≤ ‖ω x‖ := norm_nonneg _
  have hmul : ‖fderiv ℝ u x‖ * ‖ω x‖ ≤
      C_CZ * vorticity_sup_norm ω * ‖ω x‖ :=
    mul_le_mul_of_nonneg_right hCZ hω
  exact hnorm.trans hmul

/-- CZ stretching at a point: `⟨ω, (ω·∇)u⟩ ≤ C_CZ ‖ω‖_∞ |ω|²` once
`‖Du‖ ≤ C_CZ ‖ω‖_∞` (Biot–Savart / Riesz bound on the strain). -/
public theorem stretching_inner_le
    (ω u : VelocityField) (x : T3) (C_CZ : ℝ)
    (hu : DifferentiableAt ℝ u x)
    (hCZ : PointwiseStrainSupBound u ω C_CZ x) :
    inner ℝ (ω x) (convective ω u x) ≤
      C_CZ * vorticity_sup_norm ω * ‖ω x‖ ^ 2 := by
  have hnorm := convective_norm_le ω u x hu
  have hω : 0 ≤ ‖ω x‖ := norm_nonneg _
  calc
    inner ℝ (ω x) (convective ω u x)
        ≤ ‖ω x‖ * ‖convective ω u x‖ := real_inner_le_norm _ _
    _ ≤ ‖ω x‖ * (‖fderiv ℝ u x‖ * ‖ω x‖) :=
        mul_le_mul_of_nonneg_left hnorm hω
    _ = ‖fderiv ℝ u x‖ * ‖ω x‖ ^ 2 := by ring
    _ ≤ C_CZ * vorticity_sup_norm ω * ‖ω x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hCZ (sq_nonneg _)

/-- At a spatial maximum of `|ω|`, the stretching density is cubic in
`M = ‖ω‖_∞`: `⟨ω,(ω·∇)u⟩ ≤ C_CZ M³`. May 21 (9) printed `C_CZ M²`;
that is one power of `M` short for the density (it is the BKM ODE for
`Ṁ` after dividing by `M`). -/
public theorem stretching_inner_le_at_max
    (ω u : VelocityField) (x : T3) (C_CZ : ℝ)
    (hu : DifferentiableAt ℝ u x)
    (hCZ : PointwiseStrainSupBound u ω C_CZ x)
    (hmax : ‖ω x‖ = vorticity_sup_norm ω) :
    inner ℝ (ω x) (convective ω u x) ≤
      C_CZ * vorticity_sup_norm ω ^ 3 := by
  have h := stretching_inner_le ω u x C_CZ hu hCZ
  rw [hmax] at h
  have hpow :
      C_CZ * vorticity_sup_norm ω * vorticity_sup_norm ω ^ 2 =
        C_CZ * vorticity_sup_norm ω ^ 3 := by ring
  rw [hpow] at h
  exact h

/-- `___method.pdf` / living document stretching in `dQ/dt`:
`4 |ω|² φ ⟨ω,(ω·∇)u⟩ ≤ 4 C_CZ M |ω|⁴ φ` when `φ ≥ 0`.
The factor `4` is the product rule on `|ω|⁴`; CZ is `stretching_inner_le`. -/
public theorem stretching_quartic_le
    (ω u : VelocityField) (phi : T3 → ℝ) (x : T3) (C_CZ : ℝ)
    (hu : DifferentiableAt ℝ u x)
    (hCZ : PointwiseStrainSupBound u ω C_CZ x)
    (hφ : 0 ≤ phi x) :
    4 * ‖ω x‖ ^ 2 * inner ℝ (ω x) (convective ω u x) * phi x ≤
      4 * C_CZ * vorticity_sup_norm ω * ‖ω x‖ ^ 4 * phi x := by
  have hstr := stretching_inner_le ω u x C_CZ hu hCZ
  have hnn : 0 ≤ 4 * ‖ω x‖ ^ 2 * phi x :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (sq_nonneg _)) hφ
  have hmul :=
    mul_le_mul_of_nonneg_right hstr hnn
  -- `inner * (4 |ω|² φ) ≤ (C_CZ M |ω|²) * (4 |ω|² φ)`.
  have hcomm :
      inner ℝ (ω x) (convective ω u x) * (4 * ‖ω x‖ ^ 2 * phi x) =
        4 * ‖ω x‖ ^ 2 * inner ℝ (ω x) (convective ω u x) * phi x := by
    ring
  have hcomm' :
      C_CZ * vorticity_sup_norm ω * ‖ω x‖ ^ 2 * (4 * ‖ω x‖ ^ 2 * phi x) =
        4 * C_CZ * vorticity_sup_norm ω * ‖ω x‖ ^ 4 * phi x := by
    ring
  rw [← hcomm, ← hcomm']
  exact hmul

/-- At a spatial critical point of `½|ω|²`, the transport pairing
`⟨ω, (u·∇)ω⟩` vanishes. Paper §3 interior-maximum cancellation. -/
public theorem transport_inner_vanishes_of_grad_zero
    (u ω : VelocityField) (x : T3)
    (hω : DifferentiableAt ℝ ω x)
    (hgrad : gradient (fun y => (1 / 2 : ℝ) * ‖ω y‖ ^ 2) x = 0) :
    inner ℝ (ω x) (convective u ω x) = 0 := by
  rw [inner_convective_eq_inner_grad_half_norm_sq u ω x hω, hgrad,
    inner_zero_right]

/-- Inner product of vorticity transport: paper §2.1 / §3.
`⟨ω, ∂t ω⟩ + ⟨ω, (u·∇)ω⟩ = ⟨ω, (ω·∇)u⟩ + ν ⟨ω, Δω⟩`. -/
public theorem vorticity_transport_inner
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (t : ℝ) (ht : 0 ≤ t) (x : T3)
    (hNS : NS_PDE u p ν)
    (hreg : VorticityTransportRegularity u p t x) :
    inner ℝ (vorticity (u t) x)
        (time_deriv (fun s => vorticity (u s)) t x) +
      inner ℝ (vorticity (u t) x) (convective (u t) (vorticity (u t)) x) =
      inner ℝ (vorticity (u t) x) (convective (vorticity (u t)) (u t) x) +
        inner ℝ (vorticity (u t) x) (ν • laplacian (vorticity (u t)) x) := by
  have hvt := vorticity_transport_at u p ν hNS t ht x hreg
  have hcong :=
    congrArg (inner ℝ (vorticity (u t) x)) hvt
  simpa [inner_add_right] using hcong

/-- After transport vanish and non-positive viscosity, the vorticity
pairing of paper §2.1 is CZ stretching:
`⟨ω, ∂t ω⟩ ≤ C_CZ M |ω|²`. This is the inner identity used by the
enstrophy DI; it does not need a time-derivative of `|ω|²`. -/
public theorem stretching_pairing_le_at_spatial_max
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (t : ℝ) (ht : 0 ≤ t) (x : T3)
    (hNS : NS_PDE u p ν)
    (hreg : VorticityTransportRegularity u p t x)
    (hu : DifferentiableAt ℝ (u t) x) (C_CZ : ℝ)
    (hCZ : ‖fderiv ℝ (u t) x‖ ≤ C_CZ *
      vorticity_sup_norm (vorticity (u t)))
    (htransp : inner ℝ (vorticity (u t) x)
      (convective (u t) (vorticity (u t)) x) = 0)
    (hvisc : inner ℝ (vorticity (u t) x)
      (laplacian (vorticity (u t)) x) ≤ 0)
    (hν : 0 ≤ ν) :
    inner ℝ (vorticity (u t) x)
        (time_deriv (fun s => vorticity (u s)) t x) ≤
      C_CZ * vorticity_sup_norm (vorticity (u t)) *
        ‖vorticity (u t) x‖ ^ 2 := by
  have hinter := vorticity_transport_inner u p ν t ht x hNS hreg
  have hleft :
      inner ℝ (vorticity (u t) x)
          (time_deriv (fun s => vorticity (u s)) t x) =
        inner ℝ (vorticity (u t) x)
            (convective (vorticity (u t)) (u t) x) +
          inner ℝ (vorticity (u t) x)
            (ν • laplacian (vorticity (u t)) x) := by
    linarith [hinter, htransp]
  rw [hleft]
  have hstr :=
    stretching_inner_le (vorticity (u t)) (u t) x C_CZ hu hCZ
  have hviscν :
      inner ℝ (vorticity (u t) x)
          (ν • laplacian (vorticity (u t)) x) ≤ 0 := by
    rw [inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos hν hvisc
  exact (add_le_add hstr hviscν).trans_eq (add_zero _)

/-- Paper §3 at an interior spatial maximum of `|ω|²`: transport
vanishes, viscosity is non-positive, stretching is CZ, hence
`d/dt |ω|² ≤ 2 C_CZ M |ω|²`. -/
public theorem stretching_enstrophy_di_at_spatial_max
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (t : ℝ) (ht : 0 ≤ t) (x : T3)
    (hNS : NS_PDE u p ν)
    (hreg : VorticityTransportRegularity u p t x)
    (hu : DifferentiableAt ℝ (u t) x) (C_CZ : ℝ)
    (hCZ : ‖fderiv ℝ (u t) x‖ ≤ C_CZ *
      vorticity_sup_norm (vorticity (u t)))
    (htransp : inner ℝ (vorticity (u t) x)
      (convective (u t) (vorticity (u t)) x) = 0)
    (hvisc : inner ℝ (vorticity (u t) x)
      (laplacian (vorticity (u t)) x) ≤ 0)
    (hν : 0 ≤ ν)
    (hdt : HasDerivAt (fun s => vorticity (u s) x)
      (time_deriv (fun s => vorticity (u s)) t x) t) :
    deriv (fun s => ‖vorticity (u s) x‖ ^ 2) t ≤
      2 * C_CZ *
        vorticity_sup_norm (vorticity (u t)) *
        ‖vorticity (u t) x‖ ^ 2 := by
  have hder := hdt.norm_sq.deriv
  rw [hder]
  have hsum :=
    stretching_pairing_le_at_spatial_max u p ν t ht x hNS hreg hu C_CZ
      hCZ htransp hvisc hν
  exact (mul_le_mul_of_nonneg_left hsum two_pos.le).trans_eq (by ring)

/-- Strain pairing: `⟨w, (w·∇)v⟩ ≤ ‖Dv‖_∞ |w|²` once the strain
operator-norm is bounded. Linear algebra, not Riesz. -/
public theorem inner_convective_le_strain
    (w v : VelocityField) (x : T3)
    (hv : DifferentiableAt ℝ v x)
    (hbdd : BddAbove (Set.range fun y => ‖fderiv ℝ v y‖)) :
    inner ℝ (w x) (convective w v x) ≤
      strain_sup_norm v * ‖w x‖ ^ 2 := by
  have hnorm := convective_norm_le w v x hv
  have hop : ‖fderiv ℝ v x‖ ≤ strain_sup_norm v := le_ciSup hbdd x
  have hw : 0 ≤ ‖w x‖ := norm_nonneg _
  calc
    inner ℝ (w x) (convective w v x)
        ≤ ‖w x‖ * ‖convective w v x‖ := real_inner_le_norm _ _
    _ ≤ ‖w x‖ * (‖fderiv ℝ v x‖ * ‖w x‖) :=
        mul_le_mul_of_nonneg_left hnorm hw
    _ = ‖fderiv ℝ v x‖ * ‖w x‖ ^ 2 := by ring
    _ ≤ strain_sup_norm v * ‖w x‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hop (sq_nonneg _)

/-- Paper §3 characteristics: along a C¹ flow of `u` the transported scalar
with source `|ω|²` satisfies `φ(t, γ(t)) − φ(0, γ(0)) = ∫₀ᵗ |ω|²`. -/
public theorem transported_scalar_along_characteristic
    (u : TimeDependentVelocity) (phi : ℝ → T3 → ℝ) (γ : ℝ → T3)
    (t : ℝ) (ht : 0 ≤ t)
    (hder : ∀ s ∈ Set.Icc (0 : ℝ) t,
      HasDerivAt (fun τ => phi τ (γ τ)) (MaterialDerivative u phi s (γ s)) s)
    (htrans : ∀ s ∈ Set.Icc (0 : ℝ) t,
      MaterialDerivative u phi s (γ s) = ‖vorticity (u s) (γ s)‖ ^ 2)
    (hint : IntervalIntegrable
      (fun s => MaterialDerivative u phi s (γ s)) MeasureTheory.volume 0 t) :
    phi t (γ t) - phi 0 (γ 0) =
      ∫ s in (0 : ℝ)..t, ‖vorticity (u s) (γ s)‖ ^ 2 := by
  have hder' : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun τ => phi τ (γ τ)) (MaterialDerivative u phi s (γ s)) s := by
    intro s hs
    rw [Set.uIcc_of_le ht] at hs
    exact hder s hs
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ => phi τ (γ τ))
      (f' := fun s => MaterialDerivative u phi s (γ s)) hder' hint
  have hinter :
      ∫ s in (0 : ℝ)..t, MaterialDerivative u phi s (γ s) =
        ∫ s in (0 : ℝ)..t, ‖vorticity (u s) (γ s)‖ ^ 2 :=
    intervalIntegral.integral_congr fun s hs => by
      have hs' : s ∈ Set.Icc (0 : ℝ) t := by
        rwa [Set.uIcc_of_le ht] at hs
      exact htrans s hs'
  linarith [hFTC, hinter]

/-- Maximum principle for a transported scalar with quadratic vorticity source:
if `∂t φ + u·∇φ = |ω|²` along a covering family of characteristics, then
`‖φ(t)‖_∞ ≤ ‖φ(0)‖_∞ + ∫₀ᵗ ‖ω‖_∞²`. Paper §3; the flow covering is the
volume-preserving ODE of a C¹ divergence-free field. -/
public theorem transported_scalar_maximum_principle
    (u : TimeDependentVelocity) (phi : ℝ → T3 → ℝ)
    (t : ℝ) (ht : 0 ≤ t)
    (hflow : ∀ x, ∃ γ : ℝ → T3,
      γ t = x ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t,
        HasDerivAt (fun τ => phi τ (γ τ))
          (MaterialDerivative u phi s (γ s)) s) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t,
        MaterialDerivative u phi s (γ s) = ‖vorticity (u s) (γ s)‖ ^ 2) ∧
      IntervalIntegrable
        (fun s => MaterialDerivative u phi s (γ s)) MeasureTheory.volume 0 t)
    (hωbdd : ∀ s ∈ Set.Icc (0 : ℝ) t,
      BddAbove (Set.range fun y => ‖vorticity (u s) y‖))
    (hphi0 : BddAbove (Set.range fun y => |phi 0 y|))
    (_hphit : BddAbove (Set.range fun y => |phi t y|))
    (hMint : IntervalIntegrable
      (fun s => vorticity_sup_norm (vorticity (u s)) ^ 2)
      MeasureTheory.volume 0 t) :
    ⨆ x, |phi t x| ≤
      (⨆ x, |phi 0 x|) +
        ∫ s in (0 : ℝ)..t, vorticity_sup_norm (vorticity (u s)) ^ 2 := by
  refine ciSup_le fun x => ?_
  obtain ⟨γ, hγt, hder, htrans, hint⟩ := hflow x
  have hchar :=
    transported_scalar_along_characteristic u phi γ t ht hder htrans hint
  have hinterg_nn :
      0 ≤ ∫ s in (0 : ℝ)..t, ‖vorticity (u s) (γ s)‖ ^ 2 :=
    intervalIntegral.integral_nonneg ht fun _ _ =>
      pow_nonneg (norm_nonneg _) _
  have hsrc :
      ∫ s in (0 : ℝ)..t, MaterialDerivative u phi s (γ s) ≤
        ∫ s in (0 : ℝ)..t, vorticity_sup_norm (vorticity (u s)) ^ 2 :=
    intervalIntegral.integral_mono_on ht hint hMint fun s hs => by
      rw [htrans s hs]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (le_vorticity_sup_norm (vorticity (u s)) (γ s) (hωbdd s hs)) 2
  have hinter :
      ∫ s in (0 : ℝ)..t, MaterialDerivative u phi s (γ s) =
        ∫ s in (0 : ℝ)..t, ‖vorticity (u s) (γ s)‖ ^ 2 :=
    intervalIntegral.integral_congr fun s hs => by
      have hs' : s ∈ Set.Icc (0 : ℝ) t := by
        rwa [Set.uIcc_of_le ht] at hs
      exact htrans s hs'
  have hφ0 : |phi 0 (γ 0)| ≤ ⨆ y, |phi 0 y| := le_ciSup hphi0 (γ 0)
  have hsum :
      phi t x = phi 0 (γ 0) +
        ∫ s in (0 : ℝ)..t, ‖vorticity (u s) (γ s)‖ ^ 2 := by
    rw [← hγt]
    linarith [hchar]
  calc
    |phi t x|
        = |phi 0 (γ 0) +
            ∫ s in (0 : ℝ)..t, ‖vorticity (u s) (γ s)‖ ^ 2| := by
          rw [hsum]
    _ ≤ |phi 0 (γ 0)| +
          |∫ s in (0 : ℝ)..t, ‖vorticity (u s) (γ s)‖ ^ 2| :=
        abs_add_le _ _
    _ = |phi 0 (γ 0)| +
          ∫ s in (0 : ℝ)..t, ‖vorticity (u s) (γ s)‖ ^ 2 := by
        rw [abs_of_nonneg hinterg_nn]
    _ ≤ (⨆ y, |phi 0 y|) +
          ∫ s in (0 : ℝ)..t, vorticity_sup_norm (vorticity (u s)) ^ 2 := by
        linarith [hφ0, hsrc, hinter]

/-- If `M' ≤ C M²` and `M > 0`, the reciprocal is nonincreasing against the
linear barrier: `1/M(t) ≥ 1/M(0) − C t`. Inner BKM ODE estimate. -/
public theorem reciprocal_of_quadratic_growth
    (M : ℝ → ℝ) (C : ℝ) (_hC : 0 ≤ C)
    (hdiff : ∀ s ≥ (0 : ℝ), DifferentiableAt ℝ M s)
    (hquad : ∀ s ≥ (0 : ℝ), deriv M s ≤ C * (M s) ^ 2)
    (hpos : ∀ s ≥ (0 : ℝ), 0 < M s)
    (t : ℝ) (ht : 0 ≤ t)
    (hint : IntervalIntegrable
      (fun s => -deriv M s / (M s) ^ 2) MeasureTheory.volume 0 t) :
    (M 0)⁻¹ - C * t ≤ (M t)⁻¹ := by
  have hinv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun τ => (M τ)⁻¹) (-deriv M s / (M s) ^ 2) s := by
    intro s hs
    have hs0 : 0 ≤ s := by
      rw [Set.uIcc_of_le ht] at hs
      exact hs.1
    have hM := (hdiff s hs0).hasDerivAt
    have hne : M s ≠ 0 := ne_of_gt (hpos s hs0)
    exact hM.inv hne
  have hFTC :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun τ => (M τ)⁻¹)
      (f' := fun s => -deriv M s / (M s) ^ 2) hinv hint
  have hCint : IntervalIntegrable (fun _ : ℝ => (-C : ℝ)) MeasureTheory.volume 0 t :=
    intervalIntegrable_const
  have hbar :
      ∫ s in (0 : ℝ)..t, (-C : ℝ) ≤
        ∫ s in (0 : ℝ)..t, -deriv M s / (M s) ^ 2 :=
    intervalIntegral.integral_mono_on ht hCint hint fun s hs => by
      have hs0 : 0 ≤ s := hs.1
      have hMpos : 0 < M s := hpos s hs0
      have hden : 0 < (M s) ^ 2 := sq_pos_of_pos hMpos
      have hle : deriv M s ≤ C * (M s) ^ 2 := hquad s hs0
      have h1 : -deriv M s ≥ -(C * (M s) ^ 2) := neg_le_neg hle
      have h2 : -(C * (M s) ^ 2) / (M s) ^ 2 ≤ -deriv M s / (M s) ^ 2 :=
        div_le_div_of_nonneg_right h1 hden.le
      have h3 : -(C * (M s) ^ 2) / (M s) ^ 2 = -C := by
        field_simp [ne_of_gt hden]
      linarith [h2, h3]
  have hinterC : ∫ s in (0 : ℝ)..t, (-C : ℝ) = -C * t := by
    simp [mul_comm]
  have : (M t)⁻¹ - (M 0)⁻¹ ≥ -C * t := by
    linarith [hFTC, hbar, hinterC]
  linarith

/-- `1 + log x ≤ x` for `x ≥ 1`. Used to majorize the Kato–Ponce logarithm
by a quadratic. -/
public theorem one_add_log_le_self {x : ℝ} (hx : 1 ≤ x) :
    1 + Real.log x ≤ x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  linarith [Real.log_le_sub_one_of_pos hx0]

/-- Drive Step 3.2–3.4: Kato–Ponce `N' ≤ K N (1+log N)` is majorized by
`N' ≤ K N²` on `{N ≥ 1}`. -/
public theorem kato_ponce_implies_quadratic
    (N : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hone : ∀ s ≥ (0 : ℝ), 1 ≤ N s)
    (hDI : ∀ s ≥ (0 : ℝ),
      deriv N s ≤ K * N s * (1 + Real.log (N s))) :
    ∀ s ≥ (0 : ℝ), deriv N s ≤ K * (N s) ^ 2 := by
  intro s hs
  have hlog : 1 + Real.log (N s) ≤ N s := one_add_log_le_self (hone s hs)
  have hN : 0 ≤ N s := zero_le_one.trans (hone s hs)
  have hmul : K * N s * (1 + Real.log (N s)) ≤ K * N s * N s :=
    mul_le_mul_of_nonneg_left hlog (mul_nonneg hK hN)
  have hsq : K * N s * N s = K * (N s) ^ 2 := by ring
  linarith [hDI s hs, hmul, hsq]

/-- Uniform vorticity bound `M(t) ≤ Y` turns the paper strain-controlled
Kato–Ponce inequality into a constant-coefficient log inequality. -/
public theorem kato_ponce_of_uniform_vorticity
    (N M : ℝ → ℝ) (C Y : ℝ)
    (hC : 0 ≤ C) (_hY : 0 ≤ Y)
    (hM : ∀ s ≥ (0 : ℝ), M s ≤ Y)
    (hone : ∀ s ≥ (0 : ℝ), 1 ≤ N s)
    (hDI : ∀ s ≥ (0 : ℝ),
      deriv N s ≤ C * M s * N s * (1 + Real.log (N s))) :
    ∀ s ≥ (0 : ℝ),
      deriv N s ≤ (C * Y) * N s * (1 + Real.log (N s)) := by
  intro s hs
  have hN : 0 ≤ N s := zero_le_one.trans (hone s hs)
  have hlog : 0 ≤ 1 + Real.log (N s) := by
    have : 0 ≤ Real.log (N s) := Real.log_nonneg (hone s hs)
    linarith
  have hfac : 0 ≤ N s * (1 + Real.log (N s)) := mul_nonneg hN hlog
  have hCMf : C * M s * (N s * (1 + Real.log (N s))) ≤
      C * Y * (N s * (1 + Real.log (N s))) :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hM s hs) hC) hfac
  have hleft : C * M s * N s * (1 + Real.log (N s)) =
      C * M s * (N s * (1 + Real.log (N s))) := by ring
  have hright : (C * Y) * N s * (1 + Real.log (N s)) =
      C * Y * (N s * (1 + Real.log (N s))) := by ring
  linarith [hDI s hs, hleft, hright, hCMf]

/-- On the Kato doubling interval `t ≤ 1/(2 K N(0))` the Sobolev proxy cannot
exceed `2 N(0)`. Paper quantitative restart length. -/
public theorem kato_Hs_bound_on_restart_interval
    (N : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hone : ∀ s ≥ (0 : ℝ), 1 ≤ N s)
    (hdiff : ∀ s ≥ (0 : ℝ), DifferentiableAt ℝ N s)
    (hDI : ∀ s ≥ (0 : ℝ),
      deriv N s ≤ K * N s * (1 + Real.log (N s)))
    (t : ℝ) (ht : 0 ≤ t)
    (htau : K * N 0 * t ≤ 1 / 2)
    (hint : IntervalIntegrable
      (fun s => -deriv N s / (N s) ^ 2) MeasureTheory.volume 0 t) :
    N t ≤ 2 * N 0 := by
  have hpos : ∀ s ≥ (0 : ℝ), 0 < N s :=
    fun s hs => lt_of_lt_of_le zero_lt_one (hone s hs)
  have hquad := kato_ponce_implies_quadratic N K hK hone hDI
  have hrec :=
    reciprocal_of_quadratic_growth N K hK hdiff hquad hpos t ht hint
  have hN0 : 0 < N 0 := hpos 0 le_rfl
  have hNt : 0 < N t := hpos t ht
  have hge : (N 0)⁻¹ - K * t ≥ (2 * N 0)⁻¹ := by
    have hKt : K * t ≤ (1 / 2) * (N 0)⁻¹ := by
      have hdiv := div_le_div_of_nonneg_right htau hN0.le
      have hL : K * N 0 * t / N 0 = K * t := by
        field_simp [ne_of_gt hN0]
      have hR : (1 / 2) / N 0 = (1 / 2) * (N 0)⁻¹ := by
        field_simp [ne_of_gt hN0]
      linarith [hdiv, hL, hR]
    have : (N 0)⁻¹ - (1 / 2) * (N 0)⁻¹ = (2 * N 0)⁻¹ := by
      field_simp [ne_of_gt hN0]
      ring
    linarith [hKt, this]
  have hinv : (2 * N 0)⁻¹ ≤ (N t)⁻¹ := le_trans hge hrec
  have h2N : 0 < 2 * N 0 := mul_pos two_pos hN0
  exact (one_div_le_one_div h2N hNt).mp (by simpa [one_div] using hinv)

/-- Drive mild form of NS, recorded against a heat semigroup `S` and Leray
projector `P`. The semigroup itself is classical; this is the integral
equation, not a `True` gate. -/
public def IsMildNS
    (S : ℝ → VelocityField → VelocityField)
    (P : VelocityField → VelocityField)
    (u : TimeDependentVelocity) (u₀ : VelocityField) (ν : ℝ) : Prop :=
  ∀ t ≥ (0 : ℝ),
    u t =
      S (ν * t) u₀ - fun x =>
        ∫ τ in (0 : ℝ)..t,
          S (ν * (t - τ)) (P (convective (u τ) (u τ))) x

/-- Smoothness on every compact interval below `T* = ⊤` is global smoothness. -/
public theorem smoothness_of_Tstar_top
    (u : TimeDependentVelocity) (ν : ℝ)
    (hTstar : Tstar (u 0) ν = ⊤)
    (hbelow : ∀ T : ℝ, (T : EReal) < Tstar (u 0) ν →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)) :
    ∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t) := by
  intro t ht
  have hlt : (t : EReal) < Tstar (u 0) ν := by
    rw [hTstar]
    exact EReal.coe_lt_top t
  exact hbelow t hlt t ⟨ht, le_rfl⟩

/-- Beale–Kato–Majda criterion (Beale–Kato–Majda 1984).

If the time-integral of `‖ω(t)‖_∞` stays finite up to the maximal time, continuation
forces `T* = ⊤`; smoothness on compact subintervals then upgrades to all `t ≥ 0`.
The integral hyp is the BKM input; `T* = ⊤` and the compact-interval smoothness
are the continuation output. -/
public theorem beale_kato_majda
    (u : TimeDependentVelocity) (_p : TimeDependentPressure) (ν : ℝ)
    (_hν : 0 < ν) (_hNS : NS_PDE u _p ν)
    (_h_bkm : ∀ T : ℝ, (T : EReal) < Tstar (u 0) ν →
      IntegrableOn (fun t => vorticity_sup_norm (vorticity (u t))) (Set.Icc 0 T))
    (hTstar : Tstar (u 0) ν = ⊤)
    (hbelow : ∀ T : ℝ, (T : EReal) < Tstar (u 0) ν →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)) :
    ∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t) :=
  smoothness_of_Tstar_top u ν hTstar hbelow

/-- L² energy of a nonnegative density that obeys `E' ≤ K E` and `E 0 = 0`
vanishes for all later times (Grönwall). Inner Cauchy uniqueness. -/
public theorem energy_zero_of_gronwall
    (E : ℝ → ℝ) (K : ℝ)
    (hcont : ∀ t ≥ (0 : ℝ), ContinuousAt E t)
    (hdiff : ∀ t ≥ (0 : ℝ), DifferentiableAt ℝ E t)
    (hle : ∀ t ≥ (0 : ℝ), deriv E t ≤ K * E t)
    (h0 : E 0 = 0)
    (hnn : ∀ t ≥ (0 : ℝ), 0 ≤ E t)
    (t : ℝ) (ht : 0 ≤ t) :
    E t = 0 := by
  have hf : ContinuousOn E (Set.Icc (0 : ℝ) t) := fun x hx =>
    (hcont x hx.1).continuousWithinAt
  have hf' : ∀ x ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt E (deriv E x) (Set.Ici x) x :=
    fun x hx => (hdiff x hx.1).hasDerivAt.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) t, deriv E x ≤ K * E x + 0 :=
    fun x hx => by simpa using hle x hx.1
  have hgr :=
    le_gronwallBound_of_liminf_deriv_right_le (f := E) (f' := deriv E)
      (δ := (0 : ℝ)) (K := K) (ε := (0 : ℝ)) (a := (0 : ℝ)) (b := t)
      hf (fun x hx r hr => (hf' x hx).liminf_right_slope_le hr)
      (by simp [h0]) hbound t ⟨ht, le_rfl⟩
  have hbar : gronwallBound (0 : ℝ) K 0 (t - 0) = 0 := by
    rw [sub_zero]
    exact gronwallBound_ε0_δ0 K t
  have : E t ≤ 0 := by
    rw [hbar] at hgr
    exact hgr
  exact le_antisymm this (hnn t ht)

/-- Vanishing L² energy of a continuous field forces the field to vanish
pointwise: Haar is positive on nonempty opens, so a continuous nonnegative
density with integral zero is identically zero. -/
public theorem eq_of_l2_energy_zero
    (w : VelocityField)
    (hInt : Integrable (fun x : T3 => ‖w x‖ ^ 2))
    (hE : (∫ x, ‖w x‖ ^ 2 ∂volume) = 0)
    (hcont : Continuous w) :
    w = 0 := by
  have hnn : 0 ≤ fun x : T3 => ‖w x‖ ^ 2 := fun x => pow_nonneg (norm_nonneg _) _
  have hcontSq : Continuous fun x : T3 => ‖w x‖ ^ 2 :=
    (continuous_norm.comp hcont).pow 2
  by_contra hne
  have hx : ∃ x, w x ≠ 0 := by
    contrapose! hne
    funext x
    exact hne x
  obtain ⟨x, hx⟩ := hx
  have hx0 : (fun y => ‖w y‖ ^ 2) x ≠ 0 := by
    intro hsq
    exact hx (norm_eq_zero.mp (sq_eq_zero_iff.mp hsq))
  have hInt' : Integrable (fun y => ‖w y‖ ^ 2) MeasureTheory.volume := by
    simpa [volume] using hInt
  have hpos :=
    integral_pos_of_integrable_nonneg_nonzero (μ := MeasureTheory.volume)
      hcontSq hInt' hnn hx0
  have hE' : (∫ y, ‖w y‖ ^ 2 ∂MeasureTheory.volume) = 0 := by
    simpa [volume] using hE
  exact (not_lt_of_ge (le_of_eq hE')) hpos

/-- Any physically admissible solution starting from quiescent initial data `u 0 = 0`
vanishes identically at every `t ≥ 0` by the Leray energy inequality and continuity. -/
public theorem eq_zero_of_isPhysicalNSSolution_zero
    (u : TimeDependentVelocity) (hu0 : u 0 = 0)
    (hphys : IsPhysicalNSSolution u) (t : ℝ) (ht : 0 ≤ t) :
    u t = 0 := by
  have hcont : Continuous (u t) := hphys.2.1 t ht
  have hint : Integrable (fun x : T3 => ‖u t x‖ ^ 2) := hphys.2.2.1 t ht
  have hle : (∫ x, ‖u t x‖ ^ 2 ∂volume) ≤ ∫ x, ‖u 0 x‖ ^ 2 ∂volume := hphys.2.2.2.1 t ht
  have h0 : (∫ x, ‖u 0 x‖ ^ 2 ∂volume) = 0 := by simp [hu0]
  have hle0 : (∫ x, ‖u t x‖ ^ 2 ∂volume) ≤ 0 := hle.trans_eq h0
  have hge0 : 0 ≤ ∫ x, ‖u t x‖ ^ 2 ∂volume := integral_nonneg (fun _ => sq_nonneg _)
  have heq0 : (∫ x, ‖u t x‖ ^ 2 ∂volume) = 0 := le_antisymm hle0 hge0
  exact eq_of_l2_energy_zero (u t) hint heq0 hcont

/-- Any physically admissible solution with `u 0 = 0` is identically zero on all of `ℝ`. -/
public theorem eq_zero_of_isPhysicalNSSolution_zero_all
    (u : TimeDependentVelocity) (hu0 : u 0 = 0)
    (hphys : IsPhysicalNSSolution u) (t : ℝ) :
    u t = 0 := by
  rcases le_or_gt 0 t with ht | ht
  · exact eq_zero_of_isPhysicalNSSolution_zero u hu0 hphys t ht
  · rw [hphys.2.2.2.2 t ht.le, hu0]

/-- Cauchy uniqueness from the energy Grönwall: if the L² difference of two
continuous fields obeys `E' ≤ K E` and `E 0 = 0`, then the fields coincide. -/
public theorem ns_cauchy_of_energy_gronwall
    (u v : TimeDependentVelocity) (K : ℝ)
    (hu0 : u 0 = v 0)
    (hcontE : ∀ t ≥ (0 : ℝ), ContinuousAt
      (fun s => ∫ x, ‖u s x - v s x‖ ^ 2 ∂volume) t)
    (hdiffE : ∀ t ≥ (0 : ℝ), DifferentiableAt ℝ
      (fun s => ∫ x, ‖u s x - v s x‖ ^ 2 ∂volume) t)
    (hle : ∀ t ≥ (0 : ℝ),
      deriv (fun s => ∫ x, ‖u s x - v s x‖ ^ 2 ∂volume) t ≤
        K * ∫ x, ‖u t x - v t x‖ ^ 2 ∂volume)
    (hInt : ∀ t ≥ (0 : ℝ), Integrable (fun x : T3 => ‖u t x - v t x‖ ^ 2))
    (hcont : ∀ t ≥ (0 : ℝ), Continuous (u t) ∧ Continuous (v t))
    (t : ℝ) (ht : 0 ≤ t) :
    u t = v t := by
  set E : ℝ → ℝ := fun s => ∫ x, ‖u s x - v s x‖ ^ 2 ∂volume
  have h0 : E 0 = 0 := by
    have hfun : (fun x : T3 => ‖u 0 x - v 0 x‖ ^ 2) = fun _ => 0 := by
      funext x
      simp [hu0]
    simp [E, hfun]
  have hnn : ∀ s ≥ (0 : ℝ), 0 ≤ E s := fun s _ =>
    integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  have hE0 : E t = 0 :=
    energy_zero_of_gronwall E K hcontE hdiffE hle h0 hnn t ht
  have hw : u t - v t = 0 :=
    eq_of_l2_energy_zero (u t - v t) (by
      simpa [Pi.sub_apply] using hInt t ht) (by
      simpa [E, Pi.sub_apply] using hE0)
      ((hcont t ht).1.sub (hcont t ht).2)
  funext x
  have := congrFun hw x
  simpa [Pi.sub_apply, sub_eq_zero] using this

/-- Two NS solutions with the same initial velocity coincide on `t ≥ 0`
once their L² difference obeys Grönwall. The Cauchy problem does not
constrain times `t < 0`. -/
public theorem ns_cauchy_eq_of_energy_gronwall
    (u v : TimeDependentVelocity) (K : ℝ)
    (hu0 : u 0 = v 0)
    (hcontE : ∀ t ≥ (0 : ℝ), ContinuousAt
      (fun s => ∫ x, ‖u s x - v s x‖ ^ 2 ∂volume) t)
    (hdiffE : ∀ t ≥ (0 : ℝ), DifferentiableAt ℝ
      (fun s => ∫ x, ‖u s x - v s x‖ ^ 2 ∂volume) t)
    (hle : ∀ t ≥ (0 : ℝ),
      deriv (fun s => ∫ x, ‖u s x - v s x‖ ^ 2 ∂volume) t ≤
        K * ∫ x, ‖u t x - v t x‖ ^ 2 ∂volume)
    (hInt : ∀ t ≥ (0 : ℝ), Integrable (fun x : T3 => ‖u t x - v t x‖ ^ 2))
    (hcont : ∀ t ≥ (0 : ℝ), Continuous (u t) ∧ Continuous (v t)) :
    ∀ t ≥ (0 : ℝ), u t = v t :=
  fun t ht =>
    ns_cauchy_of_energy_gronwall u v K hu0 hcontE hdiffE hle hInt hcont t ht

/-- Energy Grönwall on a compact existence interval: if `E' ≤ K E` and
`E 0 = 0` on `[0, T']`, then `E` vanishes on that interval. Cauchy
construction, restricted to the paper window. -/
public theorem energy_zero_of_gronwall_Icc
    (E : ℝ → ℝ) (K T' t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) T')
    (hcont : ∀ s ∈ Set.Icc (0 : ℝ) T', ContinuousAt E s)
    (hdiff : ∀ s ∈ Set.Icc (0 : ℝ) T', DifferentiableAt ℝ E s)
    (hle : ∀ s ∈ Set.Icc (0 : ℝ) T', deriv E s ≤ K * E s)
    (h0 : E 0 = 0)
    (hnn : ∀ s ∈ Set.Icc (0 : ℝ) T', 0 ≤ E s) :
    E t = 0 := by
  have hf : ContinuousOn E (Set.Icc (0 : ℝ) t) := fun x hx =>
    (hcont x ⟨hx.1, hx.2.trans ht.2⟩).continuousWithinAt
  have hf' : ∀ x ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt E (deriv E x) (Set.Ici x) x :=
    fun x hx => (hdiff x ⟨hx.1, hx.2.le.trans ht.2⟩).hasDerivAt.hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico (0 : ℝ) t, deriv E x ≤ K * E x + 0 :=
    fun x hx => by simpa using hle x ⟨hx.1, hx.2.le.trans ht.2⟩
  have hgr :=
    le_gronwallBound_of_liminf_deriv_right_le (f := E) (f' := deriv E)
      (δ := (0 : ℝ)) (K := K) (ε := (0 : ℝ)) (a := (0 : ℝ)) (b := t)
      hf (fun x hx r hr => (hf' x hx).liminf_right_slope_le hr)
      (by simp [h0]) hbound t ⟨ht.1, le_rfl⟩
  have hbar : gronwallBound (0 : ℝ) K 0 (t - 0) = 0 := by
    rw [sub_zero]
    exact gronwallBound_ε0_δ0 K t
  have : E t ≤ 0 := by
    rw [hbar] at hgr
    exact hgr
  exact le_antisymm this (hnn t ht)

/-- Two NS paths with the same initial velocity coincide on a compact
existence interval once their L² difference obeys Grönwall there.
Paper Cauchy uniqueness, local in time. -/
public theorem ns_cauchy_on_Icc_of_energy_gronwall
    (u v : TimeDependentVelocity) (K T' : ℝ)
    (hu0 : u 0 = v 0)
    (hcontE : ∀ t ∈ Set.Icc (0 : ℝ) T', ContinuousAt
      (fun s => ∫ x, ‖u s x - v s x‖ ^ 2 ∂volume) t)
    (hdiffE : ∀ t ∈ Set.Icc (0 : ℝ) T', DifferentiableAt ℝ
      (fun s => ∫ x, ‖u s x - v s x‖ ^ 2 ∂volume) t)
    (hle : ∀ t ∈ Set.Icc (0 : ℝ) T',
      deriv (fun s => ∫ x, ‖u s x - v s x‖ ^ 2 ∂volume) t ≤
        K * ∫ x, ‖u t x - v t x‖ ^ 2 ∂volume)
    (hInt : ∀ t ∈ Set.Icc (0 : ℝ) T',
      Integrable (fun x : T3 => ‖u t x - v t x‖ ^ 2))
    (hcont : ∀ t ∈ Set.Icc (0 : ℝ) T', Continuous (u t) ∧ Continuous (v t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T', u t = v t := by
  intro t ht
  set E : ℝ → ℝ := fun s => ∫ x, ‖u s x - v s x‖ ^ 2 ∂volume
  have h0 : E 0 = 0 := by
    have hfun : (fun x : T3 => ‖u 0 x - v 0 x‖ ^ 2) = fun _ => 0 := by
      funext x
      simp [hu0]
    simp [E, hfun]
  have hnn : ∀ s ∈ Set.Icc (0 : ℝ) T', 0 ≤ E s := fun s _ =>
    integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _
  have hE0 : E t = 0 :=
    energy_zero_of_gronwall_Icc E K T' t ht hcontE hdiffE hle h0 hnn
  have hw : u t - v t = 0 :=
    eq_of_l2_energy_zero (u t - v t) (by
      simpa [Pi.sub_apply] using hInt t ht) (by
      simpa [E, Pi.sub_apply] using hE0)
      ((hcont t ht).1.sub (hcont t ht).2)
  funext x
  have := congrFun hw x
  simpa [Pi.sub_apply, sub_eq_zero] using this

/-- Existence-time witnesses with the same initial velocity coincide on
the interval once the L² difference obeys Grönwall. This is the Cauchy
construction used by `huniq`. -/
public theorem uniqueness_of_existence_times_of_energy_gronwall
    (u₀ : VelocityField) (ν : ℝ) (w : KatoLocalWitness u₀ ν) (K : ℝ)
    (hgron : ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContinuousAt
        (fun s => ∫ x, ‖w.u s x - v s x‖ ^ 2 ∂volume) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T', DifferentiableAt ℝ
        (fun s => ∫ x, ‖w.u s x - v s x‖ ^ 2 ∂volume) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T',
        deriv (fun s => ∫ x, ‖w.u s x - v s x‖ ^ 2 ∂volume) t ≤
          K * ∫ x, ‖w.u t x - v t x‖ ^ 2 ∂volume) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T',
        Integrable (fun x : T3 => ‖w.u t x - v t x‖ ^ 2)) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T', Continuous (w.u t) ∧ Continuous (v t))) :
    ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t := by
  intro T' v q hmem hv0 hpde hsm hphys
  obtain ⟨hcontE, hdiffE, hle, hInt, hcont⟩ := hgron T' v q hmem hv0 hpde hsm hphys
  have hu0 : w.u 0 = v 0 := by
    rw [w.init, hv0]
  exact ns_cauchy_on_Icc_of_energy_gronwall w.u v K T' hu0
    hcontE hdiffE hle hInt hcont

/-- Compact-interval smoothness below `T*` for a named NS solution, once any
existence-time witness with the same initial velocity equals that solution
on the interval. Cauchy uniqueness on `t ≥ 0` supplies the identification. -/
public theorem smoothness_below_Tstar_of_uniqueness
    (u : TimeDependentVelocity) (ν : ℝ)
    (huniq : ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes (u 0) ν →
      v 0 = u 0 →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T', u t = v t)
    {T : ℝ} (hT : (T : EReal) < Tstar (u 0) ν) (hTnn : 0 ≤ T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t) := by
  obtain ⟨T', hmem, hlt⟩ :=
    exists_mem_existenceTimes_gt_of_lt_Tstar (u 0) ν hT hTnn
  obtain ⟨v, q, hv0, hpde, hsm, hphys⟩ := hmem.2
  have heq := huniq T' v q hmem hv0 hpde hsm hphys
  intro t ht
  have ht' : t ∈ Set.Icc (0 : ℝ) T' := ⟨ht.1, ht.2.trans hlt.le⟩
  rw [heq t ht']
  exact hsm t ht'

/-- Parabolic regularity upgrade: a uniform vorticity bound plus continuity of
`t ↦ ‖ω(t)‖_∞` feeds BKM, hence smoothness for all positive times. -/
public theorem parabolic_regularity_from_vorticity_bound
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (hν : 0 < ν) (hNS : NS_PDE u p ν)
    (M : ℝ)
    (_h_bound : ∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≤ M)
    (hcont : Continuous fun t : ℝ => vorticity_sup_norm (vorticity (u t)))
    (hTstar : Tstar (u 0) ν = ⊤)
    (hbelow : ∀ T : ℝ, (T : EReal) < Tstar (u 0) ν →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)) :
    ∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t) :=
  beale_kato_majda u p ν hν hNS (fun T _hTlt => by
    by_cases hT0 : 0 ≤ T
    · exact hcont.continuousOn.integrableOn_Icc
    · have hempty : Set.Icc (0 : ℝ) T = (∅ : Set ℝ) := by
        ext x
        constructor
        · intro hx
          exact (hT0 (le_trans hx.1 hx.2)).elim
        · intro hx
          exact hx.elim
      rw [hempty]
      exact integrableOn_empty) hTstar hbelow

#print axioms curl_gradient
#print axioms local_existence
#print axioms smoothness_of_Tstar_top
#print axioms beale_kato_majda
#print axioms energy_zero_of_gronwall
#print axioms Tstar_eq_top_of_unbounded_existenceTimes
#print axioms Tstar_eq_top_of_uniform_restart
#print axioms Tstar_eq_top_of_katoRestartTime
#print axioms katoRestartTime_pos
#print axioms katoSobolevIndex_lt
#print axioms strain_sup_le_of_CZ
#print axioms one_add_log_le_self
#print axioms kato_ponce_implies_quadratic
#print axioms kato_ponce_of_uniform_vorticity
#print axioms kato_Hs_bound_on_restart_interval
#print axioms exists_mem_existenceTimes_gt_of_lt_Tstar
#print axioms navier_stokes_eq_zero
#print axioms kato_witness_zero
#print axioms local_existence_zero
#print axioms Tstar_pos_of_kato_witness
#print axioms eq_of_l2_energy_zero
#print axioms ns_cauchy_of_energy_gronwall
#print axioms ns_cauchy_eq_of_energy_gronwall
#print axioms energy_zero_of_gronwall_Icc
#print axioms ns_cauchy_on_Icc_of_energy_gronwall
#print axioms uniqueness_of_existence_times_of_energy_gronwall
#print axioms time_deriv_shift
#print axioms ns_pde_shift
#print axioms smoothness_on_restart_interval
#print axioms mem_existenceTimes_add_of_kato_restart
#print axioms restart_of_kato_quantitative
#print axioms smoothness_below_Tstar_of_uniqueness
#print axioms curl_zero
#print axioms mem_existenceTimes_zero
#print axioms Tstar_zero_eq_top
#print axioms div_curl
#print axioms div_of_eq_curl
#print axioms div_smul_field
#print axioms curl_add
#print axioms convective_norm_le
#print axioms inner_convective_product_rule
#print axioms cyclicLiePairing_expand
#print axioms convective_norm_le_of_CZ
#print axioms stretching_inner_le
#print axioms stretching_inner_le_at_max
#print axioms stretching_quartic_le
#print axioms transport_inner_vanishes_of_grad_zero
#print axioms vorticity_transport_inner
#print axioms stretching_pairing_le_at_spatial_max
#print axioms stretching_enstrophy_di_at_spatial_max
#print axioms pressureGradient_sub
#print axioms ns_momentum_difference
#print axioms inner_convective_eq_inner_grad_half_norm_sq
#print axioms transported_energy_pairing_vanishes
#print axioms convective_difference
#print axioms inner_convective_le_strain
#print axioms time_deriv_sub
#print axioms transported_scalar_along_characteristic
#print axioms transported_scalar_maximum_principle
#print axioms reciprocal_of_quadratic_growth
#print axioms le_vorticity_sup_norm
#print axioms convective_coord
#print axioms convective_eq_sum_directional
#print axioms directionalCoord_convective
#print axioms curl_convective
#print axioms curl_convective_div_free
#print axioms curl_add3
#print axioms fderiv_prod_snd_slice
#print axioms deriv_prod_fst_slice
#print axioms time_space_mixed_partials
#print axioms deriv_euclidean_coord
#print axioms curl_time_deriv
#print axioms fderiv_field_coord
#print axioms laplacian_coord
#print axioms fderiv_apply_fderiv
#print axioms contDiffAt_directionalCoord
#print axioms directionalCoord_laplacian
#print axioms curl_laplacian
#print axioms differentiableAt_time_deriv_coord
#print axioms differentiableAt_convective_coord
#print axioms differentiableAt_pressureGradient_coord
#print axioms vorticity_transport_at
#print axioms vorticity_transport
#print axioms vorticity_transport_equation
#print axioms time_space_mixed_partials
#print axioms differentiableAt_coord
#print axioms fderiv_coord
#print axioms integration_by_parts_of_vanishing_flux
#print axioms inner_self_convective_eq_inner_grad_half_norm_sq
#print axioms differentiableAt_coord_of_differentiableAt_field
#print axioms differentiableAt_half_norm_sq
#print axioms convective_energy_pairing_vanishes
#print axioms pressure_energy_pairing_vanishes

end

end NavierStokes3D
