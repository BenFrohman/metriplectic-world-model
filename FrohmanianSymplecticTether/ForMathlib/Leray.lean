/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianSymplecticTether.ForMathlib.PiUL2
public import FrohmanianSymplecticTether.NS_Equations

/-!
# Leray projection from Mathlib's orthogonal projection

`LerayProj H` packages a linear, self-adjoint, idempotent operator. `LerayProj.ofSubspace K`
builds one from the orthogonal projection onto any closed subspace `K`, so the self-adjoint and
idempotent fields are theorems. `lerayL2` is the instance on `L²(ℝ³; ℝ³)` whose subspace is the
closure of smooth, compactly supported, divergence-free fields.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace ForMathlib

noncomputable section

/-- A Leray-type projection: linear, self-adjoint, idempotent. -/
public structure LerayProj (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  P : H →ₗ[ℝ] H
  symm : ∀ a b, ⟪P a, b⟫ = ⟪a, P b⟫
  idem : ∀ a, P (P a) = P a

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The orthogonal projection onto a subspace with an orthogonal projection is a `LerayProj`. -/
@[expose] public def LerayProj.ofSubspace (K : Submodule ℝ H) [K.HasOrthogonalProjection] :
    LerayProj H where
  P := K.starProjection.toLinearMap
  symm a b := Submodule.inner_starProjection_left_eq_right K a b
  idem a := by
    have h := (Submodule.isIdempotentElem_starProjection (K := K)).eq
    exact congrArg (fun f : H →L[ℝ] H => f a) h

public theorem LerayProj.ofSubspace_fixed_iff (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (v : H) : (LerayProj.ofSubspace K).P v = v ↔ v ∈ K :=
  Submodule.starProjection_eq_self_iff (K := K)

public theorem LerayProj.ofSubspace_eq_zero_iff (K : Submodule ℝ H) [K.HasOrthogonalProjection]
    (v : H) : (LerayProj.ofSubspace K).P v = 0 ↔ v ∈ Kᗮ :=
  Submodule.starProjection_apply_eq_zero_iff K

/-- Smooth, compactly supported, divergence-free fields, as `L²` classes. -/
@[expose] public def divFreeTestFields : Set L2Field :=
  {f | ∃ φ : NavierStokes3D.VelocityField, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧
    (∀ x, NavierStokes3D.div φ x = 0) ∧ ⇑f =ᵐ[NavierStokes3D.volume] φ}

/-- The closed divergence-free subspace of `L²`. -/
@[expose] public def divFreeL2 : Submodule ℝ L2Field :=
  (Submodule.span ℝ divFreeTestFields).topologicalClosure

public instance : CompleteSpace divFreeL2 :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- The Leray projection on `L²(ℝ³; ℝ³)`. -/
@[expose] public def lerayL2 : LerayProj L2Field := LerayProj.ofSubspace divFreeL2

public theorem lerayL2_fixes_test (f : L2Field) (hf : f ∈ divFreeTestFields) :
    lerayL2.P f = f :=
  (LerayProj.ofSubspace_fixed_iff _ f).2
    (Submodule.le_topologicalClosure _ (Submodule.subset_span hf))

end

end ForMathlib
