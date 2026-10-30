/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import FrohmanianSymplecticTether.ForMathlib.Projection

/-!
# `Π_u` on `L²` as a Mathlib orthogonal projection

`PiL2 u` is the orthogonal projection of `L²(ℝ³; ℝ³)` onto `(span{u})ᗮ`. It is a continuous
linear map, idempotent, self-adjoint, of norm at most `1`, with kernel `span{u}` and range
`(span{u})ᗮ`. On representatives it agrees almost everywhere with the pointwise formula `Pi_u`.
-/

open MeasureTheory
open scoped RealInnerProductSpace

namespace ForMathlib

noncomputable section

/-- `L²(ℝ³; ℝ³)` with the model volume. -/
public abbrev L2Field : Type :=
  Lp (EuclideanSpace ℝ (Fin 3)) 2 NavierStokes3D.volume

/-- `Π_u` on `L²`: orthogonal projection onto `(span{u})ᗮ`. -/
@[expose] public def PiL2 (u : L2Field) : L2Field →L[ℝ] L2Field :=
  (ℝ ∙ u)ᗮ.starProjection

/-- Gram–Schmidt formula. -/
public theorem PiL2_apply (u v : L2Field) :
    PiL2 u v = v - (⟪u, v⟫ / ‖u‖ ^ 2) • u := by
  simp [PiL2, Submodule.starProjection_orthogonal', Submodule.starProjection_singleton]

public theorem PiL2_add (u v w : L2Field) : PiL2 u (v + w) = PiL2 u v + PiL2 u w :=
  map_add _ v w

public theorem PiL2_smul (u v : L2Field) (c : ℝ) : PiL2 u (c • v) = c • PiL2 u v :=
  map_smul _ c v

public theorem PiL2_idem (u v : L2Field) : PiL2 u (PiL2 u v) = PiL2 u v := by
  have h := (Submodule.isIdempotentElem_starProjection (K := (ℝ ∙ u)ᗮ)).eq
  exact congrArg (fun f : L2Field →L[ℝ] L2Field => f v) h

public theorem PiL2_selfAdjoint (u v w : L2Field) : ⟪PiL2 u v, w⟫ = ⟪v, PiL2 u w⟫ :=
  Submodule.inner_starProjection_left_eq_right _ v w

public theorem PiL2_norm_le (u : L2Field) : ‖PiL2 u‖ ≤ 1 :=
  Submodule.starProjection_norm_le _

public theorem PiL2_ker (u : L2Field) : (PiL2 u).ker = ℝ ∙ u := by
  rw [PiL2, Submodule.ker_starProjection, Submodule.orthogonal_orthogonal]

public theorem PiL2_range (u : L2Field) : (PiL2 u).range = (ℝ ∙ u)ᗮ :=
  Submodule.range_starProjection _

public theorem PiL2_apply_eq_zero_iff (u v : L2Field) : PiL2 u v = 0 ↔ ∃ c : ℝ, c • u = v := by
  rw [← Submodule.mem_span_singleton, ← PiL2_ker]; rfl

/-- The pointwise `Pi_u` on representatives agrees a.e. with `PiL2`. -/
public theorem Pi_u_ae_eq_PiL2 (u v : L2Field) :
    Pi_u (⇑u) (⇑v) =ᵐ[NavierStokes3D.volume] ⇑(PiL2 u v) := by
  have hcoef : (∫ y, ArnoldGeometric.pairing (v y) (u y) ∂NavierStokes3D.volume) /
      (∫ y, ‖u y‖ ^ 2 ∂NavierStokes3D.volume) = ⟪u, v⟫ / ‖u‖ ^ 2 := by
    congr 1
    · rw [L2.inner_def]; congr 1; funext y; exact real_inner_comm _ _
    · rw [← real_inner_self_eq_norm_sq, L2.inner_def]; congr 1; funext y
      exact (real_inner_self_eq_norm_sq _).symm
  rw [PiL2_apply]
  filter_upwards [Lp.coeFn_sub v ((⟪u, v⟫ / ‖u‖ ^ 2) • u),
    Lp.coeFn_smul (⟪u, v⟫ / ‖u‖ ^ 2) u] with x h1 h2
  rw [h1, Pi.sub_apply, h2, Pi.smul_apply]
  simp only [Pi_u, hcoef]

end

end ForMathlib
