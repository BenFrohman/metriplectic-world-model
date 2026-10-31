/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# The two-part split and a non-circular canonicity theorem for the metric bracket

Proved here, with no open hypotheses:

* `split_exists_unique` (the 2-part split): every bilinear form is uniquely the sum of an
  antisymmetric part (the Lie–Poisson/2-form slot) and a symmetric part (the metric/tether slot).
* `canonical_metric_bracket` (canonicity, non-circular): on a real inner product space, a
  bilinear form `B` that is (C1) symmetric, (C2) degenerate in the direction `u`
  (`B u · = 0`), and invariant under every linear isometry fixing `u`, is forced to be
  `B x y = c ⟪Π_u x, Π_u y⟫` for a single constant `c`, where `Π_u` is the orthogonal
  projection off `span {u}`. The hypotheses never mention `Π_u` or the diagonal of `B`,
  so this does not assume its conclusion (contrast `SaturatesTetherQuadratic`).
* `canonical_metric_bracket_sign`: if additionally `B` is negative semidefinite (the tether
  sign), then `c ≤ 0` whenever `span {u}ᗮ ≠ 0`.

Scope: this is a pointwise (one-state, finite-or-infinite-dimensional linear algebra) statement.
It does not force the weight `|ω|²` or the value of `κ` in `TetherKernelVel`; that remains open.
-/

open RealInnerProductSpace

namespace MetriplecticWorldModel

/-! ## The two-part split -/

/-- The 2-part split: `B = A + S`, `A` antisymmetric, `S` symmetric, uniquely. -/
theorem split_exists_unique {V : Type*} (B : V → V → ℝ) :
    ∃! AS : (V → V → ℝ) × (V → V → ℝ),
      (∀ x y, AS.1 x y = - AS.1 y x) ∧ (∀ x y, AS.2 x y = AS.2 y x) ∧
      (∀ x y, B x y = AS.1 x y + AS.2 x y) := by
  refine ⟨(fun x y => (B x y - B y x) / 2, fun x y => (B x y + B y x) / 2),
    ⟨fun x y => by ring, fun x y => by ring, fun x y => by ring⟩, ?_⟩
  rintro ⟨A, S⟩ ⟨hA, hS, hB⟩
  simp only at hA hS hB
  have hA' : ∀ x y, A x y = (B x y - B y x) / 2 := fun x y => by
    rw [hB, hB, hA y x, hS y x]; ring
  have hS' : ∀ x y, S x y = (B x y + B y x) / 2 := fun x y => by
    rw [hB, hB, hA y x, hS y x]; ring
  ext x y <;> simp [hA', hS']

/-! ## Canonicity of the metric bracket -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Projection off `span {u}`: `Π_u x = x − (⟪u,x⟫/‖u‖²) u`. -/
noncomputable def Pi_u (u x : E) : E := x - (⟪u, x⟫ / ‖u‖ ^ 2) • u

theorem inner_Pi_u (u : E) (hu : u ≠ 0) (x : E) : ⟪u, Pi_u u x⟫ = 0 := by
  have : ‖u‖ ^ 2 ≠ 0 := by positivity
  simp only [Pi_u, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq]
  field_simp; ring

theorem Pi_u_of_inner_zero (u x : E) (h : ⟪u, x⟫ = 0) : Pi_u u x = x := by
  simp [Pi_u, h]

/-- C1 + C2 + isotropy force `B = c ⟪Π_u ·, Π_u ·⟫`. -/
theorem canonical_metric_bracket (u : E) (hu : u ≠ 0) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hsymm : ∀ x y, B x y = B y x) (hdeg : ∀ x, B u x = 0)
    (hinv : ∀ R : E ≃ₗᵢ[ℝ] E, R u = u → ∀ x y, B (R x) (R y) = B x y) :
    ∃ c : ℝ, ∀ x y, B x y = c * ⟪Pi_u u x, Pi_u u y⟫ := by
  -- Step 1: B only sees the projections.
  have hproj : ∀ x y, B x y = B (Pi_u u x) (Pi_u u y) := by
    intro x y
    have hx : x = Pi_u u x + (⟪u, x⟫ / ‖u‖ ^ 2) • u := by simp [Pi_u]
    have hy : y = Pi_u u y + (⟪u, y⟫ / ‖u‖ ^ 2) • u := by simp [Pi_u]
    conv_lhs => rw [hx, hy]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [hsymm (Pi_u u x) u]; simp [hdeg]
  -- Step 2: on `u⊥`, the quadratic form is `c ‖z‖²`.
  have hquad : ∃ c : ℝ, ∀ z, ⟪u, z⟫ = 0 → B z z = c * ‖z‖ ^ 2 := by
    by_cases hne : ∃ e : E, ⟪u, e⟫ = 0 ∧ e ≠ 0
    · obtain ⟨e₀, he₀u, he₀⟩ := hne
      set e : E := (‖e₀‖⁻¹) • e₀
      have hn : ‖e‖ = 1 := by simp [e, norm_smul, he₀]
      have heu : ⟪u, e⟫ = 0 := by simp [e, inner_smul_right, he₀u]
      refine ⟨B e e, fun z hz => ?_⟩
      set w : E := ‖z‖ • e
      have hw : ‖w‖ = ‖z‖ := by simp [w, norm_smul, hn]
      have hwu : ⟪u, w⟫ = 0 := by simp [w, inner_smul_right, heu]
      set R : E ≃ₗᵢ[ℝ] E := Submodule.reflection (ℝ ∙ (w - z))ᗮ
      have hRw : R w = z := Submodule.reflection_sub hw
      have hRu : R u = u := by
        apply Submodule.reflection_mem_subspace_eq_self
        rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
        rw [inner_sub_right, hwu, hz, sub_zero]
      have := hinv R hRu w w
      rw [hRw] at this
      rw [this]
      simp only [w, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    · push Not at hne
      exact ⟨0, fun z hz => by
        by_cases h0 : z = 0
        · simp [h0]
        · exact absurd (hne z hz) h0⟩
  obtain ⟨c, hc⟩ := hquad
  refine ⟨c, fun x y => ?_⟩
  rw [hproj]
  set a := Pi_u u x
  set b := Pi_u u y
  have ha : ⟪u, a⟫ = 0 := inner_Pi_u u hu x
  have hb : ⟪u, b⟫ = 0 := inner_Pi_u u hu y
  have hab : ⟪u, a + b⟫ = 0 := by rw [inner_add_right, ha, hb, add_zero]
  have h1 := hc (a + b) hab
  have h2 := hc a ha
  have h3 := hc b hb
  simp only [map_add, LinearMap.add_apply] at h1
  rw [hsymm b a] at h1
  have hn : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, b⟫ + ‖b‖ ^ 2 := norm_add_sq_real a b
  rw [hn] at h1
  nlinarith [h1, h2, h3]

/-- With the tether sign (`B x x ≤ 0`), the forced constant is `≤ 0` (if `u⊥ ≠ 0`). -/
theorem canonical_metric_bracket_sign (u : E) (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (c : ℝ) (hc : ∀ x y, B x y = c * ⟪Pi_u u x, Pi_u u y⟫)
    (hneg : ∀ x, B x x ≤ 0) (e : E) (he : ⟪u, e⟫ = 0) (he0 : e ≠ 0) : c ≤ 0 := by
  have h := hneg e
  rw [hc, Pi_u_of_inner_zero u e he, real_inner_self_eq_norm_sq] at h
  have : 0 < ‖e‖ ^ 2 := by positivity
  nlinarith

/-- Converse (satisfiability): `c ⟪Π_u ·, Π_u ·⟫` is symmetric and degenerate in `u`. -/
theorem Pi_u_form_symm_degen (u : E) (hu : u ≠ 0) (c : ℝ) :
    (∀ x y, c * ⟪Pi_u u x, Pi_u u y⟫ = c * ⟪Pi_u u y, Pi_u u x⟫) ∧
    (∀ y, c * ⟪Pi_u u u, Pi_u u y⟫ = 0) := by
  refine ⟨fun x y => by rw [real_inner_comm], fun y => ?_⟩
  have : Pi_u u u = 0 := by
    have : ‖u‖ ^ 2 ≠ 0 := by positivity
    simp only [Pi_u, real_inner_self_eq_norm_sq, div_self this, one_smul, sub_self]
  simp [this]

end MetriplecticWorldModel
