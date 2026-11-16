/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import TetherMayForm.Metriplectic

/-!
# TetherMayForm.RouteA

Machine-checked Lean 4 module.
-/

namespace Frohman.Tether

open Submodule
open scoped InnerProductSpace RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **C3, Route A (May 20).** -/
structure RouteAFeedback (S w : ℝ) (u ω : H) (B : LinearMap.BilinForm ℝ H) : Prop where
  nonpos : ∀ F, B F F ≤ 0
  maximizer_reduced : ⟪u, ω⟫ = 0
  maximizer_unit : ‖ω‖ = 1
  matches_stretching : B ω ω + S * w = 0
  jacobi_reduced : ∀ F G, ⟪u, F⟫ = 0 → ⟪u, G⟫ = 0 → antiPart B F G = 0

/-- Route A C3 implies the earlier one-direction C3, with `κ = S` fixed by matching. -/
theorem RouteAFeedback.toControllable {S w : ℝ} {u ω : H} {B : LinearMap.BilinForm ℝ H}
    (h : RouteAFeedback S w u ω B) : ProducesControllableNegativeFeedback S w u B :=
  ⟨h.nonpos, ω, h.maximizer_reduced, h.maximizer_unit, by linarith [h.matches_stretching]⟩

/-- Jacobi compatibility: on the reduced orbit the Poisson part of `P + B` is `P`. -/
theorem RouteAFeedback.poisson_unchanged {S w : ℝ} {u ω : H} {B : LinearMap.BilinForm ℝ H}
    (h : RouteAFeedback S w u ω B) (P : LinearMap.BilinForm ℝ H) (hP : ∀ F, P F F = 0)
    (F G : H) (hF : ⟪u, F⟫ = 0) (hG : ⟪u, G⟫ = 0) :
    antiPart (P + B) F G = P F G := by
  have hA : P G F = -P F G := by
    have := hP (F + G); simp [hP F, hP G] at this; linarith
  have := h.jacobi_reduced F G hF hG
  rw [antiPart_apply] at this ⊢
  simp only [LinearMap.add_apply, hA]; linarith

/-- The tether satisfies Route A C3 with `κ = S`, at any reduced unit maximizer. -/
theorem frohmanianTether_routeA {S w : ℝ} (hS : 0 ≤ S) (hw : 0 ≤ w) {u ω : H}
    (hω : ⟪u, ω⟫ = 0) (hn : ‖ω‖ = 1) : RouteAFeedback S w u ω 𝔗_F[S, w, u] where
  nonpos := frohmanianTether_self_nonpos hS hw u
  maximizer_reduced := hω
  maximizer_unit := hn
  matches_stretching := by
    rw [frohmanianTether_apply, piU_eq_self_of_inner_eq_zero hω, real_inner_self_eq_norm_sq,
      hn]; ring
  jacobi_reduced := fun F G _ _ => by rw [antiPart_frohmanianTether]; rfl

/-- Within the tether family, Route A C3 forces the coefficient to be `S w`. -/
theorem routeA_fixes_coefficient {S w : ℝ} {u ω : H} (c : ℝ)
    (h : RouteAFeedback S w u ω 𝔗_F[c, 1, u]) : c = S * w :=
  feedback_fixes_coefficient c h.toControllable

/-- **Uniqueness of the Minimal Metric Tether — Route A C3.** In dimension ≥ 3, with a
reduced unit maximizer `ω`, a symmetric correction satisfies C1, C2 and Route A C3 iff it
equals `𝔗_F[S, w, u]`: the coefficient is the stretching coefficient, by matching. -/
theorem uniqueness_routeA_iff [FiniteDimensional ℝ H] (hdim : 3 ≤ Module.finrank ℝ H)
    {S w : ℝ} (hS : 0 ≤ S) (hw : 0 ≤ w) (u ω : H) (hu : u ≠ 0)
    (hω : ⟪u, ω⟫ = 0) (hn : ‖ω‖ = 1) (B : LinearMap.BilinForm ℝ H) :
    IsAdmissibleCorrection u (RouteAFeedback S w u ω) B ↔ B = 𝔗_F[S, w, u] := by
  constructor
  · intro hB
    exact uniqueness_of_minimal_metric_tether hdim S w u hu _
      (fun c hc => routeA_fixes_coefficient c hc) B hB
  · rintro rfl
    exact frohmanianTether_admissible S w u _ (frohmanianTether_routeA hS hw hω hn)

/-- For the tether itself the two C3 versions agree (given a reduced unit maximizer). -/
theorem routeA_iff_controllable_on_tether {S w : ℝ} (hS : 0 ≤ S) (hw : 0 ≤ w) {u ω : H}
    (hω : ⟪u, ω⟫ = 0) (hn : ‖ω‖ = 1) :
    RouteAFeedback S w u ω 𝔗_F[S, w, u] ↔ ProducesControllableNegativeFeedback S w u 𝔗_F[S, w, u] :=
  ⟨RouteAFeedback.toControllable, fun _ => frohmanianTether_routeA hS hw hω hn⟩

end Frohman.Tether
