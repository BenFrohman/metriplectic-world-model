/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Stanley Frohman (prepared with assistance from Grok; not a co-author).

# Main theorem: κ derived from the stretching coefficient (May 20 2026 Route A)

At a reduced unit maximizer `ω` of `|ω|²`, the leading quadratic coefficient of the
evolution of `M = ‖ω‖_∞` is modelled as `stretching + feedback = S·w + B(ω,ω)`.
Route A C3 asks that this leading coefficient vanish (exact matching). No separate
calibration constant is assumed: `κ` is *derived* as `κ = S` (`routeA_determines_kappa`).

Model assumption (honest scope): the identification of the leading coefficient with
`S·w + B(ω,ω)` is the May 20 modelling step; it is not derived here from Navier–Stokes.
-/
import TetherMayForm.RouteA
import TetherMayForm.Layer2

namespace Frohman.Tether

open scoped InnerProductSpace RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Leading quadratic coefficient of `d/dt M` at the maximizer: stretching plus feedback. -/
def leadingCoefficient (S w : ℝ) (ω : H) (B : LinearMap.BilinForm ℝ H) : ℝ :=
  S * w + B ω ω

theorem RouteAFeedback.leadingCoefficient_eq_zero {S w : ℝ} {u ω : H}
    {B : LinearMap.BilinForm ℝ H} (h : RouteAFeedback S w u ω B) :
    leadingCoefficient S w ω B = 0 := by
  unfold leadingCoefficient; linarith [h.matches_stretching]

/-- **κ is derived, not calibrated.** If a tether `𝔗_F[κ, w, u]` (with `w ≠ 0`) satisfies
Route A C3 at `ω`, then `κ = S`. -/
theorem routeA_determines_kappa {S w κ : ℝ} (hw : w ≠ 0) {u ω : H}
    (h : RouteAFeedback S w u ω 𝔗_F[κ, w, u]) : κ = S := by
  have hm := h.matches_stretching
  rw [frohmanianTether_apply, piU_eq_self_of_inner_eq_zero h.maximizer_reduced,
    real_inner_self_eq_norm_sq, h.maximizer_unit] at hm
  have : (κ - S) * w = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · exact absurd h1 hw

/-- **Frohmanian Symplectic Tether Theorem (Route A).** In dimension ≥ 3, let `u ≠ 0`,
`ω ⟂ u` a unit maximizer direction, stretching coefficient `S ≥ 0`, weight `w > 0`.
A bilinear correction `B` satisfies C1 (invariance), C2 (degeneracy) and Route A C3
(negative feedback cancelling stretching at the maximum, Poisson part unchanged on `uᗮ`)
**iff** `B = 𝔗_F[κ, w, u]` for some `κ`, and then necessarily `κ = S`. -/
theorem frohmanian_symplectic_tether_theorem [FiniteDimensional ℝ H]
    (hdim : 3 ≤ Module.finrank ℝ H) {S w : ℝ} (hS : 0 ≤ S) (hw : 0 < w) (u ω : H)
    (hu : u ≠ 0) (hω : ⟪u, ω⟫ = 0) (hn : ‖ω‖ = 1) (B : LinearMap.BilinForm ℝ H) :
    IsAdmissibleCorrection u (RouteAFeedback S w u ω) B ↔
      ∃ κ, κ = S ∧ B = 𝔗_F[κ, w, u] := by
  constructor
  · intro hB
    have hB' := (uniqueness_routeA_iff hdim hS hw.le u ω hu hω hn B).1 hB
    subst hB'
    exact ⟨S, rfl, rfl⟩
  · rintro ⟨κ, rfl, rfl⟩
    exact (uniqueness_routeA_iff hdim hS hw.le u ω hu hω hn _).2 rfl

/-- Converse direction stated alone: any tether that is Route-A admissible has `κ = S`. -/
theorem kappa_eq_stretching_of_admissible {S w κ : ℝ} (hw : w ≠ 0) {u ω : H}
    (h : IsAdmissibleCorrection u (RouteAFeedback S w u ω) 𝔗_F[κ, w, u]) : κ = S :=
  routeA_determines_kappa hw h.c3

/-- **Layer 1 → Layer 2.** With `κ` derived from Route A (`κ = S`) and Young absorption
`ε = κ/4`, if `κ'' = κ/2 − C_abs > 0` then any `y ≥ 0` obeying `y' ≤ C y² − κ'' y³` on
`[0,T]` satisfies `y ≤ max(y(0), C/κ'')`. The differential inequality is a hypothesis. -/
theorem routeA_layer2_bound {S w κ Cabs C T : ℝ} (hw : w ≠ 0) {u ω : H}
    (hA : RouteAFeedback S w u ω 𝔗_F[κ, w, u]) (hκ : 0 < kappaDD S Cabs)
    {y y' : ℝ → ℝ} (hy0 : 0 ≤ y 0) (hc : ContinuousOn y (Set.Icc 0 T))
    (hd : ∀ x ∈ Set.Ico 0 T, HasDerivWithinAt y (y' x) (Set.Ici x) x)
    (hineq : ∀ x ∈ Set.Ico 0 T, y' x ≤ C * y x ^ 2 - kappaDD κ Cabs * y x ^ 3) :
    ∀ t ∈ Set.Icc 0 T, y t ≤ max (y 0) (C / kappaDD κ Cabs) := by
  have := routeA_determines_kappa hw hA
  subst this
  exact layer2_bound hκ hy0 hc hd hineq

end Frohman.Tether
