/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# The uniform vorticity ceiling for the y³-damped comparison inequality

For `κ > 0`, any `M` with `M' ≤ C M² − κ M³ = M²(C − κM)` on `[0,T]` satisfies
`M(t) ≤ max (M 0) (max (C/κ) 0)` on `[0,T]`. The bound does not depend on `T`, so on
`[0,∞)` it is a uniform-in-time ceiling. Proved unconditionally (comparison argument, as in
`Lyapunov.ode_upper` of weighted-enstrophy-identities, extended from equality to inequality).
-/

open Set

namespace MetriplecticWorldModel

/-- The ceiling value. -/
noncomputable def ceiling (M0 C κ : ℝ) : ℝ := max M0 (max (C / κ) 0)

theorem ceiling_upper (C κ : ℝ) (hκ : 0 < κ) (M M' : ℝ → ℝ) (T : ℝ)
    (hM : ∀ t ∈ Icc 0 T, HasDerivAt M (M' t) t)
    (hle : ∀ t ∈ Icc 0 T, M' t ≤ C * M t ^ 2 - κ * M t ^ 3) :
    ∀ t ∈ Icc 0 T, M t ≤ ceiling (M 0) C κ := by
  set B := ceiling (M 0) C κ
  intro t ht
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hcont : ContinuousOn M (Icc 0 T) := fun s hs => (hM s hs).continuousAt.continuousWithinAt
  have key := image_le_of_deriv_right_lt_deriv_boundary' (a := 0) (b := T) (f := M)
    (f' := M') hcont
    (fun s hs => (hM s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (B := fun _ => B + ε) (B' := fun _ => 0)
    (by simp only [B, ceiling]; linarith [le_max_left (M 0) (max (C/κ) 0)])
    continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _) ?_ ht
  · linarith [key]
  · intro s hs hs'
    have hB0 : 0 ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
    have hBC : C / κ ≤ B := le_trans (le_max_left _ _) (le_max_right _ _)
    have hpos : 0 < M s := by rw [hs']; linarith
    have hneg : C - κ * M s < 0 := by
      rw [hs']; have := (div_le_iff₀ hκ).1 hBC; nlinarith
    have h2 : 0 < M s ^ 2 := by positivity
    have := hle s (Ico_subset_Icc_self hs)
    have : C * M s ^ 2 - κ * M s ^ 3 = M s ^ 2 * (C - κ * M s) := by ring
    nlinarith

/-- **Uniform-in-time ceiling.** If the inequality holds for all `t ≥ 0`, then
`M t ≤ max (M 0) (max (C/κ) 0)` for all `t ≥ 0`. -/
theorem uniform_ceiling (C κ : ℝ) (hκ : 0 < κ) (M M' : ℝ → ℝ)
    (hM : ∀ t, 0 ≤ t → HasDerivAt M (M' t) t)
    (hle : ∀ t, 0 ≤ t → M' t ≤ C * M t ^ 2 - κ * M t ^ 3) :
    ∀ t, 0 ≤ t → M t ≤ ceiling (M 0) C κ := fun t ht =>
  ceiling_upper C κ hκ M M' t (fun s hs => hM s hs.1) (fun s hs => hle s hs.1) t ⟨ht, le_rfl⟩

/-- Absorbing set: data starting at or below `C/κ` (with `C ≥ 0`) never exceeds `C/κ`. -/
theorem absorbing (C κ : ℝ) (hκ : 0 < κ) (hC : 0 ≤ C) (M M' : ℝ → ℝ)
    (hM : ∀ t, 0 ≤ t → HasDerivAt M (M' t) t)
    (hle : ∀ t, 0 ≤ t → M' t ≤ C * M t ^ 2 - κ * M t ^ 3) (h0 : M 0 ≤ C / κ) :
    ∀ t, 0 ≤ t → M t ≤ C / κ := by
  intro t ht
  have h := uniform_ceiling C κ hκ M M' hM hle t ht
  have hCk : 0 ≤ C / κ := div_nonneg hC hκ.le
  unfold ceiling at h
  simpa [max_eq_left hCk, max_eq_right h0] using h

/-- The ceiling is antitone in the tether strength `κ` (for `C ≥ 0`). -/
theorem ceiling_antitone_kappa (M0 C : ℝ) (hC : 0 ≤ C) {κ₁ κ₂ : ℝ} (h1 : 0 < κ₁)
    (h12 : κ₁ ≤ κ₂) : ceiling M0 C κ₂ ≤ ceiling M0 C κ₁ := by
  unfold ceiling
  exact max_le_max le_rfl (max_le_max (div_le_div_of_nonneg_left hC h1 h12) le_rfl)

/-- Finite-interval consequence (the form a BKM-type criterion uses): on every `[0,T]` the
ceiling gives a bound, hence `M` is bounded on each finite interval. -/
theorem bounded_on_every_interval (C κ : ℝ) (hκ : 0 < κ) (M M' : ℝ → ℝ)
    (hM : ∀ t, 0 ≤ t → HasDerivAt M (M' t) t)
    (hle : ∀ t, 0 ≤ t → M' t ≤ C * M t ^ 2 - κ * M t ^ 3) :
    ∀ T, 0 ≤ T → ∃ B, ∀ t ∈ Icc 0 T, M t ≤ B := fun _ _ =>
  ⟨ceiling (M 0) C κ, fun t ht => uniform_ceiling C κ hκ M M' hM hle t ht.1⟩

end MetriplecticWorldModel
