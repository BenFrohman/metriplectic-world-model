/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import MetriplecticWorldModel.Ceiling
import MetriplecticWorldModel.Model

/-!
# The full ceiling theorem

The paper's theorem `uniform_ceiling` (Section "Ceiling and stretching") states four things
together: the uniform ceiling, the absorbing set, monotonicity of the ceiling in `κ`, and the
absence of any ceiling at `κ = 0`. `uniform_ceiling_full` is their conjunction, assembled from
`uniform_ceiling`, `absorbing`, `ceiling_antitone_kappa` and `kappa_zero_no_ceiling`.
-/

open Set

namespace MetriplecticWorldModel

/-- **Full ceiling theorem**: (i) uniform ceiling for `κ > 0`; (ii) absorbing set for `C ≥ 0`;
(iii) the ceiling is antitone in `κ` for `C ≥ 0`; (iv) at `κ = 0`, `M = 1/(1-t)` satisfies
`M' ≤ M²` on `t < 1` and is unbounded on `[0, 1)`. -/
theorem uniform_ceiling_full :
    (∀ (C κ : ℝ), 0 < κ → ∀ (M M' : ℝ → ℝ),
      (∀ t, 0 ≤ t → HasDerivAt M (M' t) t) →
      (∀ t, 0 ≤ t → M' t ≤ C * M t ^ 2 - κ * M t ^ 3) →
      ∀ t, 0 ≤ t → M t ≤ ceiling (M 0) C κ) ∧
    (∀ (C κ : ℝ), 0 < κ → 0 ≤ C → ∀ (M M' : ℝ → ℝ),
      (∀ t, 0 ≤ t → HasDerivAt M (M' t) t) →
      (∀ t, 0 ≤ t → M' t ≤ C * M t ^ 2 - κ * M t ^ 3) → M 0 ≤ C / κ →
      ∀ t, 0 ≤ t → M t ≤ C / κ) ∧
    (∀ (M0 C : ℝ), 0 ≤ C → ∀ (κ₁ κ₂ : ℝ), 0 < κ₁ → κ₁ ≤ κ₂ →
      ceiling M0 C κ₂ ≤ ceiling M0 C κ₁) ∧
    ((∀ t : ℝ, t < 1 → ∃ d : ℝ, HasDerivAt (fun s : ℝ => (1 - s)⁻¹) d t ∧
        d ≤ 1 * ((1 - t)⁻¹) ^ 2 - 0 * ((1 - t)⁻¹) ^ 3) ∧
      ¬ ∃ B, ∀ t ∈ Ico (0:ℝ) 1, (1 - t)⁻¹ ≤ B) := by
  refine ⟨fun C κ hκ M M' hM hle => uniform_ceiling C κ hκ M M' hM hle,
    fun C κ hκ hC M M' hM hle h0 => absorbing C κ hκ hC M M' hM hle h0,
    fun M0 C hC κ₁ κ₂ h1 h12 => ceiling_antitone_kappa M0 C hC h1 h12, ?_, kappa_zero_no_ceiling.2⟩
  intro t ht
  exact ⟨_, (kappa_zero_no_ceiling.1 t ht).1, (kappa_zero_no_ceiling.1 t ht).2⟩

end MetriplecticWorldModel
