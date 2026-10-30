/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.Model

/-!
# A concrete instance of the tethered model (scalar peak-vorticity ODE)

`StretchingCZ` is a hypothesis on `MaxPointData`, i.e. on the model's maximizer data. It is
**not** claimed as an `L∞` estimate for unmodified Navier–Stokes (that estimate is not known;
the true bound has a log loss). In the model instance below, the stretching term is *defined*
by the model closure `St = C y³`, so `StretchingCZ` holds there by construction.

The instance: `C = 0`, any `κ > 0`, `y₀ > 0` with `κ y₀² ≤ 1`, and peak vorticity
`M t = y₀ e^{-t}`. We prove `MaxPointRealization`, `TetheredMaxRate` and `ModelContinuation`
for it, so `model_global_regularity_of_realization` holds for it with no open hypothesis.
This is a one-dimensional toy instance; it shows the hypotheses are jointly satisfiable and
non-vacuous. It is not a Galerkin truncation of Navier–Stokes.
-/

open Set Real Frohman.Tether

namespace MetriplecticWorldModel

/-- Instance peak vorticity `M t = y₀ e^{-t}`. -/
noncomputable def instM (y0 : ℝ) : ℝ → ℝ := fun t => y0 * exp (-t)
/-- Its derivative. -/
noncomputable def instM' (y0 : ℝ) : ℝ → ℝ := fun t => -(y0 * exp (-t))

theorem instM_hasDerivAt (y0 t : ℝ) : HasDerivAt (instM y0) (instM' y0 t) t := by
  have := ((hasDerivAt_neg t).exp).const_mul y0
  convert this using 1; simp [instM']

/-- Model maximizer data at time `t` (closure `St = C y³` with `C = 0`, `b = 0`). -/
noncomputable def instData (κ y0 t : ℝ) : MaxPointData where
  y := instM y0 t
  y' := instM' y0 t
  St := 0
  V := instM y0 t * instM' y0 t + κ * instM y0 t ^ 4
  tetherTerm := -κ * instM y0 t ^ 4
  b := 0

theorem instance_maxPointRealization (κ y0 : ℝ) (hκ : 0 < κ) (hy0 : 0 < y0)
    (hsmall : κ * y0 ^ 2 ≤ 1) :
    MaxPointRealization 0 κ 0 (instM y0) (instM' y0) := by
  refine ⟨fun t _ => instM_hasDerivAt y0 t, fun t ht => ⟨instData κ y0 t, rfl, rfl, ?_, ?_, ?_,
    ?_, ?_, ?_⟩⟩
  · exact mul_pos hy0 (exp_pos _)
  · simp [EnergyIdentity, instData]
  · simp [StretchingCZ, instData]
  · simp only [ViscousAtMax, instData, instM, instM']
    have he : exp (-t) ≤ 1 := exp_le_one_iff.2 (by linarith)
    have he0 : 0 < exp (-t) := exp_pos _
    have hm : y0 * exp (-t) ≤ y0 := by nlinarith
    have hm0 : 0 < y0 * exp (-t) := mul_pos hy0 he0
    have : κ * (y0 * exp (-t)) ^ 2 ≤ 1 := by
      calc κ * (y0 * exp (-t)) ^ 2 ≤ κ * y0 ^ 2 := by gcongr
        _ ≤ 1 := hsmall
    nlinarith [sq_nonneg (y0 * exp (-t))]
  · simp [TetherFeedback, instData]
  · simp [CrossControlled, instData]

/-- Smoothness predicate of the instance: `M` is `C^∞` at `t`. -/
def instSmooth (y0 : ℝ) (t : ℝ) : Prop := ContDiffAt ℝ ⊤ (instM y0) t

theorem instance_modelContinuation (y0 : ℝ) : ModelContinuation (instSmooth y0) (instM y0) :=
  fun _ t _ => by unfold instSmooth instM; fun_prop

theorem instance_tetheredMaxRate (κ y0 : ℝ) (hκ : 0 < κ) (hy0 : 0 < y0)
    (hsmall : κ * y0 ^ 2 ≤ 1) : TetheredMaxRate 0 (κ / 2 - 0) (instM y0) (instM' y0) :=
  tetheredMaxRate_of_realization 0 κ 0 hκ _ _ (instance_maxPointRealization κ y0 hκ hy0 hsmall)

/-- **Unconditional for the instance:** global smoothness and the uniform ceiling. -/
theorem instance_global_regularity (κ y0 : ℝ) (hκ : 0 < κ) (hy0 : 0 < y0)
    (hsmall : κ * y0 ^ 2 ≤ 1) :
    (∀ t, 0 ≤ t → instSmooth y0 t) ∧
      ∀ t, 0 ≤ t → instM y0 t ≤ ceiling (instM y0 0) 0 (κ / 2 - 0) :=
  model_global_regularity_of_realization 0 κ 0 hκ (by linarith) _ _ _
    (instance_maxPointRealization κ y0 hκ hy0 hsmall) (instance_modelContinuation y0)

/-- Satisfiability of `EntropyCasimir`: the zero bracket has every functional as a Casimir. -/
theorem entropyCasimir_zero_bracket {α : Type*} (S : α) :
    (∀ F : α, (fun _ _ : α => (0 : ℝ)) F S = 0) := fun _ => rfl

/-- `StretchingCZ` is satisfiable and not automatic: it holds at `St = C y³` and fails at
`St = C y³ + 1`. -/
theorem stretchingCZ_sat_and_nontrivial (C y : ℝ) :
    StretchingCZ ⟨y, 0, C * y ^ 3, 0, 0, 0⟩ C ∧ ¬ StretchingCZ ⟨y, 0, C * y ^ 3 + 1, 0, 0, 0⟩ C := by
  simp [StretchingCZ]

end MetriplecticWorldModel
