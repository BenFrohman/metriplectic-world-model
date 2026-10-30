/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import FrohmanianSymplecticTether.TetheredLyapunov
public import FrohmanianSymplecticTether.NS_Equations

/-!
# Independent Comparison Majorant

Single source of truth: `ComparisonODE` and `lemma_3_1_uniform_bound_and_continuation`
live in `TetheredLyapunov`. This module re-exports them so the analytic layer has
one Riccati majorant and one Lemma 3.1.
-/

namespace IndependentMajorant

open TetheredLyapunov NavierStokes3D

public noncomputable abbrev ComparisonODE := TetheredLyapunov.ComparisonODE

public theorem comparison_majorant_global_bound (C κ'' y0 : ℝ) (hC : 0 < C) (hκ : 0 < κ'')
    (hy0 : 0 ≤ y0) :
    ∃ Y : ℝ, ∀ t ≥ (0 : ℝ),
      0 ≤ ComparisonODE C κ'' y0 t ∧ ComparisonODE C κ'' y0 t ≤ Y :=
  ⟨max y0 (C / κ''), fun t ht =>
    TetheredLyapunov.uniform_majorant_bound C κ'' y0 hC hκ hy0 t ht⟩

public theorem lemma_3_1_uniform_bound_and_continuation
    (u0 : VelocityField) (ν : ℝ)
    (h_divfree : ∀ x, div u0 x = 0)
    (h_smooth : ContDiff ℝ (⊤ : ℕ∞) u0)
    (Mε0 C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'') (hM : 0 ≤ Mε0) :
    ∀ T : ℝ, 0 ≤ T → (T : EReal) < Tstar u0 ν →
      ComparisonODE C κ'' Mε0 T ≤ max Mε0 (C / κ'') :=
  TetheredLyapunov.lemma_3_1_uniform_bound_and_continuation
    u0 ν h_divfree h_smooth Mε0 C κ'' hC hκ hM

public noncomputable abbrev Tstar := NavierStokes3D.Tstar

end IndependentMajorant
