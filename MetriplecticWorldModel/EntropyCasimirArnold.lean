/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.HelicityGateaux

/-!
# `EntropyCasimir` for the concrete Arnold bracket

* `ArnoldCasimirField ω s` (clean restatement): the derivative field `s` is annihilated by the
  concrete choice-free bracket, `∀ a, ArnoldBracketOf ω a s = 0`. No functional-derivative
  assignment and no `Classical.choose` enter.
* `entropyCasimir_of_arnoldCasimirField` (**proved**): it implies the generic
  `EntropyCasimir` for `F G ↦ ArnoldBracketOf ω (D F) (D G)` whenever `D S = s`.
* `arnoldCasimirField_of_curl_parallel`, `arnoldCasimirField_helicity` (**proved**): helicity's
  derivative `2u` is a Casimir field on the test class, unconditionally.
* `EntropyCasimirChoice ω S` (**kept, NOT PROVABLE as stated**): `EntropyCasimir` for the
  choice-based `ClassicalBracket`, which uses `FunctionalDerivative` (= `Classical.choose` of a
  Gâteaux representative). The chosen representative is unconstrained (only up to null sets,
  and arbitrary at non-differentiable `ω`, see `gateaux_rep_of_not_differentiable`,
  `not_streamFunctionRepModGrad`), so nothing about its curl can be derived. Use
  `ArnoldCasimirField` instead.
-/

open NavierStokes3D ArnoldGeometric FrohmanianTether

namespace MetriplecticWorldModel

/-- Clean Casimir condition for the concrete bracket: `s` pairs to zero with every field. -/
def ArnoldCasimirField (ω : CoadjointOrbit) (s : T3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ a, ArnoldBracketOf ω a s = 0

/-- NOT PROVABLE as stated (choice-based; kept for the record, do not use as a target). -/
def EntropyCasimirChoice (ω : CoadjointOrbit) (S : Functional) : Prop :=
  EntropyCasimir (fun F G => ClassicalBracket F G ω) S

theorem entropyCasimir_of_arnoldCasimirField {ω : CoadjointOrbit}
    {s : T3 → EuclideanSpace ℝ (Fin 3)} (h : ArnoldCasimirField ω s)
    (D : Functional → T3 → EuclideanSpace ℝ (Fin 3)) (S : Functional) (hD : D S = s) :
    EntropyCasimir (fun F G => ArnoldBracketOf ω (D F) (D G)) S := fun F => by
  simp only; rw [hD]; exact h _

theorem arnoldCasimirField_of_curl_parallel (ω : CoadjointOrbit)
    (s : T3 → EuclideanSpace ℝ (Fin 3)) (c : ℝ) (hs : ∀ x, curl s x = c • ω.val x) :
    ArnoldCasimirField ω s := fun a => arnoldBracketOf_eq_zero_of_curl_parallel ω a s c hs

/-- Helicity: `2u = 2 B ω` is an Arnold Casimir field on the test class (no hypotheses). -/
theorem arnoldCasimirField_helicity (ω : CoadjointOrbit) (hω : IsTestOrbit ω) :
    ArnoldCasimirField ω (fun x => (2 : ℝ) • BiotSavart ω.val x) := by
  refine arnoldCasimirField_of_curl_parallel ω _ 2 fun x => ?_
  rw [curl_smul, ← velocity_from_vorticity_eq_BiotSavart, curlBiotSavartTest ω hω]

end MetriplecticWorldModel
