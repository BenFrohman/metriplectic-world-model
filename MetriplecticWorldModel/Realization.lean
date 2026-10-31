/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.Model

/-!
# What the may-form maximizer `Prop`s do and do not carry

* `realization_of_rate` (**proved**): if `M > 0` satisfies `TetheredMaxRate C κ M M'` and
  `0 ≤ C_abs`, then `MaxPointRealization C κ C_abs M M'` holds. With
  `tetheredMaxRate_of_realization` this shows the five may-form `Prop`s
  (`EnergyIdentity`, `StretchingCZ`, `ViscousAtMax`, `TetherFeedback`, `CrossControlled`),
  stated on bare real `MaxPointData`, are bookkeeping for the rate inequality: they can always
  be met by choosing the data. Their mathematical content only appears once the data are tied
  to an actual vorticity field (the `|ω|` maximizer, its time derivative, `ν ω·Δω`, ...). That
  link is not formalized; so these `Prop`s cannot be "proved" in a meaningful sense here.
* `gateaux_rep_of_not_differentiable` / `not_streamFunctionRepresentative` (**proved**):
  the encoding `IsGateauxRepresentative` quantifies over a differentiability hypothesis on `ω`,
  so at a non-differentiable `ω` every field is a representative; uniqueness fails, so
  `StreamFunctionRepresentative ω` is false there and `FunctionalDerivative` is an arbitrary
  choice. Hence `KineticEnergyCurlIdentity` cannot be proved for all `ω` in the current
  encoding; it needs a restriction to smooth orbits and uniqueness modulo gradients.
-/

open Set NavierStokes3D ArnoldGeometric FrohmanianTether Frohman.Tether

namespace MetriplecticWorldModel

theorem realization_of_rate (C κ Cabs : ℝ) (hCabs : 0 ≤ Cabs) (M M' : ℝ → ℝ)
    (hpos : ∀ t, 0 ≤ t → 0 < M t) (h : TetheredMaxRate C κ M M') :
    MaxPointRealization C κ Cabs M M' := by
  refine ⟨fun t ht => (h t ht).1, fun t ht => ?_⟩
  have hy := hpos t ht
  have hr := (h t ht).2
  refine ⟨⟨M t, M' t, C * M t ^ 3, M t * M' t - C * M t ^ 3 + κ * M t ^ 4,
    -κ * M t ^ 4, 0⟩, rfl, rfl, hy, ?_, ?_, ?_, ?_, ?_⟩
  · unfold EnergyIdentity; simp only; ring
  · unfold StretchingCZ; simp only; exact le_refl _
  · unfold ViscousAtMax; simp only
    have : M t * M' t ≤ M t * (C * M t ^ 2 - κ * M t ^ 3) := mul_le_mul_of_nonneg_left hr hy.le
    nlinarith
  · unfold TetherFeedback; simp only
  · unfold CrossControlled; simp only; norm_num; positivity

theorem gateaux_rep_of_not_differentiable (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit)
    (hnd : ¬ ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x)
    (d : T3 → EuclideanSpace ℝ (Fin 3)) : IsGateauxRepresentative F ω d := by
  intro ε hω; exact absurd hω hnd

theorem not_streamFunctionRepresentative (ω : CoadjointOrbit)
    (hnd : ¬ ∀ i x, DifferentiableAt ℝ (fun y => ω.val y i) x) :
    ¬ StreamFunctionRepresentative ω := by
  rintro ⟨ψ, _, huniq, _⟩
  set c : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1
  have h1 := huniq (fun x => ψ x + c) (gateaux_rep_of_not_differentiable _ ω hnd _)
  have h2 := congrFun h1 0
  have : c = 0 := by simpa using h2
  have hc : c ≠ 0 := by simp [c]
  exact hc this

end MetriplecticWorldModel
