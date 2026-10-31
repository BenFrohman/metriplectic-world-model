/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.ChoiceFree

/-!
# `curl (BiotSavart ω) = ω` fails in the current encoding

`CoadjointOrbit` asks only `div ω = 0` pointwise, with `div` computed by `fderiv`, which is
`0` at points of non-differentiability. So the field `pointSpike` (`e₀` at the origin, `0`
elsewhere) is a `CoadjointOrbit`. Its Biot–Savart velocity is `0`, because the integrand vanishes
almost everywhere, so `curl u = 0 ≠ pointSpike` at the origin.

* `pointSpike_val_zero` and `velocity_pointSpike` (**proved**).
* `not_curl_biotSavart_eq` (**proved**): `¬ ∀ ω, curl (velocity_from_vorticity ω) = ω.val`.

Consequently the identity `curl (BiotSavart ω) = ω`, the helicity derivative `2u`, and
Helmholtz uniqueness can only hold on a restricted class (e.g. smooth, compactly supported
`ω` and `ε`). `CurlBiotSavartOn S` names that restricted statement. With it,
`helicity_casimir_of_curlBiotSavart` (**proved**) closes the helicity Casimir for
`ArnoldBracketOf`. The restricted identity itself (Newton potential, `Δ(1/|x|) = −4πδ`) is
**open**: Mathlib has no fundamental solution of the Laplacian in `ℝ³`.
-/

open NavierStokes3D ArnoldGeometric FrohmanianTether MeasureTheory Filter Topology

namespace MetriplecticWorldModel

/-- Scalar spike: `1` at the origin, `0` elsewhere. -/
noncomputable def spike : T3 → ℝ := ({(0 : T3)} : Set T3).indicator 1

theorem fderiv_spike (y : T3) : fderiv ℝ spike y = 0 := by
  by_cases hy : y = 0
  · subst hy
    apply fderiv_zero_of_not_differentiableAt
    intro hd
    have hc := hd.continuousAt
    have hev : ∀ᶠ z in 𝓝 (0 : T3), spike z ∈ Metric.ball (1 : ℝ) (1 / 2) :=
      hc.eventually (by simpa [spike] using Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0:ℝ) < 1 / 2))
    obtain ⟨z, hz, hz0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := ({(0 : T3)}ᶜ : Set T3)))).exists
    have : spike z = 0 := by simp [spike, Set.indicator_of_notMem hz0]
    rw [this] at hz
    simp [Metric.mem_ball, Real.dist_eq] at hz
    norm_num at hz
  · have : spike =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hy] with z hz
      simp [spike, Set.indicator_of_notMem hz]
    rw [this.fderiv_eq]; simp

/-- The point-spike vorticity `e₀ · spike`. It is a `CoadjointOrbit` in this encoding. -/
noncomputable def pointSpike : CoadjointOrbit where
  val y := spike y • EuclideanSpace.single 0 1
  property x := by
    unfold NavierStokes3D.div
    rw [Fin.sum_univ_three]
    have h0 : (fun y => (spike y • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) 0) = spike := by
      funext y; simp
    have h1 : (fun y => (spike y • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) 1) = fun _ => 0 := by
      funext y; simp
    have h2 : (fun y => (spike y • EuclideanSpace.single (0 : Fin 3) (1 : ℝ)) 2) = fun _ => 0 := by
      funext y; simp
    rw [h0, h1, h2, fderiv_spike]; simp

theorem pointSpike_val_zero : pointSpike.val 0 = EuclideanSpace.single 0 1 := by
  simp [pointSpike, spike]

theorem velocity_pointSpike : velocity_from_vorticity pointSpike = 0 := by
  have hae : ∀ x, (fun y => biotSavartKernel x y • cross (pointSpike.val y) (x - y)) =ᵐ[volume]
      fun y => biotSavartKernel x y • cross ((fun _ => (0 : EuclideanSpace ℝ (Fin 3))) y) (x - y) := by
    intro x
    have : ∀ᵐ y ∂(MeasureTheory.volume : Measure T3), y ≠ (0 : T3) := by rw [ae_iff]; simp
    filter_upwards [this] with y hy
    have hs : spike y = 0 := by simp [spike, Set.indicator_of_notMem (show y ∉ ({0} : Set T3) from hy)]
    simp [pointSpike, hs]
  funext x
  have h := congrFun BiotSavart_zero x
  unfold velocity_from_vorticity BiotSavart at *
  rw [integral_congr_ae (hae x)]
  exact h

theorem not_curl_biotSavart_eq :
    ¬ ∀ ω : CoadjointOrbit, curl (velocity_from_vorticity ω) = ω.val := by
  intro h
  have := congrFun (h pointSpike) 0
  rw [velocity_pointSpike, pointSpike_val_zero] at this
  have hc : curl (0 : VelocityField) 0 = 0 := by
    simp only [curl, directionalCoord]
    simp
    ext i; fin_cases i <;> simp [EuclideanSpace.single_apply]
  rw [hc] at this
  have := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) this
  simp at this

/-- Named `Prop`: `curl (BiotSavart ω) = ω` on a class `S` of orbits (e.g. smooth, compactly
supported). Open: needs the Newton potential in `ℝ³`. -/
def CurlBiotSavartOn (S : CoadjointOrbit → Prop) : Prop :=
  ∀ ω, S ω → curl (velocity_from_vorticity ω) = ω.val

/-- Helicity Casimir for the choice-free Arnold bracket, given the restricted identity, with
`D` sending the helicity `S` to the velocity `u` (helicity's derivative is `2u`; the factor
is a constant multiple and does not affect the Casimir property). -/
theorem helicity_casimir_of_curlBiotSavart (C : CoadjointOrbit → Prop)
    (hBS : CurlBiotSavartOn C) (ω : CoadjointOrbit) (hω : C ω)
    (D : Functional → T3 → EuclideanSpace ℝ (Fin 3)) (S : Functional)
    (hD : D S = velocity_from_vorticity ω) :
    EntropyCasimir (fun F G => ArnoldBracketOf ω (D F) (D G)) S :=
  entropyCasimir_arnold ω D S 1 (fun x => by rw [hD, hBS ω hω, one_smul])

end MetriplecticWorldModel
