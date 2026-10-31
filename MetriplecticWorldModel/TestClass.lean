/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.HelmholtzObstruction

/-!
# The restricted class: smooth, compactly supported, divergence-free fields

* `IsTestOrbit ω`: every coordinate is `C^∞` and `ω` has compact support. (Divergence-free is
  built into `CoadjointOrbit`.) `pointSpike` is excluded (`not_isTestOrbit_pointSpike`, **proved**).
* `IsGateauxRepOn F ω hω δ`: the Gâteaux condition, tested only on variations `ε` in the class.
* `StreamFunctionRepModGradOn ω hω` (named `Prop`, **open**): the uniqueness claim on the class.
  It covers `C²` representatives only, modulo gradients of `C²` functions.
* `CurlBiotSavartTest := CurlBiotSavartOn IsTestOrbit` (named `Prop`, **open**).
* First Newton-potential building block: `integrableOn_ball_norm_rpow_neg` (**proved**).
  For `s < 3`, `x ↦ ‖x‖^(-s)` is integrable on every ball in `ℝ³`. This gives local integrability of
  the Newton kernel `1/(4π|x|)` (`s = 1`) and of the Biot–Savart kernel magnitude `|x|⁻²` (`s = 2`).
-/

open NavierStokes3D ArnoldGeometric FrohmanianTether MeasureTheory Set Metric

namespace MetriplecticWorldModel

/-- Smooth, compactly supported (divergence-free) field. -/
def IsTestOrbit (ω : CoadjointOrbit) : Prop :=
  IsSmoothOrbit ω ∧ HasCompactSupport ω.val

theorem not_isTestOrbit_pointSpike : ¬ IsTestOrbit pointSpike := by
  rintro ⟨hs, -⟩
  have hd := (hs.differentiable 0 0)
  have hf : (fun y => pointSpike.val y 0) = spike := by funext y; simp [pointSpike]
  rw [hf] at hd
  have h1 := hd.hasFDerivAt
  rw [fderiv_spike] at h1
  have hc := hd.continuousAt
  have hev : ∀ᶠ z in nhds (0 : T3), spike z ∈ Metric.ball (1 : ℝ) (1 / 2) :=
    hc.eventually (by simpa [spike] using Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0:ℝ) < 1 / 2))
  obtain ⟨z, hz, hz0⟩ := ((hev.filter_mono nhdsWithin_le_nhds).and
    (self_mem_nhdsWithin (s := ({(0 : T3)}ᶜ : Set T3)))).exists
  have : spike z = 0 := by simp [spike, Set.indicator_of_notMem hz0]
  rw [this] at hz
  simp [Metric.mem_ball, Real.dist_eq] at hz
  norm_num at hz

/-- Gâteaux condition tested only on variations in the class. -/
def IsGateauxRepOn (F : CoadjointOrbit → ℝ) (ω : CoadjointOrbit) (hω : IsTestOrbit ω)
    (dF : T3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∀ (ε : CoadjointOrbit) (hε : IsTestOrbit ε),
    HasDerivAt (fun t : ℝ =>
      F ⟨fun x => ω.val x + t • ε.val x,
        fun x => orbit_add_smul_div_free ω ε t (hω.1.differentiable) (hε.1.differentiable) x⟩)
      (∫ x, pairing (dF x) (ε.val x) ∂volume) 0

/-- Named `Prop` (open): uniqueness modulo gradients on the restricted class. -/
def StreamFunctionRepModGradOn (ω : CoadjointOrbit) (hω : IsTestOrbit ω) : Prop :=
  ∃ ψ : T3 → EuclideanSpace ℝ (Fin 3),
    (∀ c, ContDiff ℝ 2 (fun y => ψ y c)) ∧
    IsGateauxRepOn KineticEnergyHamiltonian ω hω ψ ∧
    curl ψ = velocity_from_vorticity ω ∧
    ∀ d, (∀ c, ContDiff ℝ 2 (fun y => d y c)) → IsGateauxRepOn KineticEnergyHamiltonian ω hω d →
      ∃ φ : T3 → ℝ, ContDiff ℝ 2 φ ∧ d = fun y => ψ y + grad φ y

/-- Named `Prop` (open): `curl (BiotSavart ω) = ω` on the restricted class. -/
def CurlBiotSavartTest : Prop := CurlBiotSavartOn IsTestOrbit

/-- Helicity Casimir on the class, conditional on `CurlBiotSavartTest`. -/
theorem helicity_casimir_test (hBS : CurlBiotSavartTest) (ω : CoadjointOrbit) (hω : IsTestOrbit ω)
    (D : Functional → T3 → EuclideanSpace ℝ (Fin 3)) (S : Functional)
    (hD : D S = velocity_from_vorticity ω) :
    EntropyCasimir (fun F G => ArnoldBracketOf ω (D F) (D G)) S :=
  helicity_casimir_of_curlBiotSavart IsTestOrbit hBS ω hω D S hD

/-- Local integrability of `‖x‖^(-s)` on balls of `ℝ³` for `s < 3`. -/
theorem integrableOn_ball_norm_rpow_neg {s : ℝ} (hs : s < 3) (R : ℝ) :
    IntegrableOn (fun x : T3 => ‖x‖ ^ (-s)) (ball (0 : T3) R) (MeasureTheory.volume) := by
  rcases le_or_gt R 0 with hR | hR
  · simp [Metric.ball_eq_empty.mpr hR]
  set f : ℝ → ℝ := (Iio R).indicator fun r => r ^ (-s) with hf
  have hfi : Integrable (fun x : T3 => f ‖x‖) (MeasureTheory.volume) := by
    rw [integrable_fun_norm_addHaar]
    have hdim : Module.finrank ℝ T3 = 3 := by simp
    rw [hdim]
    have hloc : IntegrableOn (fun y : ℝ => y ^ (2 - s)) (Ioo 0 R) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hR).mpr (by linarith)
    have hsplit : Ioi (0 : ℝ) = Ioo 0 R ∪ Ici R := by
      ext y; simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]; constructor
      · intro h; by_cases hy : y < R
        · exact Or.inl ⟨h, hy⟩
        · exact Or.inr (not_lt.mp hy)
      · rintro (⟨h, -⟩ | h) <;> linarith
    rw [hsplit]
    refine IntegrableOn.union ?_ ?_
    · refine hloc.congr_fun (fun y hy => ?_) measurableSet_Ioo
      simp only [smul_eq_mul, hf, indicator_of_mem (show y ∈ Iio R from hy.2)]
      rw [show (3 - 1 : ℕ) = 2 by rfl, ← Real.rpow_natCast, ← Real.rpow_add hy.1]
      norm_num [sub_eq_add_neg]
    · refine (integrableOn_zero).congr_fun (fun y hy => ?_) measurableSet_Ici
      have : y ∉ Iio R := fun h => absurd (mem_Ici.mp hy) (not_le.mpr h)
      simp [hf, indicator_of_notMem this]
  refine (hfi.integrableOn (s := ball (0 : T3) R)).congr_fun (fun x hx => ?_) measurableSet_ball
  simp only [hf, mem_ball_zero_iff] at hx ⊢
  rw [indicator_of_mem (show ‖x‖ ∈ Iio R from hx)]

end MetriplecticWorldModel
