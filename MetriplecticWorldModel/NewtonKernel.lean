/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.TestClass

/-!
# Newton-potential step 1: `1/|x|` is smooth and harmonic away from the origin

* `newtonRadial y := (‖y‖²)^(-1/2) = 1/|y|`.
* `scalarLaplacian f x := Σᵢ ∂ᵢ∂ᵢ f (x)` (coordinate second derivatives via `fderiv`).
* `contDiffAt_newtonRadial` (**proved**): `C^∞` at every `x ≠ 0`.
* `fderiv_newtonRadial_single` (**proved**): `∂ᵢ (1/|y|) = −yᵢ (‖y‖²)^(-3/2)` for `y ≠ 0`.
* `scalarLaplacian_newtonRadial` (**proved**): `Δ(1/|x|) = 0` for `x ≠ 0`.
-/

open NavierStokes3D MeasureTheory Set Metric
open scoped RealInnerProductSpace

namespace MetriplecticWorldModel

noncomputable def newtonRadial (y : T3) : ℝ := (‖y‖ ^ 2) ^ (-(1 / 2 : ℝ))

noncomputable def scalarLaplacian (f : T3 → ℝ) (x : T3) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) x
    (EuclideanSpace.single i 1)

theorem contDiffAt_newtonRadial {x : T3} (hx : x ≠ 0) :
    ContDiffAt ℝ ⊤ newtonRadial x := by
  unfold newtonRadial
  have h1 : ContDiffAt ℝ ⊤ (fun y : T3 => ‖y‖ ^ 2) x := (contDiff_norm_sq ℝ).contDiffAt
  exact h1.rpow_const_of_ne (by positivity)

theorem inner_single_one (y : T3) (i : Fin 3) : ⟪y, EuclideanSpace.single i (1 : ℝ)⟫ = y i := by
  have := EuclideanSpace.inner_single_right (𝕜 := ℝ) i (1 : ℝ) (y : EuclideanSpace ℝ (Fin 3))
  simpa using this

theorem hasFDerivAt_normSq_rpow (p : ℝ) {y : T3} (hy : y ≠ 0) :
    HasFDerivAt (fun z : T3 => (‖z‖ ^ 2) ^ p)
      ((p * (‖y‖ ^ 2) ^ (p - 1)) • (2 • innerSL ℝ y)) y :=
  (hasStrictFDerivAt_norm_sq y).hasFDerivAt.rpow_const (Or.inl (by positivity))

theorem normSq_rpow_partial (p : ℝ) {y : T3} (hy : y ≠ 0) (i : Fin 3) :
    fderiv ℝ (fun z : T3 => (‖z‖ ^ 2) ^ p) y (EuclideanSpace.single i 1) =
      2 * p * (‖y‖ ^ 2) ^ (p - 1) * y i := by
  rw [(hasFDerivAt_normSq_rpow p hy).fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right]
  simp [inner_single_one]
  ring

theorem fderiv_newtonRadial_single {y : T3} (hy : y ≠ 0) (i : Fin 3) :
    fderiv ℝ newtonRadial y (EuclideanSpace.single i 1) =
      -(‖y‖ ^ 2) ^ (-(3 / 2 : ℝ)) * y i := by
  unfold newtonRadial
  rw [normSq_rpow_partial _ hy]
  norm_num

theorem scalarLaplacian_newtonRadial {x : T3} (hx : x ≠ 0) :
    scalarLaplacian newtonRadial x = 0 := by
  unfold scalarLaplacian
  have hpart : ∀ i : Fin 3,
      fderiv ℝ (fun y => fderiv ℝ newtonRadial y (EuclideanSpace.single i 1)) x
        (EuclideanSpace.single i 1) =
      3 * (‖x‖ ^ 2) ^ (-(5 / 2 : ℝ)) * x i * x i - (‖x‖ ^ 2) ^ (-(3 / 2 : ℝ)) := by
    intro i
    have hev : (fun y => fderiv ℝ newtonRadial y (EuclideanSpace.single i 1)) =ᶠ[nhds x]
        fun y => -(‖y‖ ^ 2) ^ (-(3 / 2 : ℝ)) * y i := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
      exact fderiv_newtonRadial_single hy i
    rw [hev.fderiv_eq]
    have hA := (hasFDerivAt_normSq_rpow (-(3 / 2 : ℝ)) hx).fun_neg
    have hB : HasFDerivAt (fun y : T3 => y i) (EuclideanSpace.proj i : T3 →L[ℝ] ℝ) x :=
      (EuclideanSpace.proj i : T3 →L[ℝ] ℝ).hasFDerivAt
    rw [(hA.fun_mul hB).fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, innerSL_apply_apply, EuclideanSpace.inner_single_right]
    simp [inner_single_one]
    norm_num
    ring
  simp only [hpart, Fin.sum_univ_three]
  have hn : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  have key : (‖x‖ ^ 2) ^ (-(5 / 2 : ℝ)) * ‖x‖ ^ 2 = (‖x‖ ^ 2) ^ (-(3 / 2 : ℝ)) := by
    conv_lhs => arg 2; rw [← Real.rpow_one (‖x‖ ^ 2)]
    rw [← Real.rpow_add hpos]; norm_num
  rw [← key, hn]
  ring

end MetriplecticWorldModel

/-!
# Newton-potential step 2: the Newton potential of a test function is smooth

* `newtonRadial_eq` (**proved**): `newtonRadial y = ‖y‖^(-1)`.
* `locallyIntegrable_newtonRadial` (**proved**).
* `newtonPotential g := newtonRadial ⋆ g` (unnormalized; the physical potential is `−(4π)⁻¹ ·`).
* `contDiff_newtonPotential` (**proved**): `C^∞` for `g` smooth with compact support.
* `hasFDerivAt_newtonPotential` (**proved**): derivative passes under the integral,
  `D(N ⋆ g) = N ⋆ Dg` (Mathlib's convolution differentiation, instantiated).
-/

namespace MetriplecticWorldModel

open scoped Convolution

theorem newtonRadial_eq (y : T3) : newtonRadial y = ‖y‖ ^ (-(1 : ℝ)) := by
  unfold newtonRadial
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg y)]
  norm_num

theorem locallyIntegrable_newtonRadial :
    LocallyIntegrable newtonRadial (MeasureTheory.volume : Measure T3) := by
  intro x
  refine ⟨ball (0 : T3) (‖x‖ + 1), ?_, ?_⟩
  · exact isOpen_ball.mem_nhds (by simp)
  · have := integrableOn_ball_norm_rpow_neg (s := 1) (by norm_num) (‖x‖ + 1)
    refine this.congr_fun (fun y _ => (newtonRadial_eq y).symm) measurableSet_ball

noncomputable def newtonPotential (g : T3 → ℝ) : T3 → ℝ :=
  newtonRadial ⋆[ContinuousLinearMap.lsmul ℝ ℝ, MeasureTheory.volume] g

theorem contDiff_newtonPotential {g : T3 → ℝ} (hc : HasCompactSupport g)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (newtonPotential g) :=
  hc.contDiff_convolution_right (n := ⊤) (ContinuousLinearMap.lsmul ℝ ℝ)
    locallyIntegrable_newtonRadial hg

theorem hasFDerivAt_newtonPotential {g : T3 → ℝ} (hc : HasCompactSupport g)
    (hg : ContDiff ℝ 1 g) (x : T3) :
    HasFDerivAt (newtonPotential g)
      ((newtonRadial ⋆[(ContinuousLinearMap.lsmul ℝ ℝ).precompR T3, MeasureTheory.volume]
        fderiv ℝ g) x) x :=
  hc.hasFDerivAt_convolution_right _ locallyIntegrable_newtonRadial hg x

end MetriplecticWorldModel
