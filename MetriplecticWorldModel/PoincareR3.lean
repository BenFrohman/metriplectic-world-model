/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.HelicityGateaux
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare

/-!
# The Poincaré lemma on `ℝ³`: `CurlFreeIsGradient` is proved

Via Mathlib's `Convex.exists_forall_hasFDerivAt_of_fderiv_symmetric` (closed `1`-forms on a convex
open set are exact), applied to the `1`-form `a ↦ ⟪v a, ·⟫`. Curl-free means its derivative is
symmetric.
-/

open NavierStokes3D ArnoldGeometric FrohmanianTether
open scoped RealInnerProductSpace

set_option linter.unusedSimpArgs false

namespace MetriplecticWorldModel

theorem eq_sum_single (x : T3) :
    x = ∑ k : Fin 3, x k • (EuclideanSpace.single k (1 : ℝ) : T3) := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_three, PiLp.single_apply]

theorem curlFreeIsGradient : CurlFreeIsGradient := by
  intro v hv hcurl
  have hV : ContDiff ℝ 2 v := contDiff_euclidean.mpr hv
  set w : T3 → (T3 →L[ℝ] ℝ) := fun a => innerSL ℝ (v a) with hw
  have hW : ContDiff ℝ 2 w := (innerSL ℝ : T3 →L[ℝ] T3 →L[ℝ] ℝ).contDiff.comp hV
  have hdv : ∀ a, DifferentiableAt ℝ v a := fun a => (hV.differentiable (by norm_num)) a
  have hfw : ∀ a, fderiv ℝ w a = (innerSL ℝ : T3 →L[ℝ] T3 →L[ℝ] ℝ).comp (fderiv ℝ v a) :=
    fun a => ((innerSL ℝ : T3 →L[ℝ] T3 →L[ℝ] ℝ).hasFDerivAt.comp a (hdv a).hasFDerivAt).fderiv
  have hcoord : ∀ a x (i : Fin 3), fderiv ℝ v a x i = fderiv ℝ (fun y => v y i) a x := by
    intro a x i
    have h := ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i).hasFDerivAt).comp a (hdv a).hasFDerivAt
    rw [show (fun y => (v y).ofLp i) = ⇑(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => ℝ) i) ∘ v from rfl,
      h.fderiv]; rfl
  have hJ : ∀ a x (i : Fin 3), fderiv ℝ v a x i = ∑ k : Fin 3, x k * directionalCoord v i k a := by
    intro a x i
    rw [hcoord, eq_sum_single x, map_sum]
    simp only [map_smul, smul_eq_mul, directionalCoord]
    simp [Fin.sum_univ_three, EuclideanSpace.single_apply]
  have hsym : ∀ a x y, fderiv ℝ w a x y = fderiv ℝ w a y x := by
    intro a x y
    rw [hfw]
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, innerSL_apply_apply]
    have c := congrFun hcurl a
    have c0 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 0) c
    have c1 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 1) c
    have c2 := congrArg (fun z : EuclideanSpace ℝ (Fin 3) => z 2) c
    simp only [(curl_apply v a).1, (curl_apply v a).2.1, (curl_apply v a).2.2] at c0 c1 c2
    show ⟪fderiv ℝ v a x, y⟫ = ⟪fderiv ℝ v a y, x⟫
    simp only [PiLp.inner_apply, Fin.sum_univ_three, hJ]
    simp only [inner, conj_trivial, RCLike.re_to_real]
    try simp at c0 c1 c2
    have e0 : directionalCoord v 2 1 a = directionalCoord v 1 2 a := by
      simpa using (sub_eq_zero.mp (by simpa using c0))
    have e1 : directionalCoord v 0 2 a = directionalCoord v 2 0 a := by
      simpa using (sub_eq_zero.mp (by simpa using c1))
    have e2 : directionalCoord v 1 0 a = directionalCoord v 0 1 a := by
      simpa using (sub_eq_zero.mp (by simpa using c2))
    rw [e0, e1, e2]; ring
  obtain ⟨φ, hφ⟩ := (convex_univ : Convex ℝ (Set.univ : Set T3)).exists_forall_hasFDerivAt_of_fderiv_symmetric
    isOpen_univ (hW.differentiable (by norm_num)).differentiableOn (fun a _ x y => hsym a x y)
  have hφ' : ∀ a, HasFDerivAt φ (w a) a := fun a => hφ a trivial
  have hfd : fderiv ℝ φ = w := funext fun a => (hφ' a).fderiv
  refine ⟨φ, ?_, ?_⟩
  · rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_fderiv]
    refine ⟨fun a => (hφ' a).differentiableAt, by simp, ?_⟩
    rw [hfd]; exact hW.of_le (by norm_num)
  · funext y; ext c
    rw [grad_apply, hfd]
    simp only [hw, innerSL_apply_apply]
    simp [PiLp.inner_apply, Fin.sum_univ_three, PiLp.single_apply]
    fin_cases c <;> simp [inner]
