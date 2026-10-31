/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.SmoothOrbit

/-!
# `StreamFunctionRepModGrad` is false as stated; a choice-free Arnold bracket

* `not_streamFunctionRepModGrad` (**proved**): for every `ω`, `StreamFunctionRepModGrad ω`
  fails. Gâteaux representatives are only determined up to null sets: changing one at the
  single point `0` leaves every `L²` pairing unchanged, but the difference is not the
  gradient of a `C²` function (gradients of `C²` functions are continuous). So the
  `Prop` cannot be proved by Helmholtz + Biot–Savart IBP; it must be restated a.e.
* `ArnoldBracketOf ω a b := ∫ ⟨ω, curl a × curl b⟩`: the Arnold bracket taking the
  derivative fields as data (no `Classical.choose`). `arnoldBracketOf_antisymm` (**proved**).
* `arnoldBracketOf_eq_zero_of_curl_parallel` (**proved**): if `curl s = c • ω` pointwise,
  then `ArnoldBracketOf ω a s = 0` for every `a`.
* `entropyCasimir_arnold` (**proved**): for any choice-free derivative assignment `D`,
  if `curl (D S) = c • ω` then `S` is a Casimir of `F G ↦ ArnoldBracketOf ω (D F) (D G)`.
  Example: helicity, whose derivative is (twice) the velocity `u`, with `curl u = ω`.
  That `D` is the true Gâteaux derivative of `S` is a separate hypothesis, not proved here.
-/

open NavierStokes3D ArnoldGeometric FrohmanianTether MeasureTheory

namespace MetriplecticWorldModel

theorem not_streamFunctionRepModGrad (ω : CoadjointOrbit) : ¬ StreamFunctionRepModGrad ω := by
  rintro ⟨ψ, -, hrep, -, huniq⟩
  set e : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 1
  set d : T3 → EuclideanSpace ℝ (Fin 3) :=
    fun y => ψ y + ({(0 : T3)} : Set T3).indicator (fun _ => e) y with hd_def
  have hae : ∀ᵐ x ∂(MeasureTheory.volume : Measure T3), x ≠ (0 : T3) := by
    rw [ae_iff]; simp
  have hd : IsGateauxRepresentative KineticEnergyHamiltonian ω d := by
    intro ε hω hε
    convert hrep ε hω hε using 1
    apply integral_congr_ae
    filter_upwards [hae] with x hx
    simp [d, hx]
  obtain ⟨φ, hφ, hdeq⟩ := huniq d hd
  have key : ∀ y, ({(0 : T3)} : Set T3).indicator (fun _ => e) y = grad φ y := by
    intro y; have := congrFun hdeq y; simpa [d] using this
  have hg : Continuous fun y => grad φ y 0 := by
    simp_rw [grad_apply]
    exact (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hclosed : IsClosed {y : T3 | grad φ y 0 = 0} := isClosed_eq hg continuous_const
  have hsub : ({(0 : T3)}ᶜ : Set T3) ⊆ {y | grad φ y 0 = 0} := by
    intro y hy; simp only [Set.mem_setOf_eq]; rw [← key y]
    simp [Set.indicator_of_notMem hy]
  have h0 : grad φ 0 0 = 0 :=
    hclosed.closure_subset_iff.mpr hsub ((dense_compl_singleton (0 : T3)).closure_eq ▸ trivial)
  have := key 0
  rw [Set.indicator_of_mem (Set.mem_singleton _)] at this
  have h1 : e 0 = grad φ 0 0 := by rw [this]
  simp [e, h0] at h1

/-- Arnold bracket with the derivative fields given as data (choice-free). -/
noncomputable def ArnoldBracketOf (ω : CoadjointOrbit) (a b : T3 → EuclideanSpace ℝ (Fin 3)) : ℝ :=
  ∫ x, pairing (ω.val x) (cross (curl a x) (curl b x)) ∂(MeasureTheory.volume)

theorem arnoldBracketOf_antisymm (ω : CoadjointOrbit) (a b : T3 → EuclideanSpace ℝ (Fin 3)) :
    ArnoldBracketOf ω a b = -ArnoldBracketOf ω b a := by
  unfold ArnoldBracketOf
  rw [← integral_neg]
  congr 1; funext x
  simp only [pairing, cross]
  rw [← cross_anticomm, WithLp.toLp_neg, inner_neg_right]

theorem arnoldBracketOf_eq_zero_of_curl_parallel (ω : CoadjointOrbit)
    (a s : T3 → EuclideanSpace ℝ (Fin 3)) (c : ℝ) (hs : ∀ x, curl s x = c • ω.val x) :
    ArnoldBracketOf ω a s = 0 := by
  unfold ArnoldBracketOf
  have : ∀ x, pairing (ω.val x) (cross (curl a x) (curl s x)) = 0 := by
    intro x
    rw [hs x]
    simp only [pairing, cross, WithLp.ofLp_smul, LinearMap.map_smul]
    rw [WithLp.toLp_smul, inner_smul_right]
    simp only [PiLp.inner_apply, Fin.sum_univ_three, cross_apply]
    simp
    right
    rw [real_inner_eq_re_inner, real_inner_eq_re_inner, real_inner_eq_re_inner]
    simp only [RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
    ring
  simp [this]

theorem entropyCasimir_arnold (ω : CoadjointOrbit) (D : Functional → T3 → EuclideanSpace ℝ (Fin 3))
    (S : Functional) (c : ℝ) (hS : ∀ x, curl (D S) x = c • ω.val x) :
    EntropyCasimir (fun F G => ArnoldBracketOf ω (D F) (D G)) S := fun F =>
  arnoldBracketOf_eq_zero_of_curl_parallel ω (D F) (D S) c hS

end MetriplecticWorldModel
