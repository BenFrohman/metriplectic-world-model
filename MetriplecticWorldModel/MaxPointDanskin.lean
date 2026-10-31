/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import MetriplecticWorldModel.SmoothOrbit
import MetriplecticWorldModel.Model

/-!
# Maximizer data from an actual vorticity field (Danskin-type envelope)

* `danskin_upper_dini` (**proved**): for `f, ∂ₜf` jointly continuous on `ℝ × K`, `K` compact,
  the upper right Dini derivative of `t ↦ sup_K f t` is at most `∂ₜf(t,x⋆)` at a maximizer `x⋆`.
* `vorticity_danskin_upper_dini` (**proved**): the same for `|ω(t)|²`, `ω` with fixed compact support.
* `hasDerivAt_eq_of_touch_below`, `sup_mul_deriv_eq_inner` (**proved**): if `Y = sup|ω|` is
  differentiable at `t`, then `Y Y' = ω·∂ₜω` at every global maximizer.
* `inner_convective_eq_zero_of_max` (**proved**): advection drops out at the max.
* `deriv2_nonpos_of_isLocalMax`, `inner_laplacian_nonpos_of_max` (**proved**): maximum principle
  `ω·Δω ≤ 0` at a global max of `|ω|²` for `C²` fields.
* `maxPointRealization_of_field` (**proved**): `MaxPointRealization` from a solution of
  `ModelVorticityPDE`, with `EnergyIdentity`, `ViscousAtMax`, `CrossControlled` discharged;
  remaining hypotheses: `FieldStretchingBound`, `FieldTetherFeedback`, differentiability of `Y`.
  (Danskin only gives a one-sided Dini bound; replacing `HasDerivAt Y` by it in the ceiling
  argument is open.)
-/

open Set Filter Topology

namespace MetriplecticWorldModel

/-- Touching from below: if `g ≤ m` everywhere with equality at `t`, and both are differentiable
at `t`, the derivatives agree. -/
theorem hasDerivAt_eq_of_touch_below {m g : ℝ → ℝ} {t m' g' : ℝ} (hle : ∀ s, g s ≤ m s)
    (heq : g t = m t) (hm : HasDerivAt m m' t) (hg : HasDerivAt g g' t) : m' = g' := by
  have hmin : IsLocalMin (fun s => m s - g s) t :=
    Filter.Eventually.of_forall fun s => by simp only; linarith [hle s]
  have := hmin.hasDerivAt_eq_zero (hm.sub hg)
  linarith

/-- Uniform-in-`x` continuity in time on a compact set. -/
theorem eventually_forall_abs_sub_lt {X : Type*} [TopologicalSpace X] {K : Set X}
    (hK : IsCompact K) {φ : ℝ → X → ℝ} (hφ : Continuous (Function.uncurry φ)) (t : ℝ)
    {dl : ℝ} (hdl : 0 < dl) : ∀ᶠ s in 𝓝 t, ∀ x ∈ K, |φ s x - φ t x| < dl := by
  refine hK.eventually_forall_of_forall_eventually fun y _ => ?_
  have hc : Continuous fun z : ℝ × X => φ z.1 z.2 - φ t z.2 :=
    hφ.sub (hφ.comp (continuous_const.prodMk continuous_snd))
  have h0 : (fun z : ℝ × X => φ z.1 z.2 - φ t z.2) (t, y) = 0 := by simp
  have := hc.continuousAt (x := (t, y)) |>.eventually (Metric.ball_mem_nhds _ hdl)
  rw [h0] at this
  filter_upwards [this] with z hz
  simpa [Real.dist_eq] using hz

/-- **Danskin-type upper Dini bound.** Let `K` be compact and nonempty, `f, f'` jointly
continuous with `∂ₜ f = f'`. Then there is a maximizer `x⋆` of `f t` on `K` such that for every
`ε > 0` and all small `h > 0`, `sup_K f(t+h) ≤ f(t,x⋆) + h (f'(t,x⋆) + ε)`; i.e. the upper right
Dini derivative of `t ↦ sup_K f t` is at most `∂ₜ f(t,x⋆)`. -/
theorem danskin_upper_dini {X : Type*} [TopologicalSpace X] {K : Set X} (hK : IsCompact K)
    (hne : K.Nonempty) {f f' : ℝ → X → ℝ} (hf : Continuous (Function.uncurry f))
    (hf' : Continuous (Function.uncurry f'))
    (hd : ∀ s x, HasDerivAt (fun r => f r x) (f' s x) s) (t : ℝ) :
    ∃ xs ∈ K, IsMaxOn (f t) K xs ∧ ∀ ε > 0, ∃ dl > 0, ∀ h, 0 < h → h < dl →
      ∀ x ∈ K, f (t + h) x ≤ f t xs + h * (f' t xs + ε) := by
  have hft : Continuous (f t) := hf.comp (continuous_const.prodMk continuous_id)
  have hf't : Continuous (f' t) := hf'.comp (continuous_const.prodMk continuous_id)
  obtain ⟨x0, hx0K, hx0⟩ := hK.exists_isMaxOn hne hft.continuousOn
  set A := K ∩ {x | f t x = f t x0} with hA
  have hAc : IsCompact A := hK.inter_right (isClosed_eq hft continuous_const)
  obtain ⟨xs, hxsA, hxs⟩ := hAc.exists_isMaxOn ⟨x0, hx0K, rfl⟩ hf't.continuousOn
  have hxsK : xs ∈ K := hxsA.1
  have hfxs : f t xs = f t x0 := hxsA.2
  have hmax : IsMaxOn (f t) K xs := fun x hx => by
    simp only [mem_setOf_eq]; rw [hfxs]; exact hx0 hx
  refine ⟨xs, hxsK, hmax, fun ε hε => ?_⟩
  set D := f' t xs
  set U := {x | f' t x < D + ε / 2}
  have hUo : IsOpen U := isOpen_lt hf't continuous_const
  have hC : IsCompact (K \ U) := hK.diff hUo
  -- gap `η` of `f t` below its max on `K \ U`
  obtain ⟨η, hη, hgap⟩ : ∃ η > 0, ∀ x ∈ K \ U, f t x ≤ f t xs - η := by
    rcases (K \ U).eq_empty_or_nonempty with he | hne'
    · exact ⟨1, one_pos, fun x hx => by rw [he] at hx; exact hx.elim⟩
    obtain ⟨c, hcC, hc⟩ := hC.exists_isMaxOn hne' hft.continuousOn
    have hlt : f t c < f t xs := by
      rcases (show f t c ≤ f t xs from hmax hcC.1).lt_or_eq with h | h
      · exact h
      · exfalso
        have hcA : c ∈ A := ⟨hcC.1, by simp only [mem_setOf_eq]; rw [h, hfxs]⟩
        have : f' t c ≤ D := hxs hcA
        exact hcC.2 (by simp only [U, mem_setOf_eq]; linarith)
    exact ⟨f t xs - f t c, by linarith, fun x hx => by have := hc hx; simp at this; linarith⟩
  have e1 := eventually_forall_abs_sub_lt hK hf' t (half_pos hε)
  have e2 := eventually_forall_abs_sub_lt hK hf t (half_pos hη)
  obtain ⟨dl1, hdl1, h1⟩ := Metric.eventually_nhds_iff.1 e1
  obtain ⟨dl2, hdl2, h2⟩ := Metric.eventually_nhds_iff.1 e2
  set dl3 := η / (2 * (|D + ε| + 1))
  have hdl3 : 0 < dl3 := by positivity
  refine ⟨min dl1 (min dl2 dl3), lt_min hdl1 (lt_min hdl2 hdl3), fun h hh0 hhdl x hx => ?_⟩
  have hhdl1 : h < dl1 := lt_of_lt_of_le hhdl (min_le_left _ _)
  have hhdl2 : h < dl2 := lt_of_lt_of_le hhdl ((min_le_right _ _).trans (min_le_left _ _))
  have hhdl3 : h < dl3 := lt_of_lt_of_le hhdl ((min_le_right _ _).trans (min_le_right _ _))
  have hlow : -(η / 2) ≤ h * (D + ε) := by
    have hpos : 0 < 2 * (|D + ε| + 1) := by positivity
    have : h * (2 * (|D + ε| + 1)) < η := by
      have := (lt_div_iff₀ hpos).1 hhdl3; linarith
    have hab := neg_abs_le (D + ε)
    nlinarith [abs_nonneg (D + ε)]
  by_cases hxU : x ∈ U
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope (fun r => f r x) (fun r => f' r x)
      (show t < t + h by linarith)
      (fun r _ => (hd r x).continuousAt.continuousWithinAt) (fun r _ => hd r x)
    have hcd : dist c t < dl1 := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [hc.1, hc.2]
    have hbound := (abs_lt.1 (h1 hcd x hx)).2
    simp only [add_sub_cancel_left] at hcs
    have hxU' : f' t x < D + ε / 2 := hxU
    have hdiff : f (t + h) x - f t x = h * f' c x := by
      rw [hcs]; field_simp
    have := hmax hx
    simp only [mem_setOf_eq] at this
    nlinarith
  · have hxC : x ∈ K \ U := ⟨hx, hxU⟩
    have hd2 : dist (t + h) t < dl2 := by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have := (abs_lt.1 (h2 hd2 x hx)).2
    have := hgap x hxC
    linarith

/-- One-dimensional second-derivative test: at a local max of a differentiable `g` whose
derivative `g'` has derivative `g2` at `a`, `g2 ≤ 0`. -/
theorem deriv2_nonpos_of_isLocalMax {g g' : ℝ → ℝ} {a g2 : ℝ}
    (hg : ∀ s, HasDerivAt g (g' s) s) (hg' : HasDerivAt g' g2 a) (hmax : IsLocalMax g a) :
    g2 ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have h0 : g' a = 0 := hmax.hasDerivAt_eq_zero (hg a)
  have hsl := hasDerivAt_iff_tendsto_slope.1 hg'
  have hev : ∀ᶠ c in 𝓝[>] a, 0 < slope g' a c :=
    (hsl.mono_left (nhdsWithin_mono _ (fun x hx => ne_of_gt hx))).eventually (lt_mem_nhds hpos)
  have hev' : ∀ᶠ c in 𝓝[>] a, 0 < g' c := by
    filter_upwards [hev, self_mem_nhdsWithin] with c hc hca
    rw [slope_def_field, h0, sub_zero] at hc
    have : 0 < c - a := sub_pos.2 hca
    exact (div_pos_iff_of_pos_right this).1 hc
  obtain ⟨dl, hdl, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev')
  have hmax' := Metric.eventually_nhds_iff.1 hmax
  obtain ⟨dl', hdl', hm⟩ := hmax'
  set s := a + min dl dl' / 2
  have hs : a < s := by simp only [s]; have := lt_min hdl hdl'; linarith
  have hsd : dist s a < dl' := by
    rw [Real.dist_eq, abs_lt]; constructor <;> simp only [s] <;>
      linarith [min_le_right dl dl', lt_min hdl hdl']
  obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope g g' hs
    (fun r _ => (hg r).continuousAt.continuousWithinAt) (fun r _ => hg r)
  have hcd : dist c a < dl := by
    rw [Real.dist_eq, abs_lt]; constructor <;> simp only [s] at hc <;>
      linarith [hc.1, hc.2, min_le_left dl dl', lt_min hdl hdl']
  have hgc : 0 < g' c := hball hcd hc.1
  have : g a < g s := by
    rw [hcs] at hgc
    have := (div_pos_iff_of_pos_right (sub_pos.2 hs)).1 hgc; linarith
  have := hm hsd
  simp only at this; linarith


section Field
open NavierStokes3D
open scoped RealInnerProductSpace

/-- Derivative of `ω` along the line `s ↦ x + s • w`. -/
theorem hasDerivAt_line {ω : VelocityField} (hω : Differentiable ℝ ω) (x w : T3) (s : ℝ) :
    HasDerivAt (fun r : ℝ => ω (x + r • w)) (fderiv ℝ ω (x + s • w) w) s := by
  have hl : HasDerivAt (fun r : ℝ => x + r • w) w s := by
    simpa using ((hasDerivAt_id s).smul_const w).const_add x
  exact (hω (x + s • w)).hasFDerivAt.comp_hasDerivAt s hl

/-- At a global maximizer of `|ω|²`, `ω · ∂_w ω = 0` for every direction `w`
(`∇|ω|² = 0`). -/
theorem inner_fderiv_eq_zero_of_max {ω : VelocityField} (hω : Differentiable ℝ ω) {xs : T3}
    (hmax : ∀ x, ‖ω x‖ ^ 2 ≤ ‖ω xs‖ ^ 2) (w : T3) : ⟪ω xs, fderiv ℝ ω xs w⟫ = 0 := by
  have hd := (hasDerivAt_line hω xs w 0).norm_sq
  have hlm : IsLocalMax (fun r : ℝ => ‖ω (xs + r • w)‖ ^ 2) 0 :=
    Filter.Eventually.of_forall fun r => by simpa using hmax (xs + r • w)
  have := hlm.hasDerivAt_eq_zero (by simpa using hd)
  simpa using this

/-- **Advection vanishes at a maximizer**: `ω · (v·∇)ω = 0` at a global max of `|ω|²`. -/
theorem inner_convective_eq_zero_of_max {ω : VelocityField} (hω : Differentiable ℝ ω)
    {xs : T3} (hmax : ∀ x, ‖ω x‖ ^ 2 ≤ ‖ω xs‖ ^ 2) (v : VelocityField) :
    ⟪ω xs, convective v ω xs⟫ = 0 :=
  inner_fderiv_eq_zero_of_max hω hmax (v xs)

/-- Second derivative along a coordinate line at a maximizer: `ω · ∂_w² ω ≤ −|∂_w ω|² ≤ 0`. -/
theorem inner_second_deriv_nonpos_of_max {ω : VelocityField}
    (hω : ContDiff ℝ 2 ω) {xs : T3} (hmax : ∀ x, ‖ω x‖ ^ 2 ≤ ‖ω xs‖ ^ 2) (w : T3) :
    ⟪ω xs, fderiv ℝ (fun y => fderiv ℝ ω y w) xs w⟫ ≤ 0 := by
  have hd1 : Differentiable ℝ ω := hω.differentiable (by norm_num)
  have hC1 : ContDiff ℝ 1 (fun y => fderiv ℝ ω y w) :=
    (hω.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hd2 : Differentiable ℝ (fun y => fderiv ℝ ω y w) := hC1.differentiable (by norm_num)
  set ℓ' : ℝ → EuclideanSpace ℝ (Fin 3) := fun s => fderiv ℝ ω (xs + s • w) w
  have hℓ' : HasDerivAt ℓ' (fderiv ℝ (fun y => fderiv ℝ ω y w) xs w) 0 := by
    have := hasDerivAt_line hd2 xs w 0
    simpa [ℓ'] using this
  have hg : ∀ s, HasDerivAt (fun r : ℝ => ‖ω (xs + r • w)‖ ^ 2)
      (2 * ⟪ω (xs + s • w), ℓ' s⟫) s := fun s => (hasDerivAt_line hd1 xs w s).norm_sq
  have hg' : HasDerivAt (fun s => 2 * ⟪ω (xs + s • w), ℓ' s⟫)
      (2 * (⟪ω (xs + (0:ℝ) • w), fderiv ℝ (fun y => fderiv ℝ ω y w) xs w⟫ +
        ⟪fderiv ℝ ω (xs + (0:ℝ) • w) w, ℓ' 0⟫)) 0 :=
    ((hasDerivAt_line hd1 xs w 0).inner ℝ hℓ').const_mul 2
  have hlm : IsLocalMax (fun r : ℝ => ‖ω (xs + r • w)‖ ^ 2) 0 :=
    Filter.Eventually.of_forall fun r => by simpa using hmax (xs + r • w)
  have := deriv2_nonpos_of_isLocalMax hg hg' hlm
  simp only [zero_smul, add_zero, ℓ'] at this
  have hsq : 0 ≤ ⟪fderiv ℝ ω xs w, fderiv ℝ ω xs w⟫ := real_inner_self_nonneg
  linarith

/-- **Maximum principle for the viscous term**: `ω · Δω ≤ 0` at a global max of `|ω|²`
(`ω` of class `C²`). -/
theorem inner_laplacian_nonpos_of_max {ω : VelocityField} (hω : ContDiff ℝ 2 ω) {xs : T3}
    (hmax : ∀ x, ‖ω x‖ ^ 2 ≤ ‖ω xs‖ ^ 2) : ⟪ω xs, laplacian ω xs⟫ ≤ 0 := by
  unfold laplacian
  rw [inner_sum]
  exact Finset.sum_nonpos fun i _ => inner_second_deriv_nonpos_of_max hω hmax _

end Field


section Vorticity
open NavierStokes3D Frohman.Tether
open scoped RealInnerProductSpace

/-- **Danskin bound for the vorticity maximum.** For a time-dependent vorticity `ω` supported in
a fixed compact `K`, jointly continuous with jointly continuous `∂ₜω`, at each `t` there is a
global maximizer `x⋆` of `|ω(t)|²` such that for every `ε > 0` and small `h > 0`,
`|ω(t+h,x)|² ≤ |ω(t,x⋆)|² + h (∂ₜ|ω|²(t,x⋆) + ε)` for all `x`. -/
theorem vorticity_danskin_upper_dini {ω : ℝ → VelocityField} {K : Set T3} (hK : IsCompact K)
    (hne : K.Nonempty) (hsupp : ∀ s x, x ∉ K → ω s x = 0)
    (hc : Continuous (Function.uncurry ω)) (hct : Continuous (Function.uncurry (time_deriv ω)))
    (hd : ∀ s x, HasDerivAt (fun r => ω r x) (time_deriv ω s x) s) (t : ℝ) :
    ∃ xs, (∀ x, ‖ω t x‖ ^ 2 ≤ ‖ω t xs‖ ^ 2) ∧ ∀ ε > 0, ∃ dl > 0, ∀ h, 0 < h → h < dl →
      ∀ x, ‖ω (t + h) x‖ ^ 2 ≤ ‖ω t xs‖ ^ 2 + h * (2 * ⟪ω t xs, time_deriv ω t xs⟫ + ε) := by
  have hf : Continuous (Function.uncurry fun s x => ‖ω s x‖ ^ 2) := (hc.norm).pow 2
  have hf' : Continuous (Function.uncurry fun s x => 2 * ⟪ω s x, time_deriv ω s x⟫) :=
    continuous_const.mul (hc.inner hct)
  obtain ⟨xs, hxsK, hmax, hdini⟩ := danskin_upper_dini hK hne hf hf'
    (fun s x => (hd s x).norm_sq) t
  have hglob : ∀ x, ‖ω t x‖ ^ 2 ≤ ‖ω t xs‖ ^ 2 := fun x => by
    by_cases hx : x ∈ K
    · exact hmax hx
    · rw [hsupp t x hx]; simp
  refine ⟨xs, hglob, fun ε hε => ?_⟩
  obtain ⟨dl, hdl, hb⟩ := hdini ε hε
  refine ⟨dl, hdl, fun h h0 hh x => ?_⟩
  by_cases hx : x ∈ K
  · exact hb h h0 hh x hx
  · rw [hsupp _ x hx, norm_zero]
    obtain ⟨k, hk⟩ := hne
    have := hb h h0 hh k hk
    have : (0:ℝ) ≤ ‖ω (t + h) k‖ ^ 2 := by positivity
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]; linarith

/-- If `Y = sup|ω|` is differentiable at `t`, then `Y Y' = ω·∂ₜω` at **every** global maximizer
(touching from below; no compactness needed). This is the left side of `EnergyIdentity`. -/
theorem sup_mul_deriv_eq_inner {ω : ℝ → VelocityField} {Y : ℝ → ℝ} {t Y' : ℝ} {xs : T3}
    (hY : ∀ s, IsLUB (range fun x => ‖ω s x‖) (Y s)) (hYd : HasDerivAt Y Y' t)
    (hd : ∀ x, HasDerivAt (fun r => ω r x) (time_deriv ω t x) t)
    (hmax : ∀ x, ‖ω t x‖ ^ 2 ≤ ‖ω t xs‖ ^ 2) :
    Y t * Y' = ⟪ω t xs, time_deriv ω t xs⟫ := by
  have hYt : Y t = ‖ω t xs‖ := by
    refine (hY t).unique (IsGreatest.isLUB ⟨⟨xs, rfl⟩, ?_⟩)
    rintro _ ⟨x, rfl⟩
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (hmax x)
  have hle : ∀ s, ‖ω s xs‖ ^ 2 ≤ Y s ^ 2 := fun s =>
    pow_le_pow_left₀ (norm_nonneg _) ((hY s).1 ⟨xs, rfl⟩) 2
  have := hasDerivAt_eq_of_touch_below hle (by rw [hYt]) (hYd.pow 2) (hd xs).norm_sq
  simp at this; linarith

/-- Named Prop (field-level stretching bound; the only genuinely analytic hypothesis left):
`ω·(ω·∇)u ≤ C Y³` at every global maximizer of `|ω(t)|²`, `t ≥ 0`. -/
def FieldStretchingBound (ω u : ℝ → VelocityField) (Y : ℝ → ℝ) (C : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ xs, (∀ x, ‖ω t x‖ ^ 2 ≤ ‖ω t xs‖ ^ 2) →
    ⟪ω t xs, convective (ω t) (u t) xs⟫ ≤ C * Y t ^ 3

/-- Named Prop (field-level tether feedback; model-specific, false for `Tterm = 0`, `κY ≠ 0`):
`ω·Tterm = −κ Y⁴` at every global maximizer, `t ≥ 0`. -/
def FieldTetherFeedback (ω Tterm : ℝ → VelocityField) (Y : ℝ → ℝ) (κ : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ xs, (∀ x, ‖ω t x‖ ^ 2 ≤ ‖ω t xs‖ ^ 2) →
    ⟪ω t xs, Tterm t xs⟫ = -κ * Y t ^ 4

/-- The maximizer data read off an actual vorticity field at a maximizer `xs` at time `t`:
`St = ω·(ω·∇)u`, `V = ν ω·Δω`, `tetherTerm = ω·Tterm`, cross amplitude `b = 0`. -/
noncomputable def fieldMaxPointData (ν : ℝ) (ω u Tterm : ℝ → VelocityField) (Y Y' : ℝ → ℝ)
    (t : ℝ) (xs : T3) : MaxPointData where
  y := Y t
  y' := Y' t
  St := ⟪ω t xs, convective (ω t) (u t) xs⟫
  V := ν * ⟪ω t xs, laplacian (ω t) xs⟫
  tetherTerm := ⟪ω t xs, Tterm t xs⟫
  b := 0

/-- **`MaxPointRealization` from an actual vorticity field.** For a solution of
`ModelVorticityPDE ν` (`ν ≥ 0`) with `ω(t)` of class `C²` and compactly supported, `C¹` in time,
`Y = sup|ω|` positive and differentiable: `EnergyIdentity` (advection term vanishes at the
max), `ViscousAtMax` (maximum principle), `CrossControlled` (`b = 0`, `C_abs ≥ 0`) and the
`y, y'` links are **proved**; only `FieldStretchingBound` and `FieldTetherFeedback` remain as
named hypotheses (plus differentiability of `Y`). -/
theorem maxPointRealization_of_field (ν C κ Cabs : ℝ) (hν : 0 ≤ ν) (hCabs : 0 ≤ Cabs)
    (ω u Tterm : ℝ → VelocityField) (Y Y' : ℝ → ℝ) (hpde : ModelVorticityPDE ν ω u Tterm)
    (hreg : ∀ t, ContDiff ℝ 2 (ω t)) (hsupp : ∀ t, HasCompactSupport (ω t))
    (hd : ∀ s x, HasDerivAt (fun r => ω r x) (time_deriv ω s x) s)
    (hY : ∀ s, IsLUB (range fun x => ‖ω s x‖) (Y s))
    (hYd : ∀ t, 0 ≤ t → HasDerivAt Y (Y' t) t) (hpos : ∀ t, 0 ≤ t → 0 < Y t)
    (hS : FieldStretchingBound ω u Y C) (hT : FieldTetherFeedback ω Tterm Y κ) :
    MaxPointRealization C κ Cabs Y Y' := by
  refine ⟨hYd, fun t ht => ?_⟩
  have hcont : Continuous fun x => ‖ω t x‖ ^ 2 :=
    ((hreg t).continuous.norm).pow 2
  have hcs : HasCompactSupport fun x => ‖ω t x‖ ^ 2 :=
    (hsupp t).comp_left (g := fun v : EuclideanSpace ℝ (Fin 3) => ‖v‖ ^ 2) (by simp)
  obtain ⟨xs, hxs⟩ := hcont.exists_forall_ge_of_hasCompactSupport hcs
  have hmax : ∀ x, ‖ω t x‖ ^ 2 ≤ ‖ω t xs‖ ^ 2 := hxs
  have hdiff : Differentiable ℝ (ω t) := (hreg t).differentiable (by norm_num)
  refine ⟨fieldMaxPointData ν ω u Tterm Y Y' t xs, rfl, rfl, hpos t ht, ?_, ?_, ?_, ?_, ?_⟩
  · unfold EnergyIdentity fieldMaxPointData
    simp only
    rw [sup_mul_deriv_eq_inner hY (hYd t ht) (fun x => hd t x) hmax]
    obtain ⟨-, -, hev⟩ := hpde t
    have he : time_deriv ω t xs = ν • laplacian (ω t) xs + Tterm t xs
        - convective (u t) (ω t) xs + convective (ω t) (u t) xs := by
      rw [← hev xs]; abel
    rw [he, inner_add_right, inner_sub_right, inner_add_right, inner_smul_right,
      inner_convective_eq_zero_of_max hdiff hmax]
    ring
  · exact hS t ht xs hmax
  · unfold ViscousAtMax fieldMaxPointData
    exact mul_nonpos_of_nonneg_of_nonpos hν (inner_laplacian_nonpos_of_max (hreg t) hmax)
  · exact hT t ht xs hmax
  · unfold CrossControlled fieldMaxPointData
    simp only; norm_num; exact mul_nonneg hCabs (pow_nonneg (hpos t ht).le 4)

end Vorticity

end MetriplecticWorldModel
