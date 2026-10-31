import MetriplecticWorldModel.MaxPointDanskin
import MetriplecticWorldModel.Ceiling

/-!
# The ceiling from an upper Dini bound (no differentiability of `sup|ω|`)

* `ceiling_of_upper_dini` (**proved**): `M` continuous on `[0,∞)` with the one-sided Dini bound
  `M(t+h) ≤ M t + h(R t + ε)` (small `h > 0`) and `R t < 0` whenever `M t > B` stays `≤ B` if
  `M 0 ≤ B`.
* `sup_continuous_of_uniform_support` (**proved**): `Y = sup|ω|` is continuous when `ω` is jointly
  continuous with all supports in one compact `K`.
* `field_uniform_ceiling` (**proved**): for a `ModelVorticityPDE` solution with uniform compact
  support, `C²` in space, `C¹` in time, `ν ≥ 0`, `κ > 0`, under `FieldStretchingBound` and
  `FieldTetherFeedback` only: `sup|ω(t)| ≤ ceiling (sup|ω(0)|) C κ` for all `t ≥ 0`.
  No `HasDerivAt Y`, no positivity of `Y`.
* `cubicTether` / `fieldTetherFeedback_cubicTether` (**proved**): for the concrete tether
  `Tterm = −κ|ω|²ω`, `FieldTetherFeedback` holds. For a general `Tterm` it does not follow
  (`ModelVorticityPDE` leaves `Tterm` free; false for `Tterm = 0`, `κ ≠ 0`, `Y ≠ 0`).
-/

open Set Filter Topology

namespace MetriplecticWorldModel

theorem ceiling_of_upper_dini {M R : ℝ → ℝ} {B : ℝ} (hc : ContinuousOn M (Ici 0))
    (h0 : M 0 ≤ B)
    (hD : ∀ t, 0 ≤ t → ∀ ε > 0, ∃ dl > 0, ∀ h, 0 < h → h < dl → M (t + h) ≤ M t + h * (R t + ε))
    (hR : ∀ t, 0 ≤ t → B < M t → R t < 0) : ∀ t, 0 ≤ t → M t ≤ B := by
  intro T hT
  refine le_of_forall_pos_le_add fun e he => ?_
  have key := image_le_of_liminf_slope_right_lt_deriv_boundary' (a := 0) (b := T) (f := M)
    (f' := R) (hc.mono Icc_subset_Ici_self) ?_ (B := fun _ => B + e) (B' := fun _ => 0)
    (by linarith) continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _) ?_
    ⟨hT, le_rfl⟩
  · exact key
  · intro x hx r hr
    obtain ⟨dl, hdl, hb⟩ := hD x hx.1 ((r - R x) / 2) (by linarith)
    have hev : ∀ᶠ z in 𝓝[>] x, slope M x z < r := by
      have : Ioo x (x + dl) ∈ 𝓝[>] x := Ioo_mem_nhdsGT (by linarith)
      filter_upwards [this] with z hz
      have hzx : 0 < z - x := by linarith [hz.1]
      have := hb (z - x) hzx (by linarith [hz.2])
      rw [add_sub_cancel] at this
      rw [slope_def_field, div_lt_iff₀ hzx]
      nlinarith
    exact hev.frequently
  · intro x hx hxe
    exact hR x hx.1 (by rw [hxe]; linarith)

section Vorticity

open NavierStokes3D Frohman.Tether
open scoped RealInnerProductSpace

theorem sup_eq_sSup_image {ω : VelocityField} {K : Set T3} (hne : K.Nonempty)
    (hsupp : ∀ x, x ∉ K → ω x = 0) {y : ℝ} (hY : IsLUB (range fun x => ‖ω x‖) y) :
    y = sSup ((fun x => ‖ω x‖) '' K) := by
  have hbdd : BddAbove ((fun x => ‖ω x‖) '' K) := ⟨y, fun _ ⟨x, _, hx⟩ => hY.1 ⟨x, hx⟩⟩
  apply le_antisymm
  · apply hY.2
    rintro _ ⟨x, rfl⟩
    by_cases hx : x ∈ K
    · exact le_csSup hbdd ⟨x, hx, rfl⟩
    · obtain ⟨x0, hx0⟩ := hne
      simp only [hsupp x hx, norm_zero]
      exact (norm_nonneg _).trans (le_csSup hbdd ⟨x0, hx0, rfl⟩)
  · exact csSup_le (hne.image _) fun _ ⟨x, _, hx⟩ => hY.1 ⟨x, hx⟩

theorem sup_continuous_of_uniform_support {ω : ℝ → VelocityField} {K : Set T3} {Y : ℝ → ℝ}
    (hK : IsCompact K) (hne : K.Nonempty) (hsupp : ∀ s x, x ∉ K → ω s x = 0)
    (hc : Continuous (Function.uncurry ω)) (hY : ∀ s, IsLUB (range fun x => ‖ω s x‖) (Y s)) :
    Continuous Y := by
  have : Y = fun s => sSup ((fun x => ‖ω s x‖) '' K) :=
    funext fun s => sup_eq_sSup_image hne (hsupp s) (hY s)
  rw [this]
  exact hK.continuous_sSup (f := fun s x => ‖ω s x‖) hc.norm

/-- **Uniform ceiling for an actual vorticity field, from the Dini bound alone.** -/
theorem field_uniform_ceiling (ν C κ : ℝ) (hν : 0 ≤ ν) (hκ : 0 < κ)
    (ω u Tterm : ℝ → VelocityField) (Y : ℝ → ℝ) (hpde : ModelVorticityPDE ν ω u Tterm)
    {K : Set T3} (hK : IsCompact K) (hne : K.Nonempty) (hsupp : ∀ s x, x ∉ K → ω s x = 0)
    (hreg : ∀ t, ContDiff ℝ 2 (ω t))
    (hc : Continuous (Function.uncurry ω)) (hct : Continuous (Function.uncurry (time_deriv ω)))
    (hd : ∀ s x, HasDerivAt (fun r => ω r x) (time_deriv ω s x) s)
    (hY : ∀ s, IsLUB (range fun x => ‖ω s x‖) (Y s))
    (hS : FieldStretchingBound ω u Y C) (hT : FieldTetherFeedback ω Tterm Y κ) :
    ∀ t, 0 ≤ t → Y t ≤ ceiling (Y 0) C κ := by
  have hY0 : ∀ s, 0 ≤ Y s := fun s =>
    (norm_nonneg _).trans ((hY s).1 ⟨0, rfl⟩)
  set c := ceiling (Y 0) C κ
  have hc0 : 0 ≤ c := le_trans (le_max_right _ _) (le_max_right _ _)
  have hcC : C / κ ≤ c := le_trans (le_max_left _ _) (le_max_right _ _)
  have hYc : Continuous Y := sup_continuous_of_uniform_support hK hne hsupp hc hY
  have key := ceiling_of_upper_dini (M := fun s => Y s ^ 2)
    (R := fun s => 2 * (C * Y s ^ 3 - κ * Y s ^ 4)) (B := c ^ 2)
    (hYc.pow 2).continuousOn (pow_le_pow_left₀ (hY0 0) (le_max_left _ _) 2) ?_ ?_
  · intro t ht
    exact (pow_le_pow_iff_left₀ (hY0 t) hc0 two_ne_zero).1 (key t ht)
  · intro t ht ε hε
    obtain ⟨xs, hmax, hdini⟩ := vorticity_danskin_upper_dini hK hne hsupp hc hct hd t
    have hYt : Y t = ‖ω t xs‖ := by
      refine (hY t).unique (IsGreatest.isLUB ⟨⟨xs, rfl⟩, ?_⟩)
      rintro _ ⟨x, rfl⟩
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (hmax x)
    have hdiff : Differentiable ℝ (ω t) := (hreg t).differentiable (by norm_num)
    have hrate : ⟪ω t xs, time_deriv ω t xs⟫ ≤ C * Y t ^ 3 - κ * Y t ^ 4 := by
      obtain ⟨-, -, hev⟩ := hpde t
      have he : time_deriv ω t xs = ν • laplacian (ω t) xs + Tterm t xs
          - convective (u t) (ω t) xs + convective (ω t) (u t) xs := by
        rw [← hev xs]; abel
      rw [he, inner_add_right, inner_sub_right, inner_add_right, inner_smul_right,
        inner_convective_eq_zero_of_max hdiff hmax, hT t ht xs hmax]
      have h1 := hS t ht xs hmax
      have h2 := mul_nonpos_of_nonneg_of_nonpos hν (inner_laplacian_nonpos_of_max (hreg t) hmax)
      linarith
    obtain ⟨dl, hdl, hb⟩ := hdini ε hε
    refine ⟨dl, hdl, fun h hh hhd => ?_⟩
    set b := ‖ω t xs‖ ^ 2 + h * (2 * ⟪ω t xs, time_deriv ω t xs⟫ + ε)
    have hb0 : 0 ≤ b := (sq_nonneg _).trans (hb h hh hhd xs)
    have hYle : Y (t + h) ≤ Real.sqrt b := (hY (t + h)).2 (by
      rintro _ ⟨x, rfl⟩
      exact Real.le_sqrt_of_sq_le (hb h hh hhd x))
    have hsq : Y (t + h) ^ 2 ≤ b := by
      calc Y (t + h) ^ 2 ≤ Real.sqrt b ^ 2 := pow_le_pow_left₀ (hY0 _) hYle 2
        _ = b := Real.sq_sqrt hb0
    show Y (t + h) ^ 2 ≤ Y t ^ 2 + h * (2 * (C * Y t ^ 3 - κ * Y t ^ 4) + ε)
    rw [hYt] at hrate ⊢
    nlinarith
  · intro t _ hlt
    simp only at hlt ⊢
    have hgt : c < Y t := by
      by_contra hn; replace hn := not_lt.1 hn
      nlinarith [pow_le_pow_left₀ (hY0 t) hn 2]
    have hpos : 0 < Y t := lt_of_le_of_lt hc0 hgt
    have hneg : C - κ * Y t < 0 := by
      have := (div_le_iff₀ hκ).1 hcC; nlinarith
    have : C * Y t ^ 3 - κ * Y t ^ 4 = Y t ^ 3 * (C - κ * Y t) := by ring
    have h3 : 0 < Y t ^ 3 := by positivity
    nlinarith

/-- The concrete cubic tether forcing `Tterm = −κ |ω|² ω` (coined). -/
noncomputable def cubicTether (κ : ℝ) (ω : ℝ → VelocityField) : ℝ → VelocityField :=
  fun t x => (-κ * ‖ω t x‖ ^ 2) • ω t x

theorem fieldTetherFeedback_cubicTether (κ : ℝ) (ω : ℝ → VelocityField) (Y : ℝ → ℝ)
    (hY : ∀ s, IsLUB (range fun x => ‖ω s x‖) (Y s)) :
    FieldTetherFeedback ω (cubicTether κ ω) Y κ := by
  intro t _ xs hmax
  have hYt : Y t = ‖ω t xs‖ := by
    refine (hY t).unique (IsGreatest.isLUB ⟨⟨xs, rfl⟩, ?_⟩)
    rintro _ ⟨x, rfl⟩
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 (hmax x)
  simp only [cubicTether, inner_smul_right, real_inner_self_eq_norm_sq, hYt]
  ring

/-- Ceiling for the cubic tether: only `FieldStretchingBound` remains. -/
theorem field_uniform_ceiling_cubicTether (ν C κ : ℝ) (hν : 0 ≤ ν) (hκ : 0 < κ)
    (ω u : ℝ → VelocityField) (Y : ℝ → ℝ) (hpde : ModelVorticityPDE ν ω u (cubicTether κ ω))
    {K : Set T3} (hK : IsCompact K) (hne : K.Nonempty) (hsupp : ∀ s x, x ∉ K → ω s x = 0)
    (hreg : ∀ t, ContDiff ℝ 2 (ω t))
    (hc : Continuous (Function.uncurry ω)) (hct : Continuous (Function.uncurry (time_deriv ω)))
    (hd : ∀ s x, HasDerivAt (fun r => ω r x) (time_deriv ω s x) s)
    (hY : ∀ s, IsLUB (range fun x => ‖ω s x‖) (Y s)) (hS : FieldStretchingBound ω u Y C) :
    ∀ t, 0 ≤ t → Y t ≤ ceiling (Y 0) C κ :=
  field_uniform_ceiling ν C κ hν hκ ω u _ Y hpde hK hne hsupp hreg hc hct hd hY hS
    (fieldTetherFeedback_cubicTether κ ω Y hY)

end Vorticity

end MetriplecticWorldModel
