import MetriplecticWorldModel.DiniCeiling

/-!
# Field-level log-loss stretching and the cubic-tether ceiling (reduction only)

* `FieldNetRate` (named Prop, coined): `ω·(ω·∇)u + ω·Tterm ≤ C Y³ − κ Y⁴` at every global maximizer.
* `field_uniform_ceiling_of_netRate` (**proved**): the Dini ceiling under `FieldNetRate` alone.
* `FieldStretchingLogLoss` (named Prop, coined): `ω·(ω·∇)u ≤ C₁ Y³ + C₂ Y³ log(1+Y)` at every
  global maximizer. **Not proved.** It is *not* the known Calderón–Zygmund/Beale–Kato–Majda
  estimate: that one reads `|∇u|∞ ≤ C(1 + Y(1 + log⁺(‖ω‖_{C^α}/Y)) + ‖ω‖_{L²})`, with a higher norm
  of `ω` inside the log. The `Y`-only form here is a strictly stronger hypothesis.
* `fieldNetRate_of_logLoss_cubicTether` (**proved**): log loss + cubic tether ⇒ `FieldNetRate`
  with `C = C₁ + κ/4 + 4C₂²/κ` and `κ_eff = 3κ/4`.
* `field_uniform_ceiling_logLoss_cubicTether` (**proved**): hence a uniform ceiling for every
  `κ > 0`, `C₂ ≥ 0` (no `κ > 4 C_abs` gap is needed here: the cross amplitude is `b = 0` at the
  field level).
-/

open Set Filter Topology

namespace MetriplecticWorldModel

section Vorticity

open NavierStokes3D Frohman.Tether
open scoped RealInnerProductSpace

def FieldNetRate (ω u Tterm : ℝ → VelocityField) (Y : ℝ → ℝ) (C κ : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ xs, (∀ x, ‖ω t x‖ ^ 2 ≤ ‖ω t xs‖ ^ 2) →
    ⟪ω t xs, convective (ω t) (u t) xs⟫ + ⟪ω t xs, Tterm t xs⟫ ≤ C * Y t ^ 3 - κ * Y t ^ 4

def FieldStretchingLogLoss (ω u : ℝ → VelocityField) (Y : ℝ → ℝ) (C₁ C₂ : ℝ) : Prop :=
  ∀ t, 0 ≤ t → ∀ xs, (∀ x, ‖ω t x‖ ^ 2 ≤ ‖ω t xs‖ ^ 2) →
    ⟪ω t xs, convective (ω t) (u t) xs⟫ ≤ C₁ * Y t ^ 3 + C₂ * Y t ^ 3 * Real.log (1 + Y t)

theorem field_uniform_ceiling_of_netRate (ν C κ : ℝ) (hν : 0 ≤ ν) (hκ : 0 < κ)
    (ω u Tterm : ℝ → VelocityField) (Y : ℝ → ℝ) (hpde : ModelVorticityPDE ν ω u Tterm)
    {K : Set T3} (hK : IsCompact K) (hne : K.Nonempty) (hsupp : ∀ s x, x ∉ K → ω s x = 0)
    (hreg : ∀ t, ContDiff ℝ 2 (ω t))
    (hc : Continuous (Function.uncurry ω)) (hct : Continuous (Function.uncurry (time_deriv ω)))
    (hd : ∀ s x, HasDerivAt (fun r => ω r x) (time_deriv ω s x) s)
    (hY : ∀ s, IsLUB (range fun x => ‖ω s x‖) (Y s))
    (hN : FieldNetRate ω u Tterm Y C κ) :
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
        inner_convective_eq_zero_of_max hdiff hmax]
      have h1 := hN t ht xs hmax
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

theorem fieldNetRate_of_logLoss_cubicTether (κ C₁ C₂ : ℝ) (hκ : 0 < κ) (hC₂ : 0 ≤ C₂)
    (ω u : ℝ → VelocityField) (Y : ℝ → ℝ) (hY : ∀ s, IsLUB (range fun x => ‖ω s x‖) (Y s))
    (hS : FieldStretchingLogLoss ω u Y C₁ C₂) :
    FieldNetRate ω u (cubicTether κ ω) Y (C₁ + κ / 4 + 4 * C₂ ^ 2 / κ) (3 * κ / 4) := by
  intro t ht xs hmax
  have hT := fieldTetherFeedback_cubicTether κ ω Y hY t ht xs hmax
  have hSt := hS t ht xs hmax
  have hy : 0 ≤ Y t := (norm_nonneg _).trans ((hY t).1 ⟨0, rfl⟩)
  set y := Y t
  set s := Real.sqrt (1 + y)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = 1 + y := Real.sq_sqrt (by linarith)
  have hlog : Real.log (1 + y) ≤ 2 * s := by
    have h := Real.log_le_sub_one_of_pos hs0
    have : Real.log (1 + y) = 2 * Real.log s := by
      rw [← hs2, Real.log_pow]; push_cast; ring
    rw [this]; linarith
  have h1 : C₂ * Real.log (1 + y) ≤ κ / 4 * (1 + y) + 4 * C₂ ^ 2 / κ := by
    have h2 : C₂ * (2 * s) ≤ κ / 4 * s ^ 2 + 4 * C₂ ^ 2 / κ := by
      have : κ / 4 * s ^ 2 + 4 * C₂ ^ 2 / κ - C₂ * (2 * s) = (κ * s - 4 * C₂) ^ 2 / (4 * κ) := by
        field_simp; ring
      nlinarith [div_nonneg (sq_nonneg (κ * s - 4 * C₂)) (by linarith : (0:ℝ) ≤ 4 * κ)]
    nlinarith [mul_le_mul_of_nonneg_left hlog hC₂]
  have hy3 : 0 ≤ y ^ 3 := pow_nonneg hy 3
  have h3 := mul_le_mul_of_nonneg_left h1 hy3
  rw [hT]
  nlinarith

theorem field_uniform_ceiling_logLoss_cubicTether (ν C₁ C₂ κ : ℝ) (hν : 0 ≤ ν) (hκ : 0 < κ)
    (hC₂ : 0 ≤ C₂) (ω u : ℝ → VelocityField) (Y : ℝ → ℝ)
    (hpde : ModelVorticityPDE ν ω u (cubicTether κ ω))
    {K : Set T3} (hK : IsCompact K) (hne : K.Nonempty) (hsupp : ∀ s x, x ∉ K → ω s x = 0)
    (hreg : ∀ t, ContDiff ℝ 2 (ω t))
    (hc : Continuous (Function.uncurry ω)) (hct : Continuous (Function.uncurry (time_deriv ω)))
    (hd : ∀ s x, HasDerivAt (fun r => ω r x) (time_deriv ω s x) s)
    (hY : ∀ s, IsLUB (range fun x => ‖ω s x‖) (Y s))
    (hS : FieldStretchingLogLoss ω u Y C₁ C₂) :
    ∀ t, 0 ≤ t → Y t ≤ ceiling (Y 0) (C₁ + κ / 4 + 4 * C₂ ^ 2 / κ) (3 * κ / 4) :=
  field_uniform_ceiling_of_netRate ν _ _ hν (by linarith) ω u _ Y hpde hK hne hsupp hreg hc hct
    hd hY (fieldNetRate_of_logLoss_cubicTether κ C₁ C₂ hκ hC₂ ω u Y hY hS)

end Vorticity

end MetriplecticWorldModel
