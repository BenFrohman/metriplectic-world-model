/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.ConjExponents
public import FrohmanianSymplecticTether.NS_Equations
public import FrohmanianSymplecticTether.SymplecticTether

/-!
# Frohmanian Tether analytic pipeline

Three Lean 4 gates connecting the quartic Lyapunov variation to BKM:

1. `youngs_absorption_elimination` — algebraic cancellation of the factor `4`
   (`ε_abs = κ/4`), residual `-(3/4) κ I₆`.
2. `comparison_ode_stability` — phase-plane upper bound
   `y(t) ≤ max(y(0), C/κ'')` for any differentiable solution of
   `y' ≤ C y² − κ'' y³`.
3. `bkm_regularity_pipeline` — uniform bound + continuity of `M(t)` gives
   `IntegrableOn` on every compact time interval, hence BKM smoothness.

`kappa` is the defined constant from `SymplecticTether` (not an axiom).
-/

open FrohmanianTether NavierStokes3D
open MeasureTheory hiding volume
open Set Filter

namespace AnalyticPipeline

variable {kappa : ℝ}

/-- Vector field of the independent majorant: `f(z) = z² (C − κ'' z)`. -/
public theorem majorant_vector_field_eq (C κ'' z : ℝ) :
    C * z ^ 2 - κ'' * z ^ 3 = z ^ 2 * (C - κ'' * z) := by
  ring

/-- Strictly above the equilibrium `C/κ''`, the cubic field is negative. -/
public theorem majorant_vector_field_neg_of_gt
    {C κ'' z : ℝ} (hC : 0 < C) (hκ : 0 < κ'') (hz : C / κ'' < z) :
    C * z ^ 2 - κ'' * z ^ 3 < 0 := by
  have hzpos : 0 < z := lt_trans (div_pos hC hκ) hz
  have hz2 : 0 < z ^ 2 := sq_pos_of_pos hzpos
  have hlin : C - κ'' * z < 0 := by
    have hmul : κ'' * (C / κ'') < κ'' * z := mul_lt_mul_of_pos_left hz hκ
    rw [mul_div_cancel₀ C (ne_of_gt hκ)] at hmul
    linarith [hmul]
  rw [majorant_vector_field_eq]
  exact mul_neg_of_pos_of_neg hz2 hlin

/-- Algebraic elimination of the quartic factor `4` after Young with `ε_abs = κ/4`.

Matches the manuscript identity
`(4 C_CZ(3) M I₄) − κ I₆ ≤ C_abs M³ |φ|_∞^{3/2} − (3/4) κ I₆`.
`linarith` closes the step; `C_abs` stays a parameter. -/
public theorem youngs_absorption_elimination
    (M I₄ I₆ phi_norm C_abs : ℝ)
    (_h_I6_nonneg : 0 ≤ I₆)
    (h_young :
      4 * CalderonZygmundConstant3D * M * I₄ ≤
        (kappa / 4) * I₆ + C_abs * (M ^ 3 * phi_norm ^ ((3 : ℝ) / 2))) :
    4 * CalderonZygmundConstant3D * M * I₄ - kappa * I₆ ≤
      C_abs * (M ^ 3 * phi_norm ^ ((3 : ℝ) / 2)) -
        (3 / 4 : ℝ) * kappa * I₆ := by
  linarith

/-- Phase-plane upper bound for the Riccati differential *inequality*
`y' ≤ C y² − κ'' y³`.

The constant barrier `Y = max(y 0, C/κ'')` cannot be crossed: at any contact
with `Y + ε` (`ε > 0`) the vector field is strictly negative. Letting `ε → 0`
gives the uniform bound. This is the scalar comparison used for `M_ε(t)`. -/
public theorem comparison_ode_stability
    (C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'')
    (y : ℝ → ℝ)
    (hdiff : ∀ s ≥ (0 : ℝ), DifferentiableAt ℝ y s)
    (hy_dot : ∀ s ≥ (0 : ℝ), deriv y s ≤ C * (y s) ^ 2 - κ'' * (y s) ^ 3)
    (t : ℝ) (ht : 0 ≤ t) :
    y t ≤ max (y 0) (C / κ'') := by
  set Y := max (y 0) (C / κ'')
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hbarrier : C / κ'' < Y + ε :=
    lt_of_le_of_lt (le_max_right (y 0) (C / κ'')) (lt_add_of_pos_right _ hε)
  have hy0 : y 0 ≤ Y + ε :=
    (le_max_left (y 0) (C / κ'')).trans (le_add_of_nonneg_right hε.le)
  have hyC : ContinuousOn y (Icc (0 : ℝ) t) := fun x hx =>
    (hdiff x hx.1).continuousAt.continuousWithinAt
  have hyW : ∀ x ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt y (deriv y x) (Ici x) x := fun x hx =>
    (hdiff x hx.1).hasDerivAt.hasDerivWithinAt
  have hB : ∀ x, HasDerivAt (fun _ : ℝ => Y + ε) (0 : ℝ) x := fun x =>
    hasDerivAt_const x (Y + ε)
  have hcontact : ∀ x ∈ Ico (0 : ℝ) t, y x = Y + ε → deriv y x < 0 := by
    intro x hx hxeq
    have hneg : C * (Y + ε) ^ 2 - κ'' * (Y + ε) ^ 3 < 0 :=
      majorant_vector_field_neg_of_gt hC hκ hbarrier
    have := hy_dot x hx.1
    rw [hxeq] at this
    linarith
  have hle :=
    image_le_of_deriv_right_lt_deriv_boundary (f := y) (f' := deriv y)
      (a := 0) (b := t) (B := fun _ => Y + ε) (B' := fun _ => (0 : ℝ))
      hyC hyW hy0 hB hcontact
  exact hle ⟨ht, le_rfl⟩

/-- Solutions of the Riccati *equation* starting at `y 0 ≥ 0` stay nonnegative:
below `0` the vector field `y² (C − κ'' y)` is strictly positive. -/
public theorem comparison_ode_nonneg
    (C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'')
    (y : ℝ → ℝ)
    (hdiff : ∀ s ≥ (0 : ℝ), DifferentiableAt ℝ y s)
    (hy_dot : ∀ s ≥ (0 : ℝ), deriv y s = C * (y s) ^ 2 - κ'' * (y s) ^ 3)
    (hy0 : 0 ≤ y 0)
    (t : ℝ) (ht : 0 ≤ t) :
    0 ≤ y t := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  -- Equivalent: `-y t ≤ ε`. Barrier for `-y` at height `ε`.
  have hy0' : -y 0 ≤ ε := (neg_nonpos.mpr hy0).trans hε.le
  have hnegdiff : ∀ s ≥ (0 : ℝ), DifferentiableAt ℝ (fun s => -y s) s :=
    fun s hs => (hdiff s hs).neg
  have hyC : ContinuousOn (fun s => -y s) (Icc (0 : ℝ) t) := fun x hx =>
    (hnegdiff x hx.1).continuousAt.continuousWithinAt
  have hyW : ∀ x ∈ Ico (0 : ℝ) t,
      HasDerivWithinAt (fun s => -y s) (deriv (fun s => -y s) x) (Ici x) x :=
    fun x hx => (hnegdiff x hx.1).hasDerivAt.hasDerivWithinAt
  have hB : ∀ x, HasDerivAt (fun _ : ℝ => ε) (0 : ℝ) x := fun x =>
    hasDerivAt_const x ε
  have hcontact : ∀ x ∈ Ico (0 : ℝ) t, -y x = ε → deriv (fun s => -y s) x < 0 := by
    intro x hx hxeq
    have hyx : y x = -ε := by
      linarith
    have hpos : 0 < C * (y x) ^ 2 - κ'' * (y x) ^ 3 := by
      have hy2 : 0 < (y x) ^ 2 := by
        rw [hyx, neg_sq]
        exact sq_pos_of_pos hε
      have hlin : 0 < C - κ'' * y x := by
        rw [hyx]
        linarith [mul_pos hκ hε]
      rw [majorant_vector_field_eq]
      exact mul_pos hy2 hlin
    have hder : deriv y x = C * (y x) ^ 2 - κ'' * (y x) ^ 3 := hy_dot x hx.1
    have hneg : deriv (fun s => -y s) x = -deriv y x :=
      (hdiff x hx.1).hasDerivAt.neg.deriv
    linarith
  have hle :=
    image_le_of_deriv_right_lt_deriv_boundary (f := fun s => -y s)
      (f' := fun x => deriv (fun s => -y s) x)
      (a := 0) (b := t) (B := fun _ => ε) (B' := fun _ => (0 : ℝ))
      hyC hyW hy0' hB hcontact
  have : -y t ≤ ε := hle ⟨ht, le_rfl⟩
  linarith

/-- On a compact time interval, a continuous nonnegative majorant bounded by `Y`
is integrable, and its integral is at most `T * Y`. This is the finite-time
input to BKM. -/
public theorem bkm_time_integral_le
    (Y : ℝ) (M : ℝ → ℝ) (T : ℝ)
    (_hM : ∀ τ, M τ ≤ Y)
    (hcont : ContinuousOn M (Icc (0 : ℝ) T)) :
    IntegrableOn M (Icc (0 : ℝ) T) :=
  hcont.integrableOn_Icc

/-- If `M` is continuous, then `M` is integrable on every compact interval `[0, T]`
(empty if `T < 0`). Combined with `beale_kato_majda` this is the smoothness pipeline. -/
public theorem bkm_integrableOn_of_uniform_bound
    (Y : ℝ) (M : ℝ → ℝ)
    (_hM : ∀ τ ≥ (0 : ℝ), M τ ≤ Y)
    (hcont : Continuous M)
    (T : ℝ) :
    IntegrableOn M (Icc (0 : ℝ) T) := by
  by_cases hT0 : 0 ≤ T
  · exact hcont.continuousOn.integrableOn_Icc
  · have : Icc (0 : ℝ) T = (∅ : Set ℝ) := by
      ext x
      constructor
      · intro hx
        exact (hT0 (le_trans hx.1 hx.2)).elim
      · intro hx
        exact hx.elim
    rw [this]
    exact integrableOn_empty

/-- Uniform vorticity bound + continuity of `t ↦ ‖ω(t)‖_∞` ⇒ global smoothness,
via BKM (classical). -/
public theorem bkm_regularity_pipeline
    (u : TimeDependentVelocity) (p : TimeDependentPressure) (ν : ℝ)
    (hν : 0 < ν) (hNS : NS_PDE u p ν)
    (Y : ℝ)
    (hbound : ∀ τ ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u τ)) ≤ Y)
    (hcont : Continuous fun τ : ℝ => vorticity_sup_norm (vorticity (u τ)))
    (hTstar : Tstar (u 0) ν = ⊤)
    (hbelow : ∀ T : ℝ, (T : EReal) < Tstar (u 0) ν →
      ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (u t)) :
    ∀ τ ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u τ) :=
  beale_kato_majda u p ν hν hNS (fun T _hTlt =>
    bkm_integrableOn_of_uniform_bound Y
      (fun τ => vorticity_sup_norm (vorticity (u τ))) hbound hcont T)
    hTstar hbelow

/-- The Riccati differential inequality for `M(t) = ‖ω(t)‖_∞` produces the
uniform ceiling `max(M 0, C/κ'')` together with the standing continuity of
`M`. This is the assembly `hRiccati` conjunct, discharged from the comparison
ODE already kernel-checked in this module. -/
public theorem vorticity_sup_norm_riccati_bound
    (u : TimeDependentVelocity)
    (C κ'' : ℝ) (hC : 0 < C) (hκ : 0 < κ'')
    (hdiff : ∀ s ≥ (0 : ℝ),
      DifferentiableAt ℝ (fun τ => vorticity_sup_norm (vorticity (u τ))) s)
    (hDI : ∀ s ≥ (0 : ℝ),
      deriv (fun τ => vorticity_sup_norm (vorticity (u τ))) s ≤
        C * vorticity_sup_norm (vorticity (u s)) ^ 2 -
          κ'' * vorticity_sup_norm (vorticity (u s)) ^ 3)
    (hcont : Continuous fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) :
    ∃ Y : ℝ,
      (∀ τ ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u τ)) ≤ Y) ∧
      Continuous (fun τ : ℝ => vorticity_sup_norm (vorticity (u τ))) :=
  ⟨max (vorticity_sup_norm (vorticity (u 0))) (C / κ''),
    ⟨fun τ hτ =>
      comparison_ode_stability C κ'' hC hκ
        (fun s => vorticity_sup_norm (vorticity (u s))) hdiff hDI τ hτ,
      hcont⟩⟩

/-! ## ε-Young and Hölder absorption (real scalars, Mathlib) -/

/-- Conjugate pair used on `I₆^{2/3}` and the stretching product. -/
public theorem holderConjugate_three_halves_three :
    ((3 : ℝ) / 2).HolderConjugate 3 :=
  (Real.holderConjugate_iff).2 ⟨by norm_num, by norm_num⟩

/-- Paper §3 Hölder on the quartic: `∫ |ω|⁴ |φ| ≤ ‖φ‖_∞ (∫|ω|⁶)^{2/3} (∫1)^{1/3}`.
The factor `(∫1)^{1/3}` is finite Haar volume of `𝕋³`; it is a hypothesis
because Lebesgue on the model `ℝ³` is infinite. -/
public theorem holder_I4
    (ω : VorticityField) (phi : T3 → ℝ) (phiLinf : ℝ)
    (hphi : ∀ x, |phi x| ≤ phiLinf)
    (hφnn : 0 ≤ phiLinf)
    (hω : MemLp (fun x : T3 => ‖ω x‖ ^ 4) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (h1 : MemLp (fun _ : T3 => (1 : ℝ)) (ENNReal.ofReal 3) volume) :
    ∫ x, ‖ω x‖ ^ 4 * |phi x| ∂volume ≤
      phiLinf * (∫ x, ‖ω x‖ ^ 6 ∂volume) ^ ((2 : ℝ) / 3) *
        (∫ x, (1 : ℝ) ∂volume) ^ ((1 : ℝ) / 3) := by
  have hpq := holderConjugate_three_halves_three
  have hf_nn : 0 ≤ᵐ[volume] fun x : T3 => ‖ω x‖ ^ 4 :=
    Filter.Eventually.of_forall fun _ => pow_nonneg (norm_nonneg _) _
  have hg_nn : 0 ≤ᵐ[volume] fun _ : T3 => (1 : ℝ) :=
    Filter.Eventually.of_forall fun _ => zero_le_one
  have hH :=
    integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hpq hf_nn hg_nn hω h1
  have hpow : ∀ x, (‖ω x‖ ^ 4) ^ ((3 : ℝ) / 2) = ‖ω x‖ ^ 6 := by
    intro x
    have ha : 0 ≤ ‖ω x‖ := norm_nonneg _
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have hinter :
      ∫ x, ‖ω x‖ ^ 4 * (1 : ℝ) ∂volume ≤
        (∫ x, ‖ω x‖ ^ 6 ∂volume) ^ ((2 : ℝ) / 3) *
          (∫ x, (1 : ℝ) ∂volume) ^ ((1 : ℝ) / 3) := by
    have hfun :
        (fun a : T3 => (‖ω a‖ ^ 4) ^ ((3 : ℝ) / 2)) = fun a => ‖ω a‖ ^ 6 :=
      funext hpow
    have h1p : (fun _ : T3 => (1 : ℝ) ^ (3 : ℝ)) = fun _ => (1 : ℝ) := by
      funext _
      simp
    have hp : (1 : ℝ) / ((3 : ℝ) / 2) = (2 : ℝ) / 3 := by field_simp
    calc
      ∫ x, ‖ω x‖ ^ 4 * (1 : ℝ) ∂volume
          ≤ (∫ a, (‖ω a‖ ^ 4) ^ ((3 : ℝ) / 2) ∂volume) ^ (1 / ((3 : ℝ) / 2)) *
              (∫ a, (1 : ℝ) ^ (3 : ℝ) ∂volume) ^ ((1 : ℝ) / 3) := hH
      _ = (∫ a, ‖ω a‖ ^ 6 ∂volume) ^ ((2 : ℝ) / 3) *
            (∫ a, (1 : ℝ) ∂volume) ^ ((1 : ℝ) / 3) := by
          rw [hfun, h1p, hp]
  have hμ : volume (univ : Set T3) < ⊤ := by
    have hlt : eLpNorm (fun _ : T3 => (1 : ℝ)) (ENNReal.ofReal 3) volume < ⊤ :=
      h1.eLpNorm_lt_top
    rw [eLpNorm_const_lt_top_iff (μ := volume) (p := ENNReal.ofReal 3) (c := (1 : ℝ))
      (by simp) (by simp)] at hlt
    exact hlt.resolve_left (by simp)
  haveI : IsFiniteMeasure (volume : Measure T3) := ⟨hμ⟩
  have hL1 : MemLp (fun x : T3 => ‖ω x‖ ^ 4) 1 volume :=
    hω.mono_exponent (by
      have : ENNReal.ofReal (1 : ℝ) ≤ ENNReal.ofReal ((3 : ℝ) / 2) :=
        ENNReal.ofReal_le_ofReal (by norm_num)
      simpa using this)
  have hint : Integrable (fun x : T3 => ‖ω x‖ ^ 4) volume :=
    (memLp_one_iff_integrable (μ := volume)).1 hL1
  have hintc : Integrable (fun x : T3 => phiLinf * ‖ω x‖ ^ 4) volume :=
    hint.const_mul phiLinf
  have hpt : ∀ x, ‖ω x‖ ^ 4 * |phi x| ≤ phiLinf * ‖ω x‖ ^ 4 := by
    intro x
    have : 0 ≤ ‖ω x‖ ^ 4 := pow_nonneg (norm_nonneg _) _
    nlinarith [hphi x]
  have hI4 :
      ∫ x, ‖ω x‖ ^ 4 * |phi x| ∂volume ≤
        ∫ x, phiLinf * ‖ω x‖ ^ 4 ∂volume :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun x =>
        mul_nonneg (pow_nonneg (norm_nonneg _) _) (abs_nonneg _))
      hintc
      (Filter.Eventually.of_forall hpt)
  have hsc :
      ∫ x, phiLinf * ‖ω x‖ ^ 4 ∂volume = phiLinf * ∫ x, ‖ω x‖ ^ 4 ∂volume :=
    integral_const_mul _ _
  have hmul1 : (fun x : T3 => ‖ω x‖ ^ 4 * (1 : ℝ)) = fun x => ‖ω x‖ ^ 4 := by
    funext x; ring
  rw [hsc] at hI4
  rw [hmul1] at hinter
  nlinarith [hφnn, hinter, hI4]

/-- ε-Young: `ab ≤ ε a^p/p + ε^{-q/p} b^q/q`. -/
public theorem young_inequality_eps
    {a b ε p q : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hε : 0 < ε)
    (hpq : p.HolderConjugate q) :
    a * b ≤ ε * a ^ p / p + ε ^ (-(q / p)) * b ^ q / q := by
  have hp : 0 < p := hpq.pos
  have hp0 : p ≠ 0 := ne_of_gt hp
  have hεp : 0 ≤ ε ^ (p⁻¹) := Real.rpow_nonneg hε.le _
  have hεq : 0 ≤ ε ^ (-(p⁻¹)) := Real.rpow_nonneg hε.le _
  have hy := Real.young_inequality_of_nonneg
    (mul_nonneg hεp ha) (mul_nonneg hεq hb) hpq
  have hscale : ε ^ (p⁻¹) * ε ^ (-(p⁻¹)) = (1 : ℝ) := by
    rw [← Real.rpow_add hε, add_neg_cancel, Real.rpow_zero]
  have hab :
      a * b = (ε ^ (p⁻¹) * a) * (ε ^ (-(p⁻¹)) * b) := by
    calc
      a * b = (1 * a) * b := by ring
      _ = ((ε ^ (p⁻¹) * ε ^ (-(p⁻¹))) * a) * b := by rw [hscale]
      _ = (ε ^ (p⁻¹) * a) * (ε ^ (-(p⁻¹)) * b) := by ring
  have h1 : (ε ^ (p⁻¹) * a) ^ p = ε * a ^ p := by
    rw [Real.mul_rpow hεp ha, ← Real.rpow_mul hε.le, inv_mul_cancel₀ hp0, Real.rpow_one]
  have h2 : (ε ^ (-(p⁻¹)) * b) ^ q = ε ^ (-(q / p)) * b ^ q := by
    rw [Real.mul_rpow hεq hb, ← Real.rpow_mul hε.le]
    congr 1
    field_simp
  calc
    a * b = (ε ^ (p⁻¹) * a) * (ε ^ (-(p⁻¹)) * b) := hab
    _ ≤ (ε ^ (p⁻¹) * a) ^ p / p + (ε ^ (-(p⁻¹)) * b) ^ q / q := hy
    _ = ε * a ^ p / p + ε ^ (-(q / p)) * b ^ q / q := by rw [h1, h2]

/-- Explicit absorption coefficient after ε-Young with `ε = 3κ/8`
(so the `I₆` coefficient is exactly `κ/4`). -/
public noncomputable def absorptionCoeff (kappa : ℝ) (C_Sob phi : ℝ) : ℝ :=
  let ε : ℝ := 3 * kappa / 8
  ε ^ (-(2 : ℝ)) / 3 * (4 * kappa * C_Sob) ^ 3 * (phi ^ ((3 : ℝ) / 2) + 1)

/-- From Hölder `I₄ ≤ C_Sob φ I₆^{2/3}`, ε-Young with `ε = 3κ/8` yields
the exact stretching absorption used by `youngs_absorption_elimination`. -/
public theorem stretching_bound_of_holder (hκ : 0 < kappa)
    (M I4 I6 phi C_Sob : ℝ)
    (hM : 0 ≤ M) (_hI4 : 0 ≤ I4) (hI6 : 0 ≤ I6) (hphi : 0 ≤ phi)
    (hS : 0 ≤ C_Sob)
    (hH : I4 ≤ C_Sob * phi * I6 ^ ((2 : ℝ) / 3)) :
    4 * kappa * M * I4 ≤
      (kappa / 4) * I6 +
        absorptionCoeff kappa C_Sob phi * (M ^ 3 * phi ^ ((3 : ℝ) / 2)) := by
  have hκ := hκ
  set a := I6 ^ ((2 : ℝ) / 3)
  set b := 4 * kappa * C_Sob * M * phi
  set ε : ℝ := 3 * kappa / 8
  have ha : 0 ≤ a := Real.rpow_nonneg hI6 _
  have hb : 0 ≤ b :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4)
      hκ.le) hS) hM) hphi
  have hε : 0 < ε :=
    div_pos (mul_pos three_pos hκ) (by norm_num : (0 : ℝ) < 8)
  have hpq := holderConjugate_three_halves_three
  have hprod : 4 * kappa * M * I4 ≤ a * b := by
    have := mul_le_mul_of_nonneg_left hH
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hκ.le) hM)
    simpa [a, b, mul_assoc, mul_left_comm, mul_comm] using this
  have hyoung := young_inequality_eps (p := (3 : ℝ) / 2) (q := 3) ha hb hε hpq
  have ha_pow : a ^ ((3 : ℝ) / 2) = I6 := by
    dsimp [a]
    rw [← Real.rpow_mul hI6]
    norm_num
  have hcoeff : ε * a ^ ((3 : ℝ) / 2) / ((3 : ℝ) / 2) = (kappa / 4) * I6 := by
    rw [ha_pow]
    change (3 * kappa / 8) * I6 / ((3 : ℝ) / 2) = kappa / 4 * I6
    field_simp
    ring
  have hqp : (3 : ℝ) / ((3 : ℝ) / 2) = (2 : ℝ) := by field_simp
  have hφ : 0 ≤ phi ^ ((3 : ℝ) / 2) := Real.rpow_nonneg hphi _
  have hφ3 :
      phi ^ (3 : ℝ) ≤ (phi ^ ((3 : ℝ) / 2) + 1) * phi ^ ((3 : ℝ) / 2) := by
    have : phi ^ (3 : ℝ) = phi ^ ((3 : ℝ) / 2) * phi ^ ((3 : ℝ) / 2) := by
      rw [← Real.rpow_add_of_nonneg hphi (by norm_num) (by norm_num)]; norm_num
    nlinarith [hφ]
  have hrem :
      ε ^ (-((3 : ℝ) / ((3 : ℝ) / 2))) * b ^ (3 : ℝ) / 3 ≤
        absorptionCoeff kappa C_Sob phi * (M ^ 3 * phi ^ ((3 : ℝ) / 2)) := by
    have hb_nonneg : 0 ≤ 4 * kappa * C_Sob :=
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hκ.le) hS
    have hb_rpow :
        b ^ (3 : ℝ) = (4 * kappa * C_Sob) ^ (3 : ℝ) *
          M ^ (3 : ℝ) * phi ^ (3 : ℝ) := by
      dsimp [b]
      rw [mul_assoc (4 * kappa * C_Sob) M phi,
        Real.mul_rpow hb_nonneg (mul_nonneg hM hphi),
        Real.mul_rpow hM hphi]
      ring
    have hε2 : ε ^ (-((3 : ℝ) / ((3 : ℝ) / 2))) = ε ^ (-(2 : ℝ)) := by
      rw [hqp]
    have hAbs :
        absorptionCoeff kappa C_Sob phi =
          ε ^ (-(2 : ℝ)) / 3 * (4 * kappa * C_Sob) ^ 3 *
            (phi ^ ((3 : ℝ) / 2) + 1) := rfl
    have hpow3 : (4 * kappa * C_Sob) ^ (3 : ℝ) = (4 * kappa * C_Sob) ^ 3 :=
      Real.rpow_natCast _ 3
    have hM3 : M ^ (3 : ℝ) = M ^ 3 := Real.rpow_natCast _ 3
    have hnn : 0 ≤ ε ^ (-(2 : ℝ)) / 3 :=
      div_nonneg (Real.rpow_nonneg hε.le _) (by norm_num)
    have hnnK : 0 ≤ (4 * kappa * C_Sob) ^ 3 := pow_nonneg hb_nonneg _
    have hnnM : 0 ≤ M ^ 3 := pow_nonneg hM _
    rw [hε2, hb_rpow, hAbs, hpow3, hM3]
    have := mul_le_mul_of_nonneg_left hφ3
      (mul_nonneg (mul_nonneg hnn hnnK) hnnM)
    convert this using 1 <;> ring
  calc
    4 * kappa * M * I4 ≤ a * b := hprod
    _ ≤ ε * a ^ ((3 : ℝ) / 2) / ((3 : ℝ) / 2) +
          ε ^ (-((3 : ℝ) / ((3 : ℝ) / 2))) * b ^ (3 : ℝ) / 3 := hyoung
    _ = (kappa / 4) * I6 +
          ε ^ (-((3 : ℝ) / ((3 : ℝ) / 2))) * b ^ (3 : ℝ) / 3 := by rw [hcoeff]
    _ ≤ (kappa / 4) * I6 +
          absorptionCoeff kappa C_Sob phi * (M ^ 3 * phi ^ ((3 : ℝ) / 2)) := by
        linarith [hrem]

/-- Hölder I4 with the paper's Sobolev gate: `∫|ω|⁴|φ| ≤ C_Sob ‖φ‖_∞ (∫|ω|⁶)^{2/3}`
for any constant `C_Sob` with `(∫1)^{1/3} ≤ C_Sob` (Haar volume of the model torus). -/
public theorem holder_I4_le_sobolev
    (ω : VorticityField) (phi : T3 → ℝ) (phiLinf : ℝ)
    (hphi : ∀ x, |phi x| ≤ phiLinf)
    (hφnn : 0 ≤ phiLinf) (C_Sob : ℝ)
    (hω : MemLp (fun x : T3 => ‖ω x‖ ^ 4) (ENNReal.ofReal ((3 : ℝ) / 2)) volume)
    (h1 : MemLp (fun _ : T3 => (1 : ℝ)) (ENNReal.ofReal 3) volume)
    (hvol : (∫ _x, (1 : ℝ) ∂volume) ^ ((1 : ℝ) / 3) ≤ C_Sob) :
    ∫ x, ‖ω x‖ ^ 4 * |phi x| ∂volume ≤
      C_Sob * phiLinf * (∫ x, ‖ω x‖ ^ 6 ∂volume) ^ ((2 : ℝ) / 3) := by
  have hH := holder_I4 ω phi phiLinf hphi hφnn hω h1
  have hI6 : 0 ≤ (∫ x, ‖ω x‖ ^ 6 ∂volume) ^ ((2 : ℝ) / 3) :=
    Real.rpow_nonneg (integral_nonneg fun _ => pow_nonneg (norm_nonneg _) _) _
  have hprod : 0 ≤ phiLinf * (∫ x, ‖ω x‖ ^ 6 ∂volume) ^ ((2 : ℝ) / 3) :=
    mul_nonneg hφnn hI6
  calc
    ∫ x, ‖ω x‖ ^ 4 * |phi x| ∂volume
        ≤ phiLinf * (∫ x, ‖ω x‖ ^ 6 ∂volume) ^ ((2 : ℝ) / 3) *
            (∫ x, (1 : ℝ) ∂volume) ^ ((1 : ℝ) / 3) := hH
    _ ≤ phiLinf * (∫ x, ‖ω x‖ ^ 6 ∂volume) ^ ((2 : ℝ) / 3) *
            C_Sob :=
          mul_le_mul_of_nonneg_left hvol hprod
    _ = C_Sob * phiLinf *
            (∫ x, ‖ω x‖ ^ 6 ∂volume) ^ ((2 : ℝ) / 3) := by
          ring

#print axioms holderConjugate_three_halves_three
#print axioms holder_I4
#print axioms holder_I4_le_sobolev
#print axioms stretching_bound_of_holder
#print axioms vorticity_sup_norm_riccati_bound

end AnalyticPipeline
