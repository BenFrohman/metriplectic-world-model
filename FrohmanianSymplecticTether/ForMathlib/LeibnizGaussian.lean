/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Leibniz rules along curves and the 1D heat kernel

Product rules for `⟪f, g⟫`, `‖f‖²` and the quartic weight `‖f‖⁴` along a curve in `ℝ³`, and
the normalization and positivity of the 1D heat kernel `(4πt)^{-1/2} e^{-x²/(4t)}`.
-/

open Real
open scoped RealInnerProductSpace

namespace ForMathlib

local notation "R3" => EuclideanSpace ℝ (Fin 3)

public theorem hasDerivAt_inner_curve {f g : ℝ → R3} {f' g' : R3} {t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => ⟪f s, g s⟫) (⟪f', g t⟫ + ⟪f t, g'⟫) t := by
  simpa [add_comm] using hf.inner ℝ hg

public theorem hasDerivAt_norm_sq_curve {f : ℝ → R3} {f' : R3} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => ‖f s‖ ^ 2) (2 * ⟪f t, f'⟫) t :=
  hf.norm_sq

/-- Quartic weight: `d/dt ‖f‖⁴ = 4 ‖f‖² ⟪f, f'⟫`. -/
public theorem hasDerivAt_norm_pow_four_curve {f : ℝ → R3} {f' : R3} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => ‖f s‖ ^ 4) (4 * ‖f t‖ ^ 2 * ⟪f t, f'⟫) t := by
  have h := (hf.norm_sq).pow 2
  have e : (fun s => ‖f s‖ ^ 4) = fun s => (‖f s‖ ^ 2) ^ 2 := by
    funext s; ring
  rw [e]
  convert h using 1
  push_cast; ring

/-- 1D heat kernel. -/
@[expose] public noncomputable def heatKernel1D (t x : ℝ) : ℝ :=
  (4 * π * t) ^ (-(1 / 2 : ℝ)) * exp (-x ^ 2 / (4 * t))

public theorem heatKernel1D_pos {t : ℝ} (ht : 0 < t) (x : ℝ) : 0 < heatKernel1D t x :=
  mul_pos (rpow_pos_of_pos (by positivity) _) (exp_pos _)

/-- The 1D heat kernel has total mass one. -/
public theorem integral_heatKernel1D {t : ℝ} (ht : 0 < t) : ∫ x, heatKernel1D t x = 1 := by
  unfold heatKernel1D
  rw [MeasureTheory.integral_const_mul]
  have hg : (fun x : ℝ => exp (-x ^ 2 / (4 * t))) = fun x => exp (-(1 / (4 * t)) * x ^ 2) := by
    funext x; congr 1; field_simp
  rw [hg, integral_gaussian]
  have hpos : 0 < 4 * π * t := by positivity
  rw [show π / (1 / (4 * t)) = 4 * π * t by field_simp]
  rw [sqrt_eq_rpow, ← rpow_add hpos]
  norm_num
