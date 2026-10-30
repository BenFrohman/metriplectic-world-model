/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
import Mathlib

/-!
# The abstract metriplectic generator

A metriplectic system: an antisymmetric (Lie–Poisson / Arnold) bracket `P`, a symmetric
positive-semidefinite metric (tether) bracket `G`, a Hamiltonian gradient `dH` and an entropy
gradient `dS`, with the two degeneracy conditions `P(·, dS) = 0` and `G(·, dH) = 0`.
The generator is `dF/dt = {F,H} + (F,S) = P(dF, dH) + G(dF, dS)`.

Proved here, with no hypotheses beyond the structure fields:
* `energy_conserved`: `dH/dt = 0`;
* `entropy_production`: `dS/dt = G(dS,dS) ≥ 0`;
* along any trajectory whose derivatives are given by the generator, `H` is constant
  (`energy_const_along`) and `S` is monotone (`entropy_monotone_along`);
* `gen_of_G_zero`: when the metric bracket vanishes, the generator is purely Hamiltonian.
-/

namespace MetriplecticWorldModel

/-- An abstract metriplectic structure at a state, on a space `V` of functional gradients. -/
structure MetriplecticSystem (V : Type*) where
  /-- Lie–Poisson (Arnold) bracket. -/
  P : V → V → ℝ
  /-- Metric (tether) bracket. -/
  G : V → V → ℝ
  P_antisymm : ∀ a b, P a b = -P b a
  G_symm : ∀ a b, G a b = G b a
  G_nonneg : ∀ a, 0 ≤ G a a
  dH : V
  dS : V
  /-- Degeneracy: the entropy is a Casimir of the Poisson bracket. -/
  degen_P : ∀ a, P a dS = 0
  /-- Degeneracy: the energy is in the kernel of the metric bracket. -/
  degen_G : ∀ a, G a dH = 0

variable {V : Type*} (m : MetriplecticSystem V)

/-- The generator `dF/dt = {F,H} + (F,S)`. -/
def MetriplecticSystem.gen (dF : V) : ℝ := m.P dF m.dH + m.G dF m.dS

theorem P_self (a : V) : m.P a a = 0 := by
  have := m.P_antisymm a a; linarith

/-- First law: energy is conserved by the generator. -/
theorem energy_conserved : m.gen m.dH = 0 := by
  unfold MetriplecticSystem.gen
  rw [P_self, m.G_symm, m.degen_G]; simp

theorem gen_entropy_eq : m.gen m.dS = m.G m.dS m.dS := by
  unfold MetriplecticSystem.gen
  rw [m.P_antisymm, m.degen_P]; simp

/-- Second law: entropy production is nonnegative. -/
theorem entropy_production : 0 ≤ m.gen m.dS := by
  rw [gen_entropy_eq]; exact m.G_nonneg _

/-- With a vanishing metric bracket the generator is the pure Lie–Poisson flow. -/
theorem gen_of_G_zero (h : ∀ a b, m.G a b = 0) (dF : V) : m.gen dF = m.P dF m.dH := by
  unfold MetriplecticSystem.gen; rw [h]; simp

/-- Along a trajectory, if `dE/dt` is given by the generator applied to `dH`, `E` is constant. -/
theorem energy_const_along (sys : ℝ → MetriplecticSystem V) (E : ℝ → ℝ)
    (hE : ∀ t, HasDerivAt E ((sys t).gen (sys t).dH) t) (t : ℝ) : E t = E 0 := by
  have h0 : ∀ t, HasDerivAt E 0 t := fun t => by
    have := hE t; rwa [energy_conserved] at this
  exact is_const_of_deriv_eq_zero (fun t => (h0 t).differentiableAt)
    (fun t => (h0 t).deriv) t 0

/-- Along a trajectory, if `dS/dt` is given by the generator applied to `dS`, `S` is monotone. -/
theorem entropy_monotone_along (sys : ℝ → MetriplecticSystem V) (S : ℝ → ℝ)
    (hS : ∀ t, HasDerivAt S ((sys t).gen (sys t).dS) t) : Monotone S :=
  monotone_of_hasDerivAt_nonneg hS (fun t => entropy_production (sys t))

end MetriplecticWorldModel
