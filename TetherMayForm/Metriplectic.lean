/-
Copyright (c) 2026 Benjamin Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Frohman (prepared with assistance from Grok; not a co-author).

# The metriplectic split: Lie–Poisson (antisymmetric) ⊕ metric (symmetric)

Benjamin Frohman's observation (Oct 29 2026): the antisymmetric (Lie–Poisson, 2-form)
part and the symmetric (metric, `𝔗_F`) part of a bilinear bracket are orthogonal and
"invisible" to each other. This file proves the algebraic content of that statement.
-/
import TetherMayForm.Basic

namespace Frohman.Tether

open scoped InnerProductSpace RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Symmetric (metric) part `B_sym(F,G) = ½(B(F,G) + B(G,F))`. -/
noncomputable def symPart (B : LinearMap.BilinForm ℝ H) : LinearMap.BilinForm ℝ H :=
  (1 / 2 : ℝ) • (B + B.flip)

/-- Antisymmetric (Lie–Poisson / 2-form) part `B_anti(F,G) = ½(B(F,G) − B(G,F))`. -/
noncomputable def antiPart (B : LinearMap.BilinForm ℝ H) : LinearMap.BilinForm ℝ H :=
  (1 / 2 : ℝ) • (B - B.flip)

theorem symPart_apply (B : LinearMap.BilinForm ℝ H) (F G : H) :
    symPart B F G = (B F G + B G F) / 2 := by
  simp [symPart]; ring

theorem antiPart_apply (B : LinearMap.BilinForm ℝ H) (F G : H) :
    antiPart B F G = (B F G - B G F) / 2 := by
  simp [antiPart]; ring

/-- `B = B_sym + B_anti`. -/
theorem symPart_add_antiPart (B : LinearMap.BilinForm ℝ H) : symPart B + antiPart B = B := by
  ext F G; simp only [LinearMap.add_apply, symPart_apply, antiPart_apply]; ring

theorem symPart_symm (B : LinearMap.BilinForm ℝ H) (F G : H) :
    symPart B F G = symPart B G F := by
  rw [symPart_apply, symPart_apply]; ring

theorem antiPart_antisymm (B : LinearMap.BilinForm ℝ H) (F G : H) :
    antiPart B F G = -antiPart B G F := by
  rw [antiPart_apply, antiPart_apply]; ring

/-- The antisymmetric part is **alternating**: it never contributes to diagonal
feedback `B(F,F)`. -/
theorem antiPart_self (B : LinearMap.BilinForm ℝ H) (F : H) : antiPart B F F = 0 := by
  rw [antiPart_apply]; ring

/-- Diagonal feedback is carried entirely by the symmetric part. -/
theorem symPart_self (B : LinearMap.BilinForm ℝ H) (F : H) : symPart B F F = B F F := by
  rw [symPart_apply]; ring

/-- A form that is both symmetric and antisymmetric is zero (the two subspaces meet
only in `0`). -/
theorem eq_zero_of_symm_of_antisymm (D : LinearMap.BilinForm ℝ H)
    (hs : ∀ F G, D F G = D G F) (ha : ∀ F G, D F G = -D G F) : D = 0 := by
  ext F G; have := hs F G; have := ha F G; simp; linarith

/-- **Uniqueness of the split.** If `B = S + A` with `S` symmetric and `A` antisymmetric,
then `S = B_sym` and `A = B_anti`. -/
theorem split_unique (B S A : LinearMap.BilinForm ℝ H) (hB : B = S + A)
    (hS : ∀ F G, S F G = S G F) (hA : ∀ F G, A F G = -A G F) :
    S = symPart B ∧ A = antiPart B := by
  subst hB
  constructor <;> ext F G <;>
    simp only [symPart_apply, antiPart_apply, LinearMap.add_apply, hS G F, hA G F] <;> ring

/-- **Orthogonality ("mutual invisibility").** For any finite family of vectors `b`
(e.g. an orthonormal basis), the Frobenius/trace pairing
`Σᵢⱼ B_sym(bᵢ,bⱼ) · B_anti(bᵢ,bⱼ)` vanishes. -/
theorem sym_anti_pairing_eq_zero {ι : Type*} [Fintype ι] (b : ι → H)
    (B : LinearMap.BilinForm ℝ H) :
    ∑ i, ∑ j, symPart B (b i) (b j) * antiPart B (b i) (b j) = 0 := by
  set s := ∑ i, ∑ j, symPart B (b i) (b j) * antiPart B (b i) (b j)
  have h : s = -s := by
    calc s = ∑ i, ∑ j, -(symPart B (b j) (b i) * antiPart B (b j) (b i)) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [symPart_symm B (b i), antiPart_antisymm B (b i)]; ring
      _ = -s := by
            rw [Finset.sum_comm]; simp [s, Finset.sum_neg_distrib]
  linarith

/-- Same orthogonality for *any* symmetric `S` and antisymmetric `A`. -/
theorem symm_antisymm_pairing_eq_zero {ι : Type*} [Fintype ι] (b : ι → H)
    (S A : LinearMap.BilinForm ℝ H) (hS : ∀ F G, S F G = S G F)
    (hA : ∀ F G, A F G = -A G F) :
    ∑ i, ∑ j, S (b i) (b j) * A (b i) (b j) = 0 := by
  set s := ∑ i, ∑ j, S (b i) (b j) * A (b i) (b j)
  have h : s = -s := by
    calc s = ∑ i, ∑ j, -(S (b j) (b i) * A (b j) (b i)) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            rw [hS (b i), hA (b i)]; ring
      _ = -s := by
            rw [Finset.sum_comm]; simp [s, Finset.sum_neg_distrib]
  linarith

/-- **C2 for the parts — honest statement.** C2 alone (`B F u = 0`) does *not* pass to
the parts; one also needs the left slot, `B u F = 0` (two-sided degeneracy). With both,
each part is degenerate. -/
theorem parts_degenerate (u : H) (B : LinearMap.BilinForm ℝ H)
    (hR : DegenerateWRTKineticEnergy u B) (hL : ∀ F, B u F = 0) :
    DegenerateWRTKineticEnergy u (symPart B) ∧ DegenerateWRTKineticEnergy u (antiPart B) := by
  refine ⟨fun F => ?_, fun F => ?_⟩
  · rw [symPart_apply, hR, hL]; ring
  · rw [antiPart_apply, hR, hL]; ring

/-- Conversely, if both parts satisfy C2 then `B` is two-sidedly degenerate. -/
theorem degenerate_of_parts (u : H) (B : LinearMap.BilinForm ℝ H)
    (hs : DegenerateWRTKineticEnergy u (symPart B))
    (ha : DegenerateWRTKineticEnergy u (antiPart B)) :
    DegenerateWRTKineticEnergy u B ∧ ∀ F, B u F = 0 := by
  constructor
  · intro F; have h1 := hs F; have h2 := ha F
    rw [symPart_apply] at h1; rw [antiPart_apply] at h2; linarith
  · intro F; have h1 := hs F; have h2 := ha F
    rw [symPart_apply] at h1; rw [antiPart_apply] at h2; linarith

/-- The metric part of `𝔗_F` is `𝔗_F`, and its Lie–Poisson part is zero. -/
theorem symPart_frohmanianTether (κ w : ℝ) (u : H) :
    symPart 𝔗_F[κ, w, u] = 𝔗_F[κ, w, u] := by
  ext F G; rw [symPart_apply, frohmanianTether_symm κ w u G F]; ring

theorem antiPart_frohmanianTether (κ w : ℝ) (u : H) : antiPart 𝔗_F[κ, w, u] = 0 := by
  ext F G; rw [antiPart_apply, frohmanianTether_symm κ w u G F]; simp

/-- **Metriplectic bracket** `{F,G}_𝔗F = {F,G}_Poisson + 𝔗_F(F,G)`, with the Poisson part
`P` an abstract alternating form (the Arnold Lie–Poisson bracket). -/
noncomputable def metriplecticBracket (P : LinearMap.BilinForm ℝ H) (κ w : ℝ) (u : H) :
    LinearMap.BilinForm ℝ H := P + 𝔗_F[κ, w, u]

/-- The split of the metriplectic bracket is exactly (Poisson, tether). -/
theorem metriplecticBracket_split (P : LinearMap.BilinForm ℝ H) (hP : ∀ F, P F F = 0)
    (κ w : ℝ) (u : H) :
    antiPart (metriplecticBracket P κ w u) = P ∧
      symPart (metriplecticBracket P κ w u) = 𝔗_F[κ, w, u] := by
  have hA : ∀ F G, P F G = -P G F := fun F G => by
    have := hP (F + G); simp [hP F, hP G] at this; linarith
  have := split_unique (metriplecticBracket P κ w u) 𝔗_F[κ, w, u] P
    (by rw [metriplecticBracket, add_comm]) (frohmanianTether_symm κ w u) hA
  exact ⟨this.2.symm, this.1.symm⟩

/-- **Energy.** The Poisson part conserves energy (`{H,H}_P = 0`, alternating), and the
tether is degenerate on it (`𝔗_F(F,H) = 0` for all `F`), so `dH/dt = {H,H}_𝔗F = 0`. -/
theorem metriplectic_energy_conserved (P : LinearMap.BilinForm ℝ H) (hP : ∀ F, P F F = 0)
    (κ w : ℝ) (u : H) :
    P (kineticEnergyGradient u) (kineticEnergyGradient u) = 0 ∧
      (∀ F, 𝔗_F[κ, w, u] F (kineticEnergyGradient u) = 0) ∧
      metriplecticBracket P κ w u (kineticEnergyGradient u) (kineticEnergyGradient u) = 0 := by
  refine ⟨hP _, degeneracy_verification κ w u, ?_⟩
  simp [metriplecticBracket, hP, degeneracy_verification]

end Frohman.Tether
