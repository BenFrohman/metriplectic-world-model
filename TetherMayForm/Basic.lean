/-
Copyright (c) 2026 Benjamin Frohman. All rights reserved.
Released under Apache 2.0 license.
Author: Benjamin Frohman (prepared with assistance from Grok; not a co-author).

# The minimal metric frohmanianTether — the April–May 2026 form

This file formalizes, in an abstract real inner-product-space model, the
"Uniqueness of the Minimal Metric Tether" as Benjamin Frohman stated it in May 2026:
a degenerate, symmetric, bilinear minimal metric correction to the Arnold Lie–Poisson
bracket,

  `B(F,G) = -κ ∫ |ω|² ⟨Π_u δF, Π_u δG⟩`,

where `Π_u` is "the L²-orthogonal projection onto the complement of span{u}"
(vFinal, May 21 2026).

## Abstract model (what is and is not modelled)
* `H` — a real inner product space standing for the space of functional derivatives
  `δF/δω` (no completeness needed: `span{u}` is finite-dimensional).
* `u : H` — the velocity; `δH = u` for the kinetic energy `H = ½∫|u|²`, as in the May
  sources.  We do *not* model the curl / Biot–Savart relation between `u` and `ω`.
* The weight `∫|ω|²` is collapsed to one scalar `w ≥ 0` (a frozen-time, spatially
  averaged model). The pointwise integral version is not formalized here.
* `κ > 0` is a free parameter. `κ = 1` was the May teaching placeholder; `3/2`
  was introduced Aug 26 2026. Nothing below depends on its value.
* No saturation and no polarization hypotheses appear anywhere in this file.
-/

import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

namespace Frohman.Tether

open Submodule
open scoped InnerProductSpace RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## 1. The projection `Π_u` -/

/-- `Π_u`: the orthogonal projection onto `(span{u})ᗮ`, taken directly from Mathlib's
`Submodule.starProjection`. This is the May 21 definition verbatim. -/
noncomputable def piU (u : H) : H →L[ℝ] H := (ℝ ∙ u)ᗮ.starProjection

/-- Explicit formula: `Π_u x = x - (⟪u,x⟫/‖u‖²) u`. -/
theorem piU_apply (u x : H) : piU u x = x - (⟪u, x⟫ / ‖u‖ ^ 2) • u := by
  simp [piU, starProjection_orthogonal_val, starProjection_singleton]

/-- **`projectionOrthogonalToU`** (a `sorry` in the May 31 `Tether.lean`):
`Π_u u = 0`. (Holds even for `u = 0`.) -/
theorem projectionOrthogonalToU (u : H) : piU u u = 0 := by
  rw [piU, starProjection_orthogonal_val, sub_eq_zero, eq_comm,
    starProjection_eq_self_iff]
  exact mem_span_singleton_self u

/-- `Π_u` kills every multiple of `u`. -/
theorem piU_smul_self (u : H) (c : ℝ) : piU u (c • u) = 0 := by
  rw [map_smul, projectionOrthogonalToU, smul_zero]

/-- The kernel of `Π_u` is exactly `span{u}`: the projection kills nothing else. -/
theorem piU_apply_eq_zero_iff (u x : H) : piU u x = 0 ↔ x ∈ (ℝ ∙ u) := by
  rw [piU, starProjection_apply_eq_zero_iff, orthogonal_orthogonal]

/-- `Π_u` is self-adjoint. -/
theorem inner_piU_left (u x y : H) : ⟪piU u x, y⟫ = ⟪x, piU u y⟫ :=
  inner_starProjection_left_eq_right _ x y

/-! ## 2. The frohmanianTether form and the Degeneracy Verification Lemma -/

/-- The **minimal metric frohmanianTether** `B(F,G) = -κ w ⟪Π_u F, Π_u G⟫`, as a bilinear form
(bilinearity is therefore by construction). `w` stands for `∫|ω|²`. -/
noncomputable def frohmanianTether (κ w : ℝ) (u : H) : LinearMap.BilinForm ℝ H :=
  (-(κ * w)) • (innerₗ H).compl₁₂ (piU u : H →ₗ[ℝ] H) (piU u : H →ₗ[ℝ] H)

/-- `𝔗_F[κ, w, u]` — the Frohmanian Symplectic Tether `𝔗_F` (May 3 `main3`: `\mathfrak{T}_F`;
May 21 vFinal: `TF`). -/
scoped notation "𝔗_F[" κ ", " w ", " u "]" => frohmanianTether κ w u

/-- `δH = u`: the functional derivative of the kinetic energy `H = ½∫|u|²`. -/
def kineticEnergyGradient (u : H) : H := u

theorem frohmanianTether_apply (κ w : ℝ) (u F G : H) :
    frohmanianTether κ w u F G = -(κ * w) * ⟪piU u F, piU u G⟫ := by
  simp [frohmanianTether]

/-- The frohmanianTether is **symmetric** (a metric bracket, not a Poisson one). -/
theorem frohmanianTether_symm (κ w : ℝ) (u F G : H) : frohmanianTether κ w u F G = frohmanianTether κ w u G F := by
  simp only [frohmanianTether_apply, real_inner_comm]

/-- The frohmanianTether is **negative semidefinite** when `κ ≥ 0`, `w ≥ 0`. -/
theorem frohmanianTether_self_nonpos {κ w : ℝ} (hκ : 0 ≤ κ) (hw : 0 ≤ w) (u F : H) :
    frohmanianTether κ w u F F ≤ 0 := by
  rw [frohmanianTether_apply]
  have : 0 ≤ ⟪piU u F, piU u F⟫ := real_inner_self_nonneg
  nlinarith [mul_nonneg hκ hw]

/-- **C2 (degeneracy with respect to kinetic energy).** A bilinear correction `B` is
degenerate on `H = ½∫|u|²` when `B(F, H) = 0` for every `F`, where `δH = u`. -/
def DegenerateWRTKineticEnergy (u : H) (B : LinearMap.BilinForm ℝ H) : Prop :=
  ∀ F, B F u = 0

/-- Scalar form: `𝔗_F(F, c·u) = 0` for every `c`. -/
theorem degeneracy_verification_smul (κ w : ℝ) (u F : H) (c : ℝ) :
    𝔗_F[κ, w, u] F (c • u) = 0 := by
  rw [frohmanianTether_apply, piU_smul_self, inner_zero_right, mul_zero]

/-- **Degeneracy Verification Lemma** (requested by the May 21 referee report).
`B(F, c·u) = 0` for every `F` and every `c`; in particular `B(F, H) = 0`, so the frohmanianTether
leaves the Hamiltonian untouched and the reversible part stays exactly Euler.

Reasoning: `Π_u (c u) = c Π_u u = 0` by `projectionOrthogonalToU`, and the frohmanianTether only
sees `Π_u`-components. -/
theorem degeneracy_verification (κ w : ℝ) (u F : H) :
    𝔗_F[κ, w, u] F (kineticEnergyGradient u) = 0 := by
  simpa [kineticEnergyGradient] using degeneracy_verification_smul κ w u F 1

theorem frohmanianTether_degenerate (κ w : ℝ) (u : H) :
    DegenerateWRTKineticEnergy u (frohmanianTether κ w u) := fun F => by
  simpa using degeneracy_verification_smul κ w u F 1

/-- Consequently `dH/dt` receives no contribution from the frohmanianTether: `B(H,H) = 0`. -/
theorem frohmanianTether_energy_neutral (κ w : ℝ) (u : H) : frohmanianTether κ w u u u = 0 :=
  frohmanianTether_degenerate κ w u u

/-! ## 3. "Degeneracy forces the projection" (May 31 `step3`) -/

/-- **Step 3 of the May 31 plan, proved.** Any symmetric bilinear form that is
degenerate on `u` (C2) only sees `Π_u`-components:
`B(F,G) = B(Π_u F, Π_u G)`.

Reasoning: write `F = Π_u F + a u`, `G = Π_u G + b u`; every cross term contains a
`u` slot and vanishes by C2 (and symmetry for the left slot). -/
theorem degeneracy_forces_projection (u : H) (B : LinearMap.BilinForm ℝ H)
    (hsymm : ∀ F G, B F G = B G F) (hC2 : DegenerateWRTKineticEnergy u B) (F G : H) :
    B F G = B (piU u F) (piU u G) := by
  have hdec : ∀ x : H, x = piU u x + (⟪u, x⟫ / ‖u‖ ^ 2) • u := fun x => by
    rw [piU_apply]; abel
  have hu0 : B u = 0 := LinearMap.ext fun y => by rw [hsymm]; exact hC2 y
  conv_lhs => rw [hdec F, hdec G]
  simp [hu0, hC2 (piU u F)]

/-! ## 4. C1 (invariance) -/

/-- **C1, abstract form.** Invariance under the stabilizer of `u`: every linear isometry
`g` of `H` with `g u = u` preserves `B`. (In the PDE this is the coadjoint action of
volume-preserving diffeomorphisms fixing the base point; here it is modelled by the
isometries of the `L²` pairing that fix `u`.) -/
def InvariantUnderCoadjointAction (u : H) (B : LinearMap.BilinForm ℝ H) : Prop :=
  ∀ g : H ≃ₗᵢ[ℝ] H, g u = u → ∀ F G, B (g F) (g G) = B F G

theorem piU_comm_isometry (u : H) (g : H ≃ₗᵢ[ℝ] H) (hg : g u = u) (x : H) :
    piU u (g x) = g (piU u x) := by
  have : ⟪u, g x⟫ = ⟪u, x⟫ := by
    conv_lhs => rw [← hg]
    exact g.inner_map_map u x
  rw [piU_apply, piU_apply, map_sub, map_smul, hg, this]

/-- The frohmanianTether satisfies C1. -/
theorem frohmanianTether_invariant (κ w : ℝ) (u : H) :
    InvariantUnderCoadjointAction u (frohmanianTether κ w u) := by
  intro g hg F G
  rw [frohmanianTether_apply, frohmanianTether_apply, piU_comm_isometry u g hg, piU_comm_isometry u g hg,
    g.inner_map_map]

/-! ## 5. C3 and admissibility (C3 left to the author) -/

/-- An **admissible correction** relative to a feedback predicate `C3`. `C3` is an
explicit parameter — the "controllable negative feedback" condition whose exact
wording Benjamin Frohman will supply. It is deliberately *not* `True`. -/
structure IsAdmissibleCorrection (u : H) (C3 : LinearMap.BilinForm ℝ H → Prop)
    (B : LinearMap.BilinForm ℝ H) : Prop where
  symm : ∀ F G, B F G = B G F
  c1 : InvariantUnderCoadjointAction u B
  c2 : DegenerateWRTKineticEnergy u B
  c3 : C3 B

/-- The frohmanianTether is admissible for any `C3` it satisfies (C1, C2, symmetry are proved). -/
theorem frohmanianTether_admissible (κ w : ℝ) (u : H) (C3 : LinearMap.BilinForm ℝ H → Prop)
    (h3 : C3 (frohmanianTether κ w u)) : IsAdmissibleCorrection u C3 (frohmanianTether κ w u) :=
  ⟨frohmanianTether_symm κ w u, frohmanianTether_invariant κ w u, frohmanianTether_degenerate κ w u, h3⟩

/-! ## 6. Uniqueness up to gauge -/

/-- The **gauge class** in this symmetric model: symmetric bilinear forms that are
themselves degenerate on `u`. (The May living document says "closed 2-form on the
reduced orbit"; a 2-form is antisymmetric, whereas the frohmanianTether is symmetric, so the
literal May wording does not transfer. This is the symmetric analogue: forms that
descend to the reduced space `uᗮ`.) -/
def IsGauge (u : H) (D : LinearMap.BilinForm ℝ H) : Prop :=
  (∀ F G, D F G = D G F) ∧ DegenerateWRTKineticEnergy u D

/-- **Weak gauge uniqueness (proved).** Any symmetric correction satisfying C2 differs
from the frohmanianTether by a gauge term, and that difference only sees `Π_u`-components.
Honest note: given the definition of `IsGauge`, the first half is close to definitional;
the content is `degeneracy_forces_projection`. C1 and C3 are not used. -/
theorem gauge_uniqueness_weak (κ w : ℝ) (u : H) (B : LinearMap.BilinForm ℝ H)
    (hsymm : ∀ F G, B F G = B G F) (hC2 : DegenerateWRTKineticEnergy u B) :
    IsGauge u (B - frohmanianTether κ w u) ∧
      ∀ F G, (B - frohmanianTether κ w u) F G = (B - frohmanianTether κ w u) (piU u F) (piU u G) := by
  have hs : ∀ F G, (B - frohmanianTether κ w u) F G = (B - frohmanianTether κ w u) G F := fun F G => by
    simp [hsymm F G, frohmanianTether_symm κ w u F G]
  have h2 : DegenerateWRTKineticEnergy u (B - frohmanianTether κ w u) := fun F => by
    simp [hC2 F, frohmanianTether_degenerate κ w u F]
  exact ⟨⟨hs, h2⟩, degeneracy_forces_projection u _ hs h2⟩

/-! ## 6b. The Schur step -/


/-- Two unit vectors orthogonal to `u` take the same `B`-value: the reflection in the
hyperplane orthogonal to `e - e'` swaps them and fixes `u` (so C1 applies). -/
theorem diag_eq_of_norm_eq (u : H) (B : LinearMap.BilinForm ℝ H)
    (hC1 : InvariantUnderCoadjointAction u B) {e e' : H}
    (he : ⟪u, e⟫ = 0) (he' : ⟪u, e'⟫ = 0) (hn : ‖e‖ = ‖e'‖) : B e e = B e' e' := by
  have hfix : (ℝ ∙ (e - e'))ᗮ.reflection u = u := by
    apply reflection_mem_subspace_eq_self
    rw [mem_orthogonal_singleton_iff_inner_right, inner_sub_left, real_inner_comm,
      he, real_inner_comm, he', sub_zero]
  have := hC1 _ hfix e e
  rw [reflection_sub hn] at this
  exact this.symm

theorem exists_unit_orthogonal [FiniteDimensional ℝ H] (hdim : 2 ≤ Module.finrank ℝ H)
    (u : H) : ∃ e : H, ⟪u, e⟫ = 0 ∧ ‖e‖ = 1 := by
  have hne : (ℝ ∙ u)ᗮ ≠ ⊥ := by
    rw [Ne, orthogonal_eq_bot_iff]
    intro htop
    have h1 : Module.finrank ℝ (ℝ ∙ u) ≤ 1 := by
      simpa using finrank_span_le_card ({u} : Set H)
    rw [htop, finrank_top] at h1
    omega
  obtain ⟨v, hv, hv0⟩ := exists_mem_ne_zero_of_ne_bot hne
  rw [mem_orthogonal_singleton_iff_inner_right] at hv
  refine ⟨‖v‖⁻¹ • v, by rw [inner_smul_right, hv, mul_zero], ?_⟩
  rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv0)]

theorem inner_u_piU (u x : H) : ⟪u, piU u x⟫ = 0 := by
  rw [← inner_piU_left, projectionOrthogonalToU, inner_zero_left]

/-- **Schur-type step (proved).** In dimension ≥ 3, any symmetric correction obeying
C1 (invariance under isometries fixing `u`) and C2 (degeneracy on `δH = u`) is a
Frohmanian tether `𝔗_F[c, 1, u]` for some constant `c`.

Reasoning: by C2, `B` only sees `Π_u`-components. Any two unit vectors `e, e'` in `uᗮ`
are swapped by the reflection in `(e - e')ᗮ`, which fixes `u`, so C1 gives
`B(e,e) = B(e',e')`. Scaling gives `B(x,x) = B(e₀,e₀)‖Π_u x‖²`, and polarization
(using symmetry) gives `B(x,y) = B(e₀,e₀)⟪Π_u x, Π_u y⟫`. No saturation or polarization
*hypothesis* is assumed: polarization here is the algebraic identity.
(`hu` is kept for fidelity to the May statement but is not needed.) -/
theorem admissible_eq_smul_frohmanianTether [FiniteDimensional ℝ H]
    (hdim : 3 ≤ Module.finrank ℝ H) (u : H) (hu : u ≠ 0) (B : LinearMap.BilinForm ℝ H)
    (hsymm : ∀ F G, B F G = B G F) (hC1 : InvariantUnderCoadjointAction u B)
    (hC2 : DegenerateWRTKineticEnergy u B) :
    ∃ c : ℝ, B = 𝔗_F[c, 1, u] := by
  obtain ⟨e₀, he₀, hn₀⟩ := exists_unit_orthogonal (by omega) u
  have hq : ∀ x, B x x = B e₀ e₀ * ⟪piU u x, piU u x⟫ := by
    intro x
    rw [degeneracy_forces_projection u B hsymm hC2 x x]
    set p := piU u x with hp
    by_cases hp0 : p = 0
    · simp [hp0]
    have hnp : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hp0
    set e := ‖p‖⁻¹ • p
    have hpe : p = ‖p‖ • e := by simp [e, smul_smul, mul_inv_cancel₀ hnp]
    have he : ⟪u, e⟫ = 0 := by simp [e, inner_smul_right, hp, inner_u_piU]
    have hne : ‖e‖ = ‖e₀‖ := by
      rw [hn₀]; simp [e, norm_smul, inv_mul_cancel₀ hnp]
    have hB := diag_eq_of_norm_eq u B hC1 he he₀ hne
    rw [hpe]
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, real_inner_self_eq_norm_sq, hB]
    rw [← hpe]; ring
  refine ⟨-B e₀ e₀, LinearMap.ext₂ fun x y => ?_⟩
  rw [frohmanianTether_apply]
  have h1 := hq (x + y)
  have h2 := hq x
  have h3 := hq y
  simp only [map_add, LinearMap.add_apply, inner_add_left, inner_add_right] at h1
  rw [hsymm y x, real_inner_comm (piU u x) (piU u y)] at h1
  linear_combination (h1 - h2 - h3) / 2


/-- **Uniqueness of the Minimal Metric Tether (proved, relative to C3).** In dimension
≥ 3, every admissible correction (symmetric, C1, C2, C3) equals `𝔗_F[κ, w, u]`.

By `admissible_eq_smul_frohmanianTether`, `B = 𝔗_F[c, 1, u]` for some `c`; C3 then fixes
`c = κ w` through `hC3fix`. `hC3fix` is the one thing C3 must deliver: among the tether
family `𝔗_F[c, 1, u]`, the feedback condition selects exactly `c = κ w`. Once Benjamin's
C3 wording is written down, `hC3fix` becomes a lemma to prove about that wording. -/
theorem uniqueness_of_minimal_metric_tether [FiniteDimensional ℝ H]
    (hdim : 3 ≤ Module.finrank ℝ H) (κ w : ℝ) (u : H) (hu : u ≠ 0)
    (C3 : LinearMap.BilinForm ℝ H → Prop)
    (hC3fix : ∀ c : ℝ, C3 (𝔗_F[c, 1, u]) → c = κ * w)
    (B : LinearMap.BilinForm ℝ H) (hB : IsAdmissibleCorrection u C3 B) :
    B = 𝔗_F[κ, w, u] := by
  obtain ⟨c, rfl⟩ := admissible_eq_smul_frohmanianTether hdim u hu B hB.symm hB.c1 hB.c2
  have hc := hC3fix c hB.c3
  subst hc
  ext x y
  simp [frohmanianTether_apply]

/-! ## 7. The tethered bracket -/

/-- The **tethered bracket** (vFinal, May 21): `{F,G}_TF = {F,G}_classical + B(F,G)`,
evaluated on functional derivatives. The classical (Arnold Lie–Poisson) bracket is an
abstract parameter `classical`. -/
noncomputable def tetheredBracket (classical : LinearMap.BilinForm ℝ H) (κ w : ℝ) (u : H) :
    LinearMap.BilinForm ℝ H :=
  classical + 𝔗_F[κ, w, u]

/-- `⦃F, G⦄_𝔗F[classical; κ, w, u]` — the tethered bracket `{F,G}_TF`. -/
scoped notation "⦃" F ", " G "⦄_𝔗F[" P "; " κ ", " w ", " u "]" =>
  tetheredBracket P κ w u F G

/-- vFinal's `{F,H}_TF = {F,H}_classical`: on the Hamiltonian the tether is silent, so
the reversible dynamics stay exactly classical. -/
theorem tetheredBracket_kineticEnergy (classical : LinearMap.BilinForm ℝ H) (κ w : ℝ)
    (u F : H) :
    ⦃F, kineticEnergyGradient u⦄_𝔗F[classical; κ, w, u] = classical F (kineticEnergyGradient u) := by
  simp [tetheredBracket, degeneracy_verification]

/-! ## 8. C3 made concrete: controllable negative feedback -/

/-- `Π_u` fixes vectors already orthogonal to `u`. -/
theorem piU_eq_self_of_inner_eq_zero {u e : H} (he : ⟪u, e⟫ = 0) : piU u e = e := by
  rw [piU_apply, he, zero_div, zero_smul, sub_zero]

/-- **C3 — controllable negative feedback.**

May wording (living document, axiom (A5)): "production of negative quadratic feedback
with coefficient fixed by matching"; and "with κ = 1 fixed by exact leading-term
matching to the stretching coefficient" (κ = 1 being the May teaching placeholder).
The living document also says the tether "replaces [the linear growth] with a negative
quadratic feedback. This correction is derived by coefficient matching at the spatial
maximum of |ω|²."

Formal reading, deliberately *weaker than saturation*:
* `nonpos` — the feedback is negative: `B(F,F) ≤ 0` for every `F`;
* `calibrated` — *one* normalized direction `e ⟂ u`, `‖e‖ = 1` (the stand-in for "the
  spatial maximum of |ω|²") has the matched leading coefficient `B(e,e) = -κ w`.

Candour: the calibration pins `B` on a single direction, not on all of `H`. The Aug 26
saturation hypothesis pinned `B(F,F)` for *every* `F`, which already is the conclusion.
Here the spread from one direction to all directions is *proved* (C1 + C2, Schur step);
C3 only normalizes the one remaining scalar. It still is a normalization: it is where
`κ w` enters, by matching, exactly as the May text says. -/
structure ProducesControllableNegativeFeedback (κ w : ℝ) (u : H)
    (B : LinearMap.BilinForm ℝ H) : Prop where
  nonpos : ∀ F, B F F ≤ 0
  calibrated : ∃ e : H, ⟪u, e⟫ = 0 ∧ ‖e‖ = 1 ∧ B e e = -(κ * w)

/-- `hC3fix`, now proved: within the tether family, C3 forces `c = κ w`. -/
theorem feedback_fixes_coefficient {κ w : ℝ} {u : H} (c : ℝ)
    (h : ProducesControllableNegativeFeedback κ w u 𝔗_F[c, 1, u]) : c = κ * w := by
  obtain ⟨e, he, hn, hB⟩ := h.calibrated
  rw [frohmanianTether_apply, piU_eq_self_of_inner_eq_zero he, real_inner_self_eq_norm_sq,
    hn] at hB
  linarith

/-- The Frohmanian tether satisfies C3 (for `κ, w ≥ 0`, dimension ≥ 2). -/
theorem frohmanianTether_feedback [FiniteDimensional ℝ H] (hdim : 2 ≤ Module.finrank ℝ H)
    {κ w : ℝ} (hκ : 0 ≤ κ) (hw : 0 ≤ w) (u : H) :
    ProducesControllableNegativeFeedback κ w u 𝔗_F[κ, w, u] := by
  refine ⟨frohmanianTether_self_nonpos hκ hw u, ?_⟩
  obtain ⟨e, he, hn⟩ := exists_unit_orthogonal hdim u
  refine ⟨e, he, hn, ?_⟩
  rw [frohmanianTether_apply, piU_eq_self_of_inner_eq_zero he, real_inner_self_eq_norm_sq,
    hn]
  ring

/-- **Uniqueness of the Minimal Metric Tether — unconditional form.** In dimension ≥ 3,
a symmetric bilinear correction satisfies C1 (invariance), C2 (degeneracy) and C3
(controllable negative feedback, calibrated to `κ w`) **iff** it is `𝔗_F[κ, w, u]`. -/
theorem uniqueness_of_minimal_metric_tether_iff [FiniteDimensional ℝ H]
    (hdim : 3 ≤ Module.finrank ℝ H) {κ w : ℝ} (hκ : 0 ≤ κ) (hw : 0 ≤ w) (u : H)
    (hu : u ≠ 0) (B : LinearMap.BilinForm ℝ H) :
    IsAdmissibleCorrection u (ProducesControllableNegativeFeedback κ w u) B ↔
      B = 𝔗_F[κ, w, u] := by
  constructor
  · intro hB
    exact uniqueness_of_minimal_metric_tether hdim κ w u hu _
      (fun c hc => feedback_fixes_coefficient c hc) B hB
  · rintro rfl
    exact frohmanianTether_admissible κ w u _ (frohmanianTether_feedback (by omega) hκ hw u)

/-- **Frohmanian Symplectic Tether Theorem** — the May 30 export name. Existence and
uniqueness of the minimal metric tether under C1–C3 (abstract model). -/
theorem frohmanian_symplectic_tether_theorem_calibrated [FiniteDimensional ℝ H]
    (hdim : 3 ≤ Module.finrank ℝ H) {κ w : ℝ} (hκ : 0 ≤ κ) (hw : 0 ≤ w) (u : H)
    (hu : u ≠ 0) :
    IsAdmissibleCorrection u (ProducesControllableNegativeFeedback κ w u) 𝔗_F[κ, w, u] ∧
      ∀ B, IsAdmissibleCorrection u (ProducesControllableNegativeFeedback κ w u) B →
        B = 𝔗_F[κ, w, u] :=
  ⟨(uniqueness_of_minimal_metric_tether_iff hdim hκ hw u hu _).2 rfl,
    fun B => (uniqueness_of_minimal_metric_tether_iff hdim hκ hw u hu B).1⟩

end Frohman.Tether
