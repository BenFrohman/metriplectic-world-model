/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import FrohmanianSymplecticTether.SymplecticTether
public import FrohmanianSymplecticTether.TetheredLyapunov
public import FrohmanianSymplecticTether.Uniqueness
public import FrohmanianSymplecticTether.IndependentMajorant
public import FrohmanianSymplecticTether.ArnoldGeometric
public import FrohmanianSymplecticTether.NS_Equations
public import FrohmanianSymplecticTether.AnalyticPipeline
public import Mathlib.Analysis.Calculus.ContDiff.Basic

-- NOTE: No silencing options. The build has 0 `sorry`; classical inputs enter as explicit
-- hypotheses. Full convention documented in TetheredLyapunov.lean.

-- Error Explanations (Lean Language Reference) — Assembly Layer
-- This file historically contained the last 7 hard errors (custom unicode-in-identifier notation,
-- ambiguous CoadjointOrbit export, ContDiff ∞ syntax, vorticity_L references). All were fixed
-- in the "priority 2" work (clean ASCII identifiers, open hygiene with `hiding`, granular
-- ContDiff import, alignment to the 6-arg schematic global_regularity signature).
-- The full Error Explanations table integration (this session) confirms that the current state
-- avoids every row:
-- • synthInstanceFailed / unknownIdentifier / invalidDottedIdent / invalidField: eliminated by
--   the notation cleanup and the explicit `open ArnoldGeometric hiding CoadjointOrbit`.
-- • inferBinderTypeFailed: the schematic theorems (frohmanian_tether_theorem,
--   global_regularity_for_NS) now have fully explicit 6-arg signatures matching the author
--   abstract; all binders are elaborated before bodies.
-- • dependsOnNoncomputable: top-level theorems that use choice (Gâteaux representative,
--   Biot–Savart integrals, Riccati solution) are marked `noncomputable` or live in
--   a noncomputable context.
-- • projNonPropFromProp / propRecLargeElim: C1–C3 and smoothness are real `Prop`s
--   (`ContDiff`, `Integrable`, degeneracy, feedback), never `True` gates.
-- • redundantMatchAlt / inductionWithNoAlts: none present.
-- • ctor* / inductiveParam*: no new inductives declared here.
-- The assembly point deliberately stays thin (it only wires Layer 1 geometric justification
-- to Layer 2 analytic continuation). This keeps the error surface minimal and makes the
-- "unique proof confirmation" property easy to audit: any future green proof of the novel
-- geometry will be visibly the one that satisfies the author abstract's ∃! form.
-- Cross-ref: all prior reference blocks (especially §5 module hygiene and the GlobalRegularity
-- cleanup that removed the last hard errors) are still in force.

/-! # Global Regularity: Final Integration and the Frohmanian Symplectic Tether Theorem

This module assembles everything and states the main theorem exactly as
formulated in the audited LaTeX (including the three parts of Theorem 2.1
and the corollary from the PASS 5 argument, which is **conditional**: see below).

The top-level statement below is the exact Abstract formulation supplied by the author
(Sections 1 + overall theorem), using the Frohmanian Symplectic Tether as the central device.
-/

namespace GlobalRegularity

open FrohmanianTether TetheredLyapunov
open ArnoldGeometric hiding CoadjointOrbit
open ArnoldGeometric (CoadjointOrbit)
open NavierStokes3D MeasureTheory

variable {kappa : ℝ}
-- FrohmanianTether ns (containing uniqueness_of_minimal_tether) is qualified below to avoid
-- "unknown namespace" during module elaboration (the export in root makes it available at top level).

/-! ## Main Theorem — Frohmanian Symplectic Tether Theorem -/

/-- High-level statement of the full theorem — **conditional**.
The regularity conjunct holds *given* `hDI : ∀ u₀ ν, FrohmanianTetherRate u₀ ν`
(the rate `M' ≤ C M² - κ'' M³` along every solution) and the classical local-theory
binders `hKato`, `hTlb`, `hInt`, `huniq_shift`, `huniq`. `FrohmanianTetherRate` is open
and is not derived from the unmodified equation in this repository
(see `HWEIGHT_OBSTRUCTION.md`). This is not an unconditional Navier–Stokes solution.
The work is split across SymplecticTether.lean (existence + uniqueness of the Tether)
and TetheredLyapunov.lean (global regularity conditional on the rate, via the majorant).
Editor green ticks only mean this declaration elaborated. The certificate is
`#print axioms frohmanian_tether_theorem`: it must list `propext`,
`Classical.choice`, `Quot.sound` and must **not** list `sorryAx`. -/
public theorem frohmanian_tether_theorem (hκ : 0 < kappa)
    (hKato : ∀ u₀ ν, ContDiff ℝ (⊤ : ℕ∞) u₀ → (∀ x, div u₀ x = 0) →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) → 0 < ν →
      KatoLocalWitness u₀ ν)
    (hDI : ∀ u₀ ν, FrohmanianTetherRate u₀ ν)
    (τ : ℝ) (hτ : 0 < τ)
    (hTlb : ∀ u₁ ν (hsm : ContDiff ℝ (⊤ : ℕ∞) u₁)
      (hdiv : ∀ x, div u₁ x = 0)
      (hE : Integrable (fun x : T3 => ‖u₁ x‖ ^ 2))
      (hν : 0 < ν),
      τ ≤ (hKato u₁ ν hsm hdiv hE hν).T)
    (hInt : ∀ u₀ ν (_hν : 0 < ν) (T : ℝ) (v : TimeDependentVelocity)
      (q : TimeDependentPressure),
      T ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun x : T3 => ‖v t x‖ ^ 2))
    (huniq_shift : ∀ u₀ ν (_hν : 0 < ν) (T : ℝ) (v : TimeDependentVelocity)
      (q : TimeDependentPressure),
      T ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ (w' : KatoLocalWitness (v t) ν),
          ∀ s ∈ Set.Icc (0 : ℝ) w'.T, v (t + s) = w'.u s)
    (huniq : ∀ u₀ ν (w : KatoLocalWitness u₀ ν),
      ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
        T' ∈ existenceTimes u₀ ν →
        v 0 = u₀ →
        NS_PDE v q ν →
        (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
        IsPhysicalNSSolution v →
        ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t) :
  ∃ (𝔗_F : CoadjointOrbit → Functional → Functional → ℝ),
    (∀ F ω,
      FunctionalDerivative KineticEnergyHamiltonian ω =
          velocity_from_vorticity ω →
      (∀ x, div (velocity_from_vorticity ω) x = 0) →
      Integrable (fun y => ‖velocity_from_vorticity ω y‖ ^ 2) →
      TetheredBracket kappa F KineticEnergyHamiltonian ω =
        ClassicalBracket F KineticEnergyHamiltonian ω) ∧
    (∀ (B : CoadjointOrbit → Functional → Functional → ℝ),
      (∀ ω F G, B ω F G = B ω G F) →
      InvariantUnderCoadjointAction B →
      DegenerateWRTKineticEnergy B →
      ProducesControllableNegativeFeedback kappa B →
      SaturatesTetherQuadratic kappa B →
      Polarizes B →
      Polarizes (TetherKernel kappa) →
      ∀ ω F G, B ω F G = 𝔗_F ω F G) ∧
    (∀ (B : CoadjointOrbit → Functional → Functional → ℝ)
      (α : CoadjointOrbit → T3 → ℝ),
      HasTetherKernelDensity B α →
      (∀ ω x, α ω x = canonicalTetherDensity kappa ω x) →
      ∀ ω F G, B ω F G = 𝔗_F ω F G) ∧
    (∀ (u₀ : VelocityField) (ν : ℝ),
      0 < ν →
      (∀ x, div u₀ x = 0) →
      ContDiff ℝ (⊤ : ℕ∞) u₀ →
      Integrable (fun x : T3 => ‖u₀ x‖ ^ 2) →
      ∃ (u : ℝ → VelocityField) (p : ℝ → PressureField),
        NS_PDE u p ν ∧
        u 0 = u₀ ∧
        (∀ t ≥ (0 : ℝ), ContDiff ℝ (⊤ : ℕ∞) (u t)) ∧
        (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
        (∀ t ≥ (0 : ℝ), ∀ x, div (u t) x = 0)) := by
  refine ⟨TetherKernel kappa, ?_, ?_, ?_, ?_⟩
  · intro F ω hδ hdiv hInt
    exact tethered_reproduces_classical_euler F ω hδ hdiv hInt
  · intro B hanti hC1 hC2 hC3 hsat hpolB hpolT ω F G
    exact uniqueness_of_minimal_tether hκ B hanti hC1 hC2 hC3 hsat hpolB hpolT ω F G
  · intro B α hrepr hα ω F G
    exact uniqueness_of_kernel_density B α hrepr hα ω F G
  · intro u₀ ν hνpos hdiv hsm hE
    let w := hKato u₀ ν hsm hdiv hE hνpos
    have hreg :=
      global_regularity_of_constructions u₀ ν hdiv hsm hE hνpos
        (fun u₁ hsm₁ hdiv₁ hE₁ => hKato u₁ ν hsm₁ hdiv₁ hE₁ hνpos)
        (fun u p hNS hu0 hphys =>
          let ⟨C, κ'', hC, hκ, hd, hdd, hc, _⟩ := hDI u₀ ν u p hνpos hNS hu0 hphys
          ⟨C, κ'', hC, hκ, hd, hdd, hc⟩)
        τ hτ
        (fun u₁ hsm₁ hdiv₁ hE₁ => hTlb u₁ ν hsm₁ hdiv₁ hE₁ hνpos)
        (hInt u₀ ν hνpos)
        (huniq_shift u₀ ν hνpos)
        (huniq u₀ ν w)
    exact ⟨w.u, w.p, hreg⟩

/-! ## Abstract (exact formulation supplied by the author) -/

open NavierStokes3D

/-- IsSmooth is the classical notion of infinite differentiability (black-box via ContDiff). -/
public abbrev IsSmooth (f : VelocityField) : Prop := ContDiff ℝ (⊤ : ℕ∞) f

/-- Sup-norm (L^∞) of a vorticity field (classical, black-box, using clean ASCII name to avoid
unicode identifier issues in the current Lean/mathlib pin).
Still exactly matches the abstract intent: a classical sup-norm proxy for |ω|_{L^∞} used in BKM-type criteria.

Marked noncomputable because it depends on Real.instSupSet (standard for sup-norm proxies in analysis). -/
public noncomputable def vorticity_sup_norm (ω : VorticityField) : ℝ :=
  NavierStokes3D.vorticity_sup_norm ω

-- Clean alias (no custom unicode notation) provided so that references in comments / the abstract
-- theorem can mention the L^∞ control without triggering parser/elaboration problems.
noncomputable abbrev vorticity_sup_norm_proxy (ω : VorticityField) : ℝ := vorticity_sup_norm ω

/-- The solution satisfies the unmodified 3D incompressible Navier–Stokes equations
and is physically admissible (`IsPhysicalNSSolution u`). -/
public def satisfies_NavierStokes (u : TimeDependentVelocity) (ν : ℝ) : Prop :=
  IsPhysicalNSSolution u ∧ ∃ p : TimeDependentPressure, navier_stokes_eq u p ν

/-- Main theorem (Abstract, formalized) — **conditional on `hRiccati`**.

`hRiccati : FrohmanianTetherBound (u0 0) ν` is a time-uniform bound on `‖ω‖_∞`.
It is open; by BKM it is equivalent in difficulty to regularity itself
(see `FrohmanianSymplecticTether/GlobalRegularity.lean`, `FrohmanianTetherClosingBound`). Given it, plus the
classical local-theory binders `w`, `hrestart`, `huniq`, every smooth, divergence-free
initial field generates a unique global smooth solution. Not an unconditional Navier–Stokes solution.

This is the top-level statement whose proof proceeds via the Frohmanian Symplectic Tether
(the 5-step uniqueness + tethered Lyapunov + independent majorant + BKM upgrade).
-/
public theorem global_regularity_for_NS
    (u0 : TimeDependentVelocity)
    (h_div_free : ∀ t x, div (u0 t) x = 0)
    (h_smooth : IsSmooth (u0 0))
    (h_finite_energy : Integrable (fun x : T3 => ‖u0 0 x‖ ^ 2))
    (ν : ℝ) (h_ν_pos : ν > 0)
    (w : KatoLocalWitness (u0 0) ν)
    (hRiccati : FrohmanianTetherBound (u0 0) ν)
    (τ : ℝ) (hτ : 0 < τ)
    (hrestart : ∀ t : ℝ, 0 ≤ t → (t : EReal) < Tstar (u0 0) ν →
      ∃ T' ∈ existenceTimes (u0 0) ν, t + τ ≤ T')
    (huniq : ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes (u0 0) ν →
      v 0 = u0 0 →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t) :
  ∃ (u : TimeDependentVelocity),
    (∀ t ≥ (0 : ℝ), IsSmooth (u t)) ∧
    (u 0 = u0 0) ∧
    (∀ t ≥ (0 : ℝ), satisfies_NavierStokes u ν) ∧
    (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
    (∀ v : TimeDependentVelocity,
      (∀ t ≥ (0 : ℝ), IsSmooth (v t)) →
      v 0 = u0 0 →
      (∀ t ≥ (0 : ℝ), satisfies_NavierStokes v ν) →
      ∀ t ≥ (0 : ℝ), v t = u t) := by
  obtain ⟨hNS, hu0, hsm, hnn, _hdiv⟩ :=
    TetheredLyapunov.global_regularity_of_restart (u0 0) ν
      (fun x => h_div_free 0 x) h_smooth h_finite_energy h_ν_pos
      w (fun u p hNS hu0 hphys =>
          let ⟨Y, hb, hc, _⟩ := hRiccati u p hNS hu0 hphys
          ⟨Y, hb, hc⟩) τ hτ hrestart huniq
  refine ⟨w.u, hsm, hu0, ?ns, hnn, ?uniq⟩
  · intro _t _ht
    exact ⟨w.phys, w.p, hNS⟩
  · intro v hsmv hv0 hNSv t ht
    obtain ⟨hphys_v, q, hq⟩ := hNSv 0 le_rfl
    have ht1 : 0 < t + 1 := by linarith
    have hmem : t + 1 ∈ existenceTimes (u0 0) ν :=
      mem_existenceTimes (u0 0) ν ht1 v q hv0 hq (fun s hs => hsmv s hs.1) hphys_v
    exact (huniq (t + 1) v q hmem hv0 hq (fun s hs => hsmv s hs.1) hphys_v
      t ⟨ht, le_of_lt (lt_add_one t)⟩).symm

-- Finite kinetic energy of the initial field. Mathlib's `Integrable f` is
-- `AEStronglyMeasurable f ∧ HasFiniteIntegral f`. An earlier encoding wrote
-- `HasFiniteIntegral (fun t => u0 t • x) vol`: that is the finite-integral
-- conjunct of the same energy hypothesis, but it mixed the time variable into
-- a spatial density and did not type as `∫ ‖u₀‖²`. The hypothesis here is the
-- classical Kato/Leray L² energy at `t = 0`, identical to `local_existence`
-- and `frohmanian_tether_theorem`. One statement, one energy condition;
-- not a second theorem. On `T³`, smooth data are automatically integrable;
-- the binder is kept because Kato's theorem is classically stated in L².
-- The L^∞ bound on vorticity is the quantity controlled by the tether + majorant.

/-!
# Validating a Lean Proof — Integration of the Lean Language Reference

This block was added during the systematic reference-integration campaign upon receipt of the
full "Validating a Lean Proof" section (escalating checks: blue double ticks → #print axioms →
lean4checker --fresh → gold-standard comparator + external checkers).

The section is of the *highest* importance for this project because:
- The central claim (global regularity via the novel Frohmanian Symplectic Tether) is a
  high-stakes mathematical result (3D Navier–Stokes Regularity territory).
- The user has repeatedly emphasized the desire for "unique proof confirmation".
- The build has 0 `sorry`. Local existence, BKM continuation and the tethered
  Riccati majorant enter as explicitly stated hypotheses, so every regularity
  statement here is conditional on them. Transparent validation hygiene is therefore essential.

Current toolchain (as of this session): `leanprover/lean4:v4.28.0`
(This is exactly the version the user requested we retain, matching Terence Tao’s Analysis I
repository pin. On 4.28.0 the older `Lean.trustCompiler` mechanism is still active for any
native evaluation. See the dedicated subsection below.)

## The Four Escalating Levels of Validation (directly from the reference)

1. **Blue Double Check Marks (everyday interactive use)**
   - What it means: The theorem elaborated successfully and the kernel accepted a proof term
     constructed from the definitions, theorems, and axioms in scope.
   - Current status for this project: the build has 0 `sorry`; classical inputs enter as
     explicit hypotheses.
   - Protection: incomplete proofs, explicit `sorry` in the *current* theorem, honest tactic bugs.
   - Limitation: does *not* detect `sorry` or incomplete proofs in dependencies.

2. **#print axioms thmName**
   - What it means: Lists every axiom the theorem (and everything it depends on) relies upon.
   - Expected output on a finished proof of the novel geometry:
       `propext`, `Classical.choice`, `Quot.sound`
     (the three standard axioms of Lean's logic — benign).
   - Any appearance of `sorryAx` → the theorem or a dependency uses `sorry` or is incomplete.
   - Any appearance of `Lean.trustCompiler` (on 4.28.0) → native evaluation was used somewhere
     in the dependency chain (see dedicated note below).
   - Any other custom axiom → the result is only valid relative to the soundness of that axiom.
   - **Action taken in this file**: concrete `#print axioms` commands are placed immediately after
     the two top-level schematic theorems (see below).

3. **lean4checker --fresh**
   - Replays the proofs stored in the `.olean` files through the kernel.
   - Catches a small class of bugs in Lean's core handling of kernel state and simple attacks
     that bypass the elaborator.
   - Recommended as part of CI (the lean-action GitHub Action supports `lean4checker: true`).
   - Limitation: still trusts the structural integrity of the `.olean` files themselves.

4. **Gold Standard: comparator + external checkers (nanoda, etc.)**
   - For high-risk scenarios (proof marketplaces, high-reward competitions, unaligned AI,
     or when one wants protection against seriously malicious proof attempts that try to
     compromise how Lean interprets a statement).
   - Builds in a sandbox, exports the proof term to a serialized format, then validates
     *outside* the sandbox using both Lean's kernel *and* independent external checkers.
   - This is the level that would give the strongest "unique proof confirmation" for the
     novel Frohmanian geometry (the 5-step canonicity + explicit Jacobi identity on F_p).
   - Requires that the proof avoid `Lean.trustCompiler` / native evaluation on 4.28.0
     (external checkers have no access to the Lean compiler).

## On Lean.trustCompiler (relevant because we are pinned to 4.28.0)

The project is deliberately kept on `v4.28.0` (per the user's explicit request, matching the
pin used in Terence Tao’s Analysis I formalization repository).

On this version:
- Any use of `decide +native`, `bv_decide`, or direct `Lean.ofReduceBool` introduces the axiom
  `Lean.trustCompiler`.
- External checkers (lean4checker with --fresh, comparator + nanoda) *cannot* replay such proofs.
- The reference is clear: "When that level of checking is needed, proofs have to avoid using
  native evaluation."

**Project policy for validation levels (honest vs. malicious context)**

- Classical black-box infrastructure (local existence, BKM, parabolic regularity, CZ estimates,
  transport/Young/Hölder algebra, ODE comparison, etc.) may freely use any convenient tactics,
  including native evaluation, during development. These are documented with citations and
  will eventually be replaced by citations to mathlib or small ForMathlib lemmas.
- The *novel geometric core* (everything in SymplecticTether.lean: TetherKernel definition,
  the five atomic `step1_locality` … `step5_higher_order` lemmas, `tethered_jacobi_identity`
  with its explicit cyclic-sum calculation on test functionals F_p, degeneracy proofs,
  invariance, etc.) **must eventually be free of native evaluation** if we ever wish to subject
  the final artifact to comparator + external checkers for the strongest possible assurance.
- The analytic layer in TetheredLyapunov (majorant ODE, differential inequality, Lemma 3.1
  continuation) sits in the middle: the independent-majorant construction itself is pure
  mathematics and should be kernel-checkable; heavy numerical or decision-procedure work
  inside classical inequalities can stay native if clearly marked.

This distinction directly supports the four living audit checklists (especially Non-Circularity
and Canonicality) and the two-layer architecture.

## Current Honest Development State (rails off)

The build has 0 `sorry`, and `#print axioms` reports only `propext`,
`Classical.choice` and `Quot.sound`. Local existence, BKM continuation and the
tethered Riccati majorant of `‖ω‖_∞` enter as explicitly stated hypotheses;
results that use them are conditional on them.


## Concrete Commands (live in this file)

After the two main theorems you will find:

    #print axioms frohmanian_tether_theorem
    #print axioms global_regularity_for_NS

Run these (or `lake build` followed by inspecting the output) to see the current axiom
surface. As the proof matures, these commands become part of the permanent validation
ritual.

See the new "Validation and Trust Strategy" section in Blueprint.md for the full mapping of
these four levels onto the project's novel geometry and the goal of unique proof confirmation.
-/

#print axioms frohmanian_tether_theorem
#print axioms global_regularity_for_NS


/-! ## Non-Vacuity and Joint Satisfiability after the `IsPhysicalNSSolution` Repair

Adding `IsPhysicalNSSolution` (pointwise time-differentiability `DifferentiableAt ℝ (fun s => u s x) t`,
spatial continuity, and the Leray L² energy inequality `∫ ‖u t x‖² ≤ ∫ ‖u 0 x‖²`) rules out
step-in-time parasitic fields (`stepField`) and unbounded non-L² waves. With this repair:
1. `stepField` is proved not physically admissible (`stepField_not_physical`);
2. the repaired uniqueness hypothesis `huniq` is proved satisfiable at `u₀ = 0` (`repaired_huniq_at_zero`);
3. `FrohmanianTetherBound 0 ν` and `FrohmanianTetherRate 0 ν` are proved unconditionally (`frohmanianTetherBound_zero`, `frohmanianTetherRate_zero`);
4. `GlobalRegularity.global_regularity_for_NS` is instantiated unconditionally at `u₀ = 0` (`global_regularity_for_NS_nonvacuous_at_zero`), proving that all of its hypotheses are jointly satisfiable. -/

/-- Step-in-time constant field: `0` for `t ≤ 1`, `e₀` for `t > 1`. -/
@[expose] public noncomputable def stepField : TimeDependentVelocity :=
  fun t _ => if 1 < t then EuclideanSpace.single 0 (1 : ℝ) else 0

/-- `stepField` violates `IsPhysicalNSSolution` (it jumps from `0` to `e₀ ≠ 0` at `t = 1`). -/
public theorem stepField_not_physical : ¬ IsPhysicalNSSolution stepField := by
  intro hphys
  have hS0 : stepField 0 = 0 := by funext x; simp [stepField]
  have h20 : stepField 2 = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero stepField hS0 hphys 2 (by norm_num)
  have h2 := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) (congrFun h20 0)
  simp [stepField] at h2

/-- With `IsPhysicalNSSolution v`, the `L²` integrability hypothesis `hInt` of
`restart_of_kato_quantitative`, `global_regularity_of_constructions`, and
`frohmanian_tether_theorem` holds **unconditionally** for every initial datum
`u₀` and viscosity `ν`. -/
public theorem repaired_hInt (u₀ : VelocityField) (ν : ℝ) :
    ∀ (T : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T ∈ existenceTimes u₀ ν →
      v 0 = u₀ →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun x : T3 => ‖v t x‖ ^ 2) := by
  intro _T v _q _hmem _hv0 _hpde _hsm hphys t ht
  exact hphys.2.2.1 t ht.1

/-- With `IsPhysicalNSSolution v`, the shifted-restart uniqueness hypothesis
`huniq_shift` of `restart_of_kato_quantitative`,
`global_regularity_of_constructions`, and `frohmanian_tether_theorem` is
**provably satisfied** at `u₀ = 0`: both `v` and any restart witness `w'`
starting at `v t = 0` vanish identically on `[0, ∞)`. -/
public theorem repaired_huniq_shift_at_zero (ν : ℝ) :
    ∀ (T : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T ∈ existenceTimes (0 : VelocityField) ν →
      v 0 = (0 : VelocityField) →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∀ (w' : KatoLocalWitness (v t) ν),
          ∀ s ∈ Set.Icc (0 : ℝ) w'.T, v (t + s) = w'.u s := by
  intro _T v _q _hmem hv0 _hpde _hsm hphys t ht w' s hs
  have hvt : v t = 0 := eq_zero_of_isPhysicalNSSolution_zero v hv0 hphys t ht.1
  have hvts : v (t + s) = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero v hv0 hphys (t + s) (add_nonneg ht.1 hs.1)
  have hw0 : w'.u 0 = 0 := w'.init.trans hvt
  have hws : w'.u s = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero w'.u hw0 w'.phys s hs.1
  rw [hvts, hws]

/-- With `IsPhysicalNSSolution v`, the uniqueness binder `huniq` of `global_regularity_for_NS`
is unconditionally satisfied at `u₀ = 0` for *every* `w : KatoLocalWitness 0 ν`. -/
public theorem repaired_huniq_at_zero (ν : ℝ) (w : KatoLocalWitness 0 ν) :
    ∀ (T' : ℝ) (v : TimeDependentVelocity) (q : TimeDependentPressure),
      T' ∈ existenceTimes 0 ν →
      v 0 = 0 →
      NS_PDE v q ν →
      (∀ t ∈ Set.Icc (0 : ℝ) T', ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      IsPhysicalNSSolution v →
      ∀ t ∈ Set.Icc (0 : ℝ) T', w.u t = v t := by
  intro T' v _q _hmem hv0 _hpde _hsm hphys t ht
  have hw_zero : w.u t = 0 := eq_zero_of_isPhysicalNSSolution_zero w.u w.init w.phys t ht.1
  have hv_zero : v t = 0 := eq_zero_of_isPhysicalNSSolution_zero v hv0 hphys t ht.1
  exact hw_zero.trans hv_zero.symm

/-- Vorticity and its sup-norm vanish on the zero velocity field. -/
public theorem vorticity_sup_norm_zero_field :
    NavierStokes3D.vorticity_sup_norm (vorticity (0 : VelocityField)) = 0 := by
  unfold NavierStokes3D.vorticity_sup_norm vorticity
  have hcurl : (fun x : T3 => ‖curl (0 : VelocityField) x‖) = fun _ => (0 : ℝ) := by
    funext x
    rw [curl_zero x, norm_zero]
  rw [hcurl, ciSup_const]

/-- `FrohmanianTetherBound 0 ν` holds unconditionally after the `IsPhysicalNSSolution` repair. -/
public theorem frohmanianTetherBound_zero (ν : ℝ) : FrohmanianTetherBound 0 ν := by
  intro u p _hNS hu0 hphys
  have hu_all : ∀ τ : ℝ, u τ = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero_all u hu0 hphys
  have hfun : (fun τ : ℝ => NavierStokes3D.vorticity_sup_norm (vorticity (u τ))) = fun _ => (0 : ℝ) := by
    funext τ
    rw [hu_all τ, vorticity_sup_norm_zero_field]
  refine ⟨0, ?_, ?_, ?_⟩
  · intro τ _hτ
    rw [hu_all τ, vorticity_sup_norm_zero_field]
  · rw [hfun]
    exact continuous_const
  · intro τ _hτ
    refine ⟨0, ?_⟩
    rintro y ⟨x, rfl⟩
    dsimp [vorticity]
    rw [hu_all τ, curl_zero x, norm_zero]

/-- `FrohmanianTetherRate 0 ν` holds unconditionally after the `IsPhysicalNSSolution` repair. -/
public theorem frohmanianTetherRate_zero (ν : ℝ) : FrohmanianTetherRate 0 ν := by
  intro u p _hν _hNS hu0 hphys
  have hu_all : ∀ τ : ℝ, u τ = 0 :=
    eq_zero_of_isPhysicalNSSolution_zero_all u hu0 hphys
  have hfun : (fun τ : ℝ => NavierStokes3D.vorticity_sup_norm (vorticity (u τ))) = fun _ => (0 : ℝ) := by
    funext τ
    rw [hu_all τ, vorticity_sup_norm_zero_field]
  refine ⟨1, 1, one_pos, one_pos, ?_, ?_, ?_, ?_⟩
  · intro s _hs
    rw [hfun]
    exact differentiableAt_const 0
  · intro s _hs
    have hds : deriv (fun τ => NavierStokes3D.vorticity_sup_norm (vorticity (u τ))) s = 0 := by
      rw [hfun]; simp
    rw [hds, hu_all s, vorticity_sup_norm_zero_field]
    norm_num
  · rw [hfun]
    exact continuous_const
  · intro τ _hτ
    refine ⟨0, ?_⟩
    rintro y ⟨x, rfl⟩
    dsimp [vorticity]
    rw [hu_all τ, curl_zero x, norm_zero]

/-- **Kernel-verified non-vacuity of `GlobalRegularity.global_regularity_for_NS`:**
at quiescent initial data `u0 = 0`, every hypothesis of `global_regularity_for_NS`
(`h_div_free`, `h_smooth`, `h_finite_energy`, `w = kato_witness_zero ν`,
`hRiccati = frohmanianTetherBound_zero ν`, `hrestart`, and `huniq = repaired_huniq_at_zero ν`)
is unconditionally discharged, producing a global smooth solution without any unproved assumptions. -/
public theorem global_regularity_for_NS_nonvacuous_at_zero (ν : ℝ) (hν : 0 < ν) :
    ∃ (u : TimeDependentVelocity),
      (∀ t ≥ (0 : ℝ), IsSmooth (u t)) ∧
      (u 0 = 0) ∧
      (∀ t ≥ (0 : ℝ), satisfies_NavierStokes u ν) ∧
      (∀ t ≥ (0 : ℝ), vorticity_sup_norm (vorticity (u t)) ≥ 0) ∧
      (∀ v : TimeDependentVelocity,
        (∀ t ≥ (0 : ℝ), IsSmooth (v t)) →
        v 0 = 0 →
        (∀ t ≥ (0 : ℝ), satisfies_NavierStokes v ν) →
        ∀ t ≥ (0 : ℝ), v t = u t) :=
  global_regularity_for_NS
    (fun _ => 0)
    (fun _ x => div_zero_field x)
    contDiff_const
    (by simp)
    ν hν
    (kato_witness_zero ν)
    (frohmanianTetherBound_zero ν)
    1 one_pos
    (fun t ht _ => ⟨t + 1, mem_existenceTimes_zero ν (by linarith), le_rfl⟩)
    (repaired_huniq_at_zero ν (kato_witness_zero ν))

#print axioms stepField_not_physical
#print axioms repaired_hInt
#print axioms repaired_huniq_shift_at_zero
#print axioms repaired_huniq_at_zero
#print axioms frohmanianTetherBound_zero
#print axioms frohmanianTetherRate_zero
#print axioms global_regularity_for_NS_nonvacuous_at_zero

end GlobalRegularity

