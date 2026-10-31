# Metriplectic World Model

> **Work in progress.** Draft formalization; results are stated with their exact status (proved unconditionally / conditional on named Props). Nothing here solves the Clay problem or proves Navier–Stokes regularity.
>
> **DOIs:** reduction paper [10.5281/zenodo.23842298](https://doi.org/10.5281/zenodo.23842298); main paper [10.5281/zenodo.23842565](https://doi.org/10.5281/zenodo.23842565)


Lean 4 + Mathlib (`v4.30.0-rc1`). Author: Benjamin Stanley Frohman (ORCID 0009-0006-7068-3718).

**This repository formalizes a model.** The model is the Frohmanian tethered metriplectic
system. It is a different system from unmodified 3D Navier–Stokes: it adds a metric (tether)
bracket and a cubic damping of the peak vorticity. Nothing here proves anything about
unmodified Navier–Stokes, and it does not resolve the Clay Millennium problem.

## The model

* **Brackets.** The Lie–Poisson (Arnold) bracket `{F,H} = P(dF,dH)` is antisymmetric. The
  metric (tether) bracket `(F,S) = G(dF,dS)` is symmetric and positive semidefinite. In the
  velocity-tether instance, `G = −TetherKernelVel κ`, where
  `TetherKernelVel κ ω F G = −κ ∫ |ω|² ⟨Π_u curl δF/δω, Π_u curl δG/δω⟩`.
* **Generator.** `dF/dt = {F,H} + (F,S)`.
* **Degeneracy conditions.** `P(·, dS) = 0` (the entropy is a Casimir) and `G(·, dH) = 0`.
* **Modified vorticity dynamics.** At the point of maximum vorticity, the tether adds the
  term `−κ y⁴` to `y y'`. This gives the model inequality `M' ≤ C M² − κ M³` for the peak
  vorticity `M`. Unmodified Navier–Stokes has no such term (`κ = 0`).

## What the model implies (each item below is a theorem, or conditional as noted)

1. **Uniform-in-time vorticity ceiling.** For every `κ > 0`:
   `M t ≤ max (M 0) (max (C/κ) 0)` for all `t ≥ 0`.
   * `uniform_ceiling` is **proved** from the differential inequality.
   * `model_uniform_ceiling` is conditional on `TetheredMaxRate`.
   * `ceiling_antitone_kappa` (**proved**): a stronger tether gives a lower ceiling.
   * `absorbing` (**proved**): if `M 0 ≤ C/κ`, then `M` stays at or below `C/κ` for all time.
2. **Energy conservation and the degeneracy structure.**
   * `energy_conserved` (**proved**): `dH/dt = 0` for any metriplectic system.
   * `energy_const_along` (**proved**): `H` is constant along any trajectory of the generator.
   * For the velocity tether, `degen_G` is **proved** from `KineticEnergyCurlIdentity` plus
     finite energy, by the ported C2 result `tetherKernelVel_C2_at`.
   * `velocityTether_energy_conserved` is conditional on `KineticEnergyCurlIdentity` and
     `EntropyCasimir`.
3. **Entropy production.**
   * `entropy_production` and `gen_entropy_eq` (**proved**): `dS/dt = G(dS,dS) ≥ 0`.
   * `entropy_monotone_along` (**proved**): `S` is monotone along any trajectory.
   * For the velocity tether, the entropy production equals `−TetherKernelVel κ ω S S ≥ 0`
     (`velocityTether_entropy_production`). This is conditional on the same two `Prop`s as
     in item 2.
4. **Global smooth existence within the model.**
   * `model_global_regularity` gives smoothness for all `t ≥ 0` together with the uniform
     ceiling. It is conditional on `TetheredMaxRate` and `ModelContinuation`.
   * `model_global_regularity_of_realization` derives the rate from the may-form maximizer
     `Prop`s, with effective damping `κ/2 − C_abs > 0`. The algebra step, `maxpoint_rate`,
     is **proved**.
5. **Separation from Navier–Stokes.** `kappa_zero_no_ceiling` (**proved**): at `κ = 0`, the
   inequality `M' ≤ M²` is satisfied by `1/(1−t)`, which is unbounded on `[0,1)`. So the
   ceiling comes from the `κ M³` term alone.

6. **Concrete instance (unconditional).** `MetriplecticWorldModel/Instance.lean`: the scalar
   toy instance `C = 0`, `κ > 0`, `M t = y₀ e^{-t}` with `κ y₀² ≤ 1`. It **proves**
   `instance_maxPointRealization`, `instance_tetheredMaxRate` and `instance_modelContinuation`,
   so `instance_global_regularity` (global smoothness plus the uniform ceiling) holds with no
   open hypothesis. It is a one-dimensional ODE instance, not a Galerkin truncation of
   Navier–Stokes; it shows the model hypotheses are jointly satisfiable.
   `stretchingCZ_sat_and_nontrivial` and `entropyCasimir_zero_bracket` are satisfiability
   examples.

7. **The two-part split and canonicity of the metric bracket (closed and proven unconditionally).**
   `MetriplecticWorldModel/Canonical.lean`, no named `Prop`s:
   * `split_exists_unique` (**proved**): every bilinear bracket is uniquely an antisymmetric
     (Lie–Poisson, 2-form) part plus a symmetric (metric/tether) part.
   * `canonical_metric_bracket` (**proved**, non-circular): on a real inner product space, a
     bilinear form that is symmetric (C1), degenerate in the direction `u` (C2: `B u · = 0`),
     and invariant under every linear isometry fixing `u` must equal `c ⟪Π_u x, Π_u y⟫`, with
     `Π_u` the projection off `span {u}`. The hypotheses do not mention `Π_u` or the diagonal
     of `B`, unlike the older `SaturatesTetherQuadratic`-based uniqueness, which assumed its answer.
   * `canonical_metric_bracket_sign` (**proved**): with the tether sign (`B x x ≤ 0`), `c ≤ 0`.
   * `Pi_u_form_symm_degen` (**proved**): the forced form does satisfy C1 and C2.
   * Scope: this is a pointwise statement at one state. It does **not** force the `|ω|²`
     weight, the value of `κ`, or the C3 feedback condition; deriving those from C1–C3 is
     still open. The isometry-invariance hypothesis is an explicit theorem argument.

8. **What the maximizer `Prop`s carry, and an encoding obstruction (proved).**
   `MetriplecticWorldModel/Realization.lean`:
   * `realization_of_rate` (**proved**): if `M > 0`, `0 ≤ C_abs` and `TetheredMaxRate C κ M M'`
     hold, then `MaxPointRealization C κ C_abs M M'` holds. Together with
     `tetheredMaxRate_of_realization`, this shows the five may-form `Prop`s, stated on bare real
     `MaxPointData`, are bookkeeping for the rate inequality. Their real content needs the data
     tied to an actual vorticity field (the maximizer of `|ω|`, `ν ω·Δω`, and so on). That link is
     not formalized, so `EnergyIdentity`, `ViscousAtMax`, `TetherFeedback`, `CrossControlled`
     and `StretchingCZ` stay open as statements about a real field.
   * `not_streamFunctionRepresentative` (**proved**): at a non-differentiable `ω`, every field is
     a Gâteaux representative under the current encoding, so `StreamFunctionRepresentative ω` is
     false there. `KineticEnergyCurlIdentity` therefore cannot be proved for every `ω` as it is
     encoded. It needs the orbit restricted to smooth fields and uniqueness modulo gradients.

9. **Smooth orbits, the model PDE, the Arnold and viscous brackets, and log-loss stretching** (`SmoothOrbit.lean`, `AuditFixes.lean`).
   * `ModelVorticityPDE ν ω u T` is a *definition*: `∂ₜω + (u·∇)ω − (ω·∇)u = νΔω + T`, with `u = BiotSavart ω` and `div ω = 0`. No existence theorem is claimed for it.
   * `curl_grad_eq_zero` and `curl_add_grad` are **proved**.
   * `kineticEnergyCurlIdentity_of_modGrad` is **proved conditional** on the named `Prop` `StreamFunctionRepModGrad ω`. That `Prop` says the stream-function representative is unique modulo gradients on a smooth orbit. It replaces exact uniqueness, which is false at nonsmooth ω (item 8). The `Prop` itself is **false as stated**: `not_streamFunctionRepModGrad` (**proved**, `ChoiceFree.lean`) shows it fails for every ω. Representatives are only determined up to null sets, and a one-point change is not a continuous gradient. So `kineticEnergyCurlIdentity_of_modGrad` is vacuous. A correct version must be stated almost everywhere; that version (Helmholtz + Biot–Savart IBP) is **open**.
   * `EntropyCasimir` for the concrete choice-free Arnold bracket with `S` = helicity is now **proved** on the test class for any derivative assignment whose value on `S` is a `C¹` Gâteaux representative (`helicity_casimir_of_rep`, item 15). Under the choice-based `FunctionalDerivative` it is still not provable as stated (the chosen representative is not controlled).
   * **Choice-free Arnold bracket** (`ChoiceFree.lean`). `ArnoldBracketOf ω a b := ∫⟨ω, curl a × curl b⟩` takes the derivative fields as data, with no `Classical.choose`. `arnoldBracketOf_antisymm` is **proved**. `entropyCasimir_arnold` is **proved**: for any derivative assignment `D`, if `curl (D S) = c•ω` pointwise, then `S` is a Casimir of `F G ↦ ArnoldBracketOf ω (D F) (D G)`. Example: helicity, whose derivative is 2u, with curl u = ω. **Open:** that `D` is the true Gâteaux derivative (for helicity, Biot–Savart self-adjointness and curl(BiotSavart ω) = ω). Note that the ported `ClassicalBracket` has no curls, so it differs from Arnold's bracket in this convention.
   * `classicalBracket_antisymm` is **proved**: the Arnold bracket `ClassicalBracket` is antisymmetric, so it is a valid `P`. The public lemma `ClassicalBracket_antisymm` was **added** (additively) to the ported `ArnoldGeometric.lean`, because its integrand is module-private.
   * `ViscousBracket ν` is defined as `ν∫Σᵢ⟨∂ᵢ curl δF, ∂ᵢ curl δG⟩`. `viscousBracket_symm` and `viscousBracket_nonneg` are **proved**. It is symmetric and PSD, but it is **not** degenerate with respect to kinetic energy. So viscosity is not a metriplectic `G` in the strict sense.
   * **Relabel:** every result that uses `StretchingCZ` rests on a hypothesis **known false as a pure L∞ bound** for Navier–Stokes, because the known bound has a log loss. `StretchingLogLoss d C₁ C₂` (`St ≤ C₁y³ + C₂y³log(1+y)`) is the honest alternative. Under it, `maxpoint_rate_logLoss` (**proved**) gives `y' ≤ (C₁+κ/4+4C₂²/κ)y² − (κ/4−Cabs)y³`. The tether still dominates when `κ > 4·Cabs`.
   * **R³ vs T³:** the type named `T3` (original name kept) is actually ℝ³ (`EuclideanSpace ℝ (Fin 3)`), not the torus. No port to the torus was done.

## Open named `Prop`s

Open beyond these: deriving the `|ω|²` weight, `κ`, and C3 from C1–C3 (full gauge-uniqueness of `TetherKernelVel`).


Each one is passed as an explicit argument. None is proved here.

* `TetheredMaxRate C κ M M'`: `M` is differentiable and satisfies `M' ≤ C M² − κ M³` for `t ≥ 0`.
* `MaxPointRealization C κ Cabs M M'`: for every `t ≥ 0`, there is maximizer data satisfying
  the five may-form `Prop`s: `EnergyIdentity`, `StretchingCZ`, `ViscousAtMax`,
  `TetherFeedback` and `CrossControlled`.
  * `StretchingCZ` is a pure `y³` bound. It is a hypothesis on the model's maximizer data only. As an `L∞` estimate
    for unmodified Navier–Stokes it is not known (the true bound has a log loss), and nothing here
    claims it for Navier–Stokes. In the concrete instance it holds by the model closure `St = C y³`.
  * `TetherFeedback` holds only in the tethered model.
* `ModelContinuation Smooth M`: a continuation criterion of Beale–Kato–Majda type for the model.
* `EntropyCasimir P S`: the entropy is a Casimir of `P`. For the concrete bracket see `ArnoldCasimirField` (item 17; proved for helicity). The choice-based instance `EntropyCasimirChoice` is not provable as stated.
* `MaxPointRealization` is discharged from an actual field in item 17, except `FieldStretchingBound` and `FieldTetherFeedback`. Differentiability of `sup|ω|` is not needed for the ceiling (item 18), and `FieldTetherFeedback` is proved for `cubicTether`.
* `KineticEnergyCurlIdentity ω` (ported): `curl(δH/δω) = u`.

10. **Biot–Savart and Helmholtz in the current encoding** (`HelmholtzObstruction.lean`).
   * `not_curl_biotSavart_eq` is **proved**: `curl (BiotSavart ω) = ω` fails for some `CoadjointOrbit`. The witness is `pointSpike`: `e₀` at the origin, `0` elsewhere. It is admitted because `div` uses `fderiv`, which is `0` where the field is not differentiable. Its Biot–Savart velocity is `0`, since the integrand vanishes almost everywhere, but the field is nonzero at the origin.
   * So the identity, the helicity derivative `2u`, and Helmholtz uniqueness (smooth or a.e.) can only hold on a restricted class of orbits, for example smooth and compactly supported ω and variations.
   * `CurlBiotSavartOn S` names that restricted identity. `helicity_casimir_of_curlBiotSavart` is **proved conditional** on it: helicity is a Casimir of `ArnoldBracketOf` at ω in `S` when `D S = u`. The factor 2 does not affect the Casimir property.
   * `CurlBiotSavartOn` for smooth compactly supported divergence-free ω is now **proved** (`curlBiotSavartTest`, item 14), via a Newton potential built in this repo. **Still open:** that `D S = 2u` is the true Gâteaux derivative of helicity, which needs Biot–Savart self-adjointness (a Fubini argument with a singular kernel). Also open: the restricted Helmholtz uniqueness (de Rham / Poincaré lemma plus the fundamental lemma for div-free test fields). The class of variations ε in `IsGateauxRepresentative` would also have to be restricted.

11. **The restricted class and the first Newton-potential piece** (`TestClass.lean`).
   * `IsTestOrbit ω`: smooth (`C^∞`), compactly supported and divergence-free. `not_isTestOrbit_pointSpike` is **proved**: the counterexample from item 10 is excluded. (Until item 15 the smoothness was mis-encoded as analytic; see the definition fix there.)
   * `IsGateauxRepOn` is the Gâteaux condition, tested only on variations in the class.
   * Restated named `Prop`s (`StreamFunctionRepModGradOn` was open here and is **proved** in item 16; `CurlBiotSavartTest` was open here and is proved in item 14):
     * `StreamFunctionRepModGradOn ω hω`: `C²` representatives are unique modulo `C²` gradients, with `curl ψ = u`.
     * `CurlBiotSavartTest := CurlBiotSavartOn IsTestOrbit` (now **proved**, item 14).
   * `helicity_casimir_test` is **proved conditional** on `CurlBiotSavartTest`.
   * `integrableOn_ball_norm_rpow_neg` is **proved**: for `s < 3`, `‖x‖^(-s)` is integrable on every ball of ℝ³. So the Newton kernel `1/(4π|x|)` and the Biot–Savart kernel magnitude `|x|⁻²` are locally integrable. This is the first step toward the Newton potential.
   * **Steps toward `CurlBiotSavartTest`** (all five now done, see items 12–14; `CurlBiotSavartTest` is **proved** in item 14):
     1. `1/|x|` is smooth and harmonic away from 0.
     2. Differentiate the convolution `N * ω` under the integral sign, for compactly supported smooth ω.
     3. `Δ(N * ω) = −4π ω` (done by a regularized-kernel route, item 13, not via spheres).
     4. `curl curl = ∇div − Δ`, together with `div ω = 0`.
     5. Identify `curl(N * ω)` with the repo's `BiotSavart`.

12. **Newton-potential steps 1 and 2** (`NewtonKernel.lean`). All **proved**, no sorry:
   * `scalarLaplacian_newtonRadial`: with `newtonRadial y = (‖y‖²)^(-1/2) = 1/|y|`, the sum of second partials `Σᵢ ∂ᵢ∂ᵢ (1/|y|) = 0` for every `y ≠ 0`. `contDiffAt_newtonRadial` proves it is `C^∞` there. This is **step 1**.
   * `contDiff_newtonPotential` and `hasFDerivAt_newtonPotential`: for a smooth, compactly supported scalar `g`, `newtonRadial ⋆ g` is `C^∞`, and its derivative is `newtonRadial ⋆ Dg` (differentiation under the integral). This is **step 2**. It applies componentwise to ω and uses `locallyIntegrable_newtonRadial`.
   * **Step 3, partial progress** (`RegularizedKernel.lean`, all **proved**). This uses a regularized kernel and avoids sphere surface integrals:
     * `scalarLaplacian_regNewton`: with `N_ε(y) = (‖y‖²+ε²)^(-1/2)`, `Δ N_ε = −3ε²(‖y‖²+ε²)^(-5/2)` everywhere.
     * `regNewton_le` and `tendsto_regNewton`: `0 ≤ N_ε ≤ N` (for `y ≠ 0`), and `N_ε → N` pointwise off the origin.
     * `integral_neg_scalarLaplacian_regNewton`: `∫_{ℝ³} −Δ N_ε = 4π`. This uses polar decomposition plus the 1D identity `integral_regRadial`.
     * `tendsto_regPeak_approxIdentity`: `−Δ N_ε/(4π)` is an approximate identity (Mathlib's peak-function theorem).
   * Step 3 was completed in item 13.

13. **Newton-potential step 3 closed** (`NewtonLaplacian.lean`). All **proved**, no sorry, no hypotheses beyond `g ∈ C²` with compact support:
   * `integral_mul_scalarLaplacian_eq`: `∫ K Δg = ∫ (ΔK) g` for `K ∈ C²` and `g ∈ C²_c` (two Mathlib integrations by parts per coordinate; no boundary terms).
   * (a) `regNewton_conv_laplacian`: `∫ N_ε(t) Δg(x−t) dt = ∫ (ΔN_ε)(y−x) g(y) dy`.
   * (b) `tendsto_regNewton_conv`: `∫ N_ε(t) h(x−t) dt → ∫ N(t) h(x−t) dt` as `ε → 0` (dominated by `N·|h|`).
   * (c) `scalarLaplacian_newtonPotential`: `Δ(N ⋆ g)(x) = ∫ N(t) Δg(x−t) dt` (step 2 unpacked coordinatewise via `convolution_precompR_apply`).
   * `scalarLaplacian_newtonPotential_eq`: **`Δ(N ⋆ g) = −4π g` pointwise**, with `N = 1/|y|`. Assembled from (a)–(c), `regPeak_scale` and the approximate identity.
   * Steps 4 and 5 were completed in item 14.

14. **Steps 4–5 closed; `CurlBiotSavartTest` proved** (`BiotSavartNewton.lean`). All **proved**, no sorry, no hypotheses:
   * `newtonPotential_deriv_eq`: for `h ∈ C¹_c`, `N ⋆ ∂ⱼh = −∫ (tⱼ/|t|³) h(x−t) dt`. The singular integration by parts is done with the regularized kernel (`regNewton_conv_deriv`, `gradKer`) and the limit `ε → 0` on both sides (`tendsto_regNewton_conv`, `tendsto_gradKer_conv`, dominated by `|t|⁻²|h|`).
   * `biotSavart_eq_curl_newtonVec` (**step 5**): on the test class, the repo's `BiotSavart ω = (4π)⁻¹ curl (N ⋆ ω)` pointwise (`newtonVec` = componentwise Newton potential).
   * `curl_curl_newtonVec` (**step 4**): `curl curl (N ⋆ ω) = 4π ω`, from symmetry of second derivatives (`fderiv_fderiv_swap`), `div (N ⋆ ω) = N ⋆ div ω = 0` and `Δ(N ⋆ ωₖ) = −4π ωₖ` (item 13).
   * `curlBiotSavartTest : CurlBiotSavartTest` — **proved**. Hence `helicity_casimir_test_closed`: the helicity Casimir statement on the test class with no `CurlBiotSavartTest` hypothesis. It takes `D S = u` as an explicit argument; item 15 removes that hypothesis.

15. **Helicity: self-adjointness, Gâteaux derivative `2u`, Casimir with no `D S` value hypothesis** (`HelicityGateaux.lean`). All **proved**, no sorry:
   * **Definition fix (`IsSmoothOrbit`).** It previously read `ContDiff ℝ ⊤`, which in current Mathlib is `ω`-smoothness (analytic), so a compactly supported test orbit was forced to be `0` and the test-class results of items 11–14 were vacuous. It now reads `ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)` (`C^∞`); every earlier proof rebuilt with one one-line edit. The class is non-trivial: `curlOrbit` / `isTestOrbit_curlOrbit` build test orbits `curl ψ` from any `C^∞_c` field `ψ`.
   * `biotSavart_selfAdjoint`: `∫⟨B a, b⟩ = ∫⟨B b, a⟩` for continuous compactly supported `a, b` (Fubini on `|x−y|⁻²|a(y)||b(x)|`, `integrable_prod_rpow_neg_two`, kernel symmetry, triple product `inner_cross_eq`).
   * `helicity ω := ∫⟨B ω, ω⟩`; `helicity_line` (exact quadratic along `ω + tε`) and `helicity_gateaux : IsGateauxRepOn helicity ω hω (2 • B ω)`.
   * `curl_eq_of_isGateauxRepOn`: two `C¹` Gâteaux representatives of the *same* functional on the test class have equal curl (test fields `curl(χ eₖ)`, `integral_pairing_curl_single`, fundamental lemma, continuity).
   * `curl_eq_two_of_helicity_rep`, `helicity_casimir_of_rep`: if `D S` is any `C¹` Gâteaux representative of helicity then `curl (D S) = 2ω` and `S` is a Casimir of `F G ↦ ArnoldBracketOf ω (D F) (D G)`; `helicity_casimir_canonical` for `D S = 2u`. No `D S = u` hypothesis.
   * **(2) partial.** `kineticEnergy_reps_curl_eq`: `C¹` kinetic-energy representatives have equal curl (the curl half of Helmholtz uniqueness). `streamFunctionRepModGradOn_of_exists`: `StreamFunctionRepModGradOn` follows from one `C²` stream-function representative plus the named `Prop` `CurlFreeIsGradient` (Poincaré lemma on `ℝ³`). Both remaining inputs are now **proved** in item 16.
   * **(3).** For the concrete Arnold bracket, `EntropyCasimir` is proved for helicity as above. For the choice-based `FunctionalDerivative` bracket it remains not provable as stated.

16. **Poincaré lemma and the kinetic-energy representative; `StreamFunctionRepModGradOn` closed** (`PoincareR3.lean`, `KineticEnergyRep.lean`). All **proved**, no sorry:
   * `curlFreeIsGradient : CurlFreeIsGradient`: a `C²` curl-free field on `ℝ³` is `grad φ` with `φ ∈ C²` (Mathlib's Poincaré lemma for closed 1-forms on convex sets, applied to `x ↦ ⟪v x, ·⟫`; symmetry of the derivative from `curl v = 0`).
   * `decays_newtonPotential`: if `g` is continuous, compactly supported and `∫ g = 0`, then `|N ⋆ g (x)| ≤ C (1 + |x|)⁻²`. Mean-zero inputs: `integral_fderiv_eq_zero` (derivatives of `C¹_c` functions) and `IsTestOrbit.integral_coord_eq_zero` (each coordinate of a divergence-free test field, via `ω_k = Σ_j ∂_j(x_k ω_j)`).
   * `DGood` (differentiable, decaying, decaying first derivatives) holds for the coordinates of `B ω` (`dGood_biotSavart`) and of `ψ := keStream ω = (4π)⁻¹ N ⋆ ω` (`dGood_keStream`). In particular `B ω ∈ L²`, so the kinetic energy is a genuine finite integral on the test class.
   * `integral_pairing_curl_symm`: `∫ ⟪a, curl b⟫ = ∫ ⟪curl a, b⟫` for `DGood` fields (six integrations by parts). Hence `integral_inner_biotSavart_eq`: `∫ ⟪B ω, B ε⟫ = ∫ ⟪ψ, ε⟫`.
   * `kineticEnergy_line`, `keStream_isGateauxRep : IsGateauxRepOn KineticEnergyHamiltonian ω hω (keStream ω)`, `contDiff_keStream` (`C^∞`, so `C²`), `curl_keStream : curl ψ = u`.
   * **`streamFunctionRepModGradOn : ∀ ω hω, StreamFunctionRepModGradOn ω hω`**, unconditionally on the test class.
   * **Smoothness audit.** Grepping the whole repo for `ContDiff… ℝ ⊤` (which in current Mathlib means analytic) found two more uses. `Instance.lean` `instSmooth` said `C^∞` in its docstring but stated analyticity. That claim was stronger but still true. It is now stated as `C^∞`. `contDiffAt_newtonRadial` (`NewtonKernel.lean`) states analyticity of `1/|x|` away from 0. This is a true, stronger claim, proved, and only used through its `C^∞` consequence; it is left as is and documented here. Every other occurrence already uses `((⊤ : ℕ∞) : WithTop ℕ∞)`.

17. **Maximizer data from an actual vorticity field; `EntropyCasimir` for the concrete bracket** (`MaxPointDanskin.lean`, `EntropyCasimirArnold.lean`). All **proved**, no sorry:
   * `danskin_upper_dini`: Danskin-type envelope bound. If `f` and `∂ₜf` are jointly continuous on `ℝ × K` with `K` compact, there is a maximizer `x⋆` of `f t` on `K` such that `sup_K f(t+h) ≤ f(t,x⋆) + h(∂ₜf(t,x⋆) + ε)` for small `h > 0`. So the upper right Dini derivative of `t ↦ sup_K f t` is at most `∂ₜf(t,x⋆)`. `vorticity_danskin_upper_dini` applies this to `|ω(t)|²` when `ω` has a fixed compact support.
   * `hasDerivAt_eq_of_touch_below`, `sup_mul_deriv_eq_inner`: if `Y = sup|ω|` is differentiable at `t`, then `Y Y' = ω·∂ₜω` at **every** global maximizer.
   * `inner_convective_eq_zero_of_max`: advection drops out at the maximum (`ω·(v·∇)ω = 0`). `deriv2_nonpos_of_isLocalMax` (a 1D second-derivative test) and `inner_laplacian_nonpos_of_max` give the maximum principle `ω·Δω ≤ 0` at a global max of `|ω|²` for `C²` fields.
   * `maxPointRealization_of_field`: `MaxPointRealization C κ C_abs Y Y'` for a solution of `ModelVorticityPDE ν` (`ν ≥ 0`), where `ω(t)` is `C²` and compactly supported, `ω` is `C¹` in time, and `Y = sup|ω| > 0`. The data come from the field at a maximizer (`fieldMaxPointData`: `St = ω·(ω·∇)u`, `V = ν ω·Δω`, `tetherTerm = ω·Tterm`, `b = 0`). `EnergyIdentity`, `ViscousAtMax`, `CrossControlled` (for `C_abs ≥ 0`) and the links for `y` and `y'` are discharged.
   * **Still assumed** (named `Prop`s / hypotheses): `FieldStretchingBound` (the field-level `StretchingCZ`, which has the log-loss caveat of item 9 and is not known for Navier–Stokes) and `FieldTetherFeedback` (`ω·Tterm = −κY⁴` at the max, model-specific). `maxPointRealization_of_field` also assumes that `Y` is differentiable; item 18 removes that assumption for the ceiling. The field regularity (`C²`, compact support, `C¹` in time) is also assumed and not proved for any solution.
   * `ArnoldCasimirField ω s := ∀ a, ArnoldBracketOf ω a s = 0` is the clean restatement of `EntropyCasimir` for the concrete bracket. It uses no derivative assignment and no choice. `entropyCasimir_of_arnoldCasimirField` gives the generic form, and `arnoldCasimirField_helicity` proves helicity's `2u` is a Casimir field on the test class with no hypotheses.
   * `EntropyCasimirChoice ω S` (the choice-based `ClassicalBracket` form) is **kept and marked NOT PROVABLE as stated**: `FunctionalDerivative` is an unconstrained `Classical.choose`.

18. **The ceiling from the upper Dini bound alone; a concrete tether** (`DiniCeiling.lean`). All **proved**, no sorry:
   * `ceiling_of_upper_dini`: a function `M`, continuous on `[0,∞)`, with `M(t+h) ≤ M t + h(R t + ε)` for small `h > 0`, and with `R t < 0` whenever `M t > B`, stays `≤ B` if `M 0 ≤ B`. This is a Dini comparison lemma built on Mathlib's `image_le_of_liminf_slope_right_lt_deriv_boundary'`.
   * `sup_eq_sSup_image`, `sup_continuous_of_uniform_support`: `Y = sup|ω|` is continuous when `ω` is jointly continuous and every `ω(t)` is supported in one compact `K`.
   * `field_uniform_ceiling`: take a `ModelVorticityPDE` solution with `ν ≥ 0` and `κ > 0`. Assume `C²` in space, `C¹` in time (jointly continuous `ω` and `∂ₜω`), support in a fixed compact `K`, and `FieldStretchingBound` and `FieldTetherFeedback`. Then `sup|ω(t)| ≤ ceiling (sup|ω(0)|) C κ` for all `t ≥ 0`. **No differentiability or positivity of `Y` is assumed.** It is applied to `Y²` with the Danskin bound.
   * `cubicTether κ ω := −κ|ω|²ω`, `fieldTetherFeedback_cubicTether`: for this concrete tether, `FieldTetherFeedback` is a theorem. `field_uniform_ceiling_cubicTether` leaves only `FieldStretchingBound`. For a general `Tterm`, `FieldTetherFeedback` does **not** follow: `ModelVorticityPDE` leaves `Tterm` free, and the Prop fails for `Tterm = 0`.
   * **Still assumed:** `FieldStretchingBound`; the existence and regularity of solutions, including the uniform compact support, which real Navier–Stokes solutions do not have in general. This is a statement about the model, not Navier–Stokes.

19. **Log-loss stretching with the cubic tether: a reduction, not the CZ estimate** (`LogLossCeiling.lean`). All **proved**, no sorry:
   * `FieldNetRate`: a named Prop. At every maximizer, `ω·(ω·∇)u + ω·Tterm ≤ C Y³ − κ Y⁴`.
   * `field_uniform_ceiling_of_netRate`: the Dini ceiling of item 18 under `FieldNetRate` alone.
   * `FieldStretchingLogLoss`: a named Prop, **not proved**. At every maximizer, `ω·(ω·∇)u ≤ C₁Y³ + C₂Y³ log(1+Y)`.
   * `fieldNetRate_of_logLoss_cubicTether`: log loss plus `cubicTether` gives `FieldNetRate` with `C = C₁ + κ/4 + 4C₂²/κ` and `κ_eff = 3κ/4`.
   * `field_uniform_ceiling_logLoss_cubicTether`: hence `sup|ω(t)| ≤ ceiling` for every `κ > 0` and `C₂ ≥ 0`. No `κ > 4 C_abs` gap is needed, because the cross amplitude is `0` at the field level.
   * **Honest status: the ceiling is NOT unconditional, on the test class or anywhere.** The Calderón–Zygmund/Beale–Kato–Majda log-loss estimate is **not formalized**: no singular-integral, Hölder or Sobolev theory for `∇BiotSavart` exists in this repo.
   * Even when proved, the known estimate has the form `|∇u|∞ ≤ C(1 + Y(1 + log⁺(‖ω‖_{C^α}/Y)) + ‖ω‖_{L²})`, with a higher norm inside the log. A time-uniform bound on `‖ω(t)‖_{C^α}` is not available from the ceiling argument, and it is essentially the regularity question itself. So that form does not close the ceiling; the `Y`-only `FieldStretchingLogLoss` is a strictly stronger hypothesis than anything known.
   * **Remaining hypotheses** of `field_uniform_ceiling_logLoss_cubicTether`:
     * `FieldStretchingLogLoss`;
     * `ModelVorticityPDE` with `cubicTether`;
     * `C²` in space for every `t`;
     * joint continuity of `ω` and `∂ₜω`, with the pointwise time derivative;
     * support in one fixed compact `K` for all `t`;
     * `Y = sup|ω|` as an `IsLUB`;
     * `ν ≥ 0`, `κ > 0`, `C₂ ≥ 0`.

## Coined names

**Author's name:** `Pi_u` is Benjamin Frohman's own May 31 name (`Tether_May31.lean.txt:43`). In this repo it is the orthogonal projection `x − (⟪u,x⟫/‖u‖²)•u`. Lemmas derived from it (e.g. `Pi_u_form_symm_degen`) carry the name.

**Coined in this build (not the author's names):** `split_exists_unique`, `canonical_metric_bracket`, `canonical_metric_bracket_sign`, `Pi_u_form_symm_degen` (name derived from `Pi_u`), `realization_of_rate`, `gateaux_rep_of_not_differentiable`, `not_streamFunctionRepresentative`, `IsSmoothOrbit`, `grad`, `curl_grad_eq_zero`, `curl_add_grad`, `StreamFunctionRepModGrad`, `kineticEnergyCurlIdentity_of_modGrad`, `ModelVorticityPDE`, `StretchingLogLoss`, `maxpoint_rate_logLoss`, `classicalBracket_antisymm`, `ClassicalBracket_antisymm`, `ViscousBracket`, `viscousBracket_symm`, `viscousBracket_nonneg`, `not_streamFunctionRepModGrad`, `ArnoldBracketOf`, `arnoldBracketOf_antisymm`, `arnoldBracketOf_eq_zero_of_curl_parallel`, `entropyCasimir_arnold`, `spike`, `fderiv_spike`, `pointSpike`, `pointSpike_val_zero`, `velocity_pointSpike`, `not_curl_biotSavart_eq`, `CurlBiotSavartOn`, `helicity_casimir_of_curlBiotSavart`, `IsTestOrbit`, `not_isTestOrbit_pointSpike`, `IsGateauxRepOn`, `StreamFunctionRepModGradOn`, `CurlBiotSavartTest`, `helicity_casimir_test`, `integrableOn_ball_norm_rpow_neg`, `newtonRadial`, `scalarLaplacian`, `contDiffAt_newtonRadial`, `inner_single_one`, `hasFDerivAt_normSq_rpow`, `normSq_rpow_partial`, `fderiv_newtonRadial_single`, `scalarLaplacian_newtonRadial`, `newtonRadial_eq`, `locallyIntegrable_newtonRadial`, `newtonPotential`, `contDiff_newtonPotential`, `hasFDerivAt_newtonPotential`, `regNewton`, `hasFDerivAt_regSq_rpow`, `regSq_rpow_partial`, `scalarLaplacian_regNewton`, `regNewton_nonneg`, `regNewton_le`, `tendsto_regNewton`, `hasDerivAt_regRadialPrimitive`, `tendsto_regRadialPrimitive`, `integral_regRadial`, `integral_neg_scalarLaplacian_regNewton`, `regPeak`, `regPeak_nonneg`, `integral_regPeak`, `tendsto_regPeak_decay`, `tendsto_regPeak_approxIdentity`, `integral_mul_dd_eq`, `integral_mul_scalarLaplacian_eq`, `scalarLaplacian_comp_sub`, `contDiff_regNewton`, `regNewton_neg`, `regNewton_conv_laplacian`, `regPeak_scale`, `ae_ne_zero_T3`, `integrable_newtonRadial_mul`, `tendsto_regNewton_conv`, `newtonPotential_apply`, `fderiv_newtonPotential_apply`, `scalarLaplacian_newtonPotential`, `scalarLaplacian_newtonPotential_eq`, `gradKer`, `gradKer_bound`, `locallyIntegrable_norm_rpow_neg_two`, `integrable_rpow_neg_two_mul`, `tendsto_gradKer_conv`, `regNewton_conv_deriv`, `newtonPotential_deriv_eq`, `newtonVec`, `newtonVec_coord`, `directionalCoord_newtonVec`, `integrable_gradKer_mul`, `gradKer_zero_eq`, `biotSavart_eq_curl_newtonVec`, `fderiv_fderiv_swap`, `curl_curl_newtonVec`, `curlBiotSavartTest`, `helicity_casimir_test_closed`, `biotSavartKernel_eq`, `continuous_cross`, `inner_cross_eq`, `norm_cross_le`, `measurable_rpow_neg_two_sub`, `integrable_rpow_neg_two_sub`, `continuous_conv_rpow_neg_two`, `integrable_prod_rpow_neg_two`, `norm_kernel_smul_cross_le`, `measurable_biotSavartKernel`, `kernel_symm`, `integrable_biotSavart_density`, `bsPairDensity`, `integrable_bsPairDensity`, `bsPairDensity_swap`, `inner_biotSavart_eq_integral`, `biotSavart_selfAdjoint`, `integrable_inner_biotSavart`, `IsTestOrbit.continuous`, `helicity`, `helicity_line`, `helicity_gateaux`, `hasCompactSupport_fderiv_apply`, `continuous_fderiv_apply`, `integral_mul_fderiv_test`, `integral_ibp_two`, `coord_smul_single`, `integral_pairing_curl_single_0`, `integral_pairing_curl_single_1`, `integral_pairing_curl_single_2`, `integral_pairing_curl_single`, `contDiff_directionalCoord`, `contDiff_curl_coord`, `hasCompactSupport_curl`, `curlOrbit`, `isTestOrbit_curlOrbit`, `continuous_curl_of_C1`, `curl_eq_of_isGateauxRepOn`, `contDiff_biotSavart_coord`, `curl_eq_two_of_helicity_rep`, `helicity_casimir_of_rep`, `helicity_casimir_canonical`, `kineticEnergy_reps_curl_eq`, `CurlFreeIsGradient`, `streamFunctionRepModGradOn_of_exists`, `eq_sum_single`, `curlFreeIsGradient`, `Decays`, `Decays.sub`, `Decays.const_mul`, `Decays.integrable_mul`, `abs_inv_norm_sub_le`, `newtonRadial_eq_inv`, `continuous_newtonPotential`, `newtonPotential_eq_swap`, `decays_newtonPotential`, `integral_fderiv_eq_zero`, `IsTestOrbit.coord_contDiff`, `IsTestOrbit.coord_compact`, `IsTestOrbit.integral_coord_eq_zero`, `DGood`, `dGood_newtonPotential`, `DGood.sub`, `DGood.const_mul`, `DGood.congr`, `dGood_newtonVec`, `dGood_directionalCoord_newtonVec`, `DGood.ibp`, `integral_lin6`, `integral_pairing_curl_symm`, `dGood_biotSavart`, `keStream`, `keStream_coord`, `dGood_keStream`, `contDiff_keStream`, `curl_keStream`, `pairing_eq_sum`, `integrable_pairing_of_dGood`, `integral_inner_biotSavart_eq`, `kineticEnergy_line`, `keStream_isGateauxRep`, `streamFunctionRepModGradOn`, `hasDerivAt_eq_of_touch_below`, `eventually_forall_abs_sub_lt`, `danskin_upper_dini`, `deriv2_nonpos_of_isLocalMax`, `hasDerivAt_line`, `inner_fderiv_eq_zero_of_max`, `inner_convective_eq_zero_of_max`, `inner_second_deriv_nonpos_of_max`, `inner_laplacian_nonpos_of_max`, `vorticity_danskin_upper_dini`, `sup_mul_deriv_eq_inner`, `FieldStretchingBound`, `FieldTetherFeedback`, `fieldMaxPointData`, `maxPointRealization_of_field`, `ArnoldCasimirField`, `EntropyCasimirChoice`, `entropyCasimir_of_arnoldCasimirField`, `arnoldCasimirField_of_curl_parallel`, `arnoldCasimirField_helicity`, `ceiling_of_upper_dini`, `sup_eq_sSup_image`, `sup_continuous_of_uniform_support`, `field_uniform_ceiling`, `cubicTether`, `fieldTetherFeedback_cubicTether`, `field_uniform_ceiling_cubicTether`, `FieldNetRate`, `field_uniform_ceiling_of_netRate`, `FieldStretchingLogLoss`, `fieldNetRate_of_logLoss_cubicTether`, `field_uniform_ceiling_logLoss_cubicTether`.

## Ported libraries

These are copied verbatim, keeping only the modules needed for the build.

* `FrohmanianSymplecticTether/` comes from frohmanian-symplectic-tether-regularity at
  `e937414` (the `VelocityTether` import closure). It provides symmetry, sign, C1, C3, the
  feedback bound and C2. These are re-exported in `ported_velocityTether_facts`.
* `TetherMayForm/` comes from may-form at `9001b76` (the `Enstrophy` import closure). It
  provides `MaxPointData` and the maximizer `Prop`s.
* `ceiling_upper` extends `Lyapunov.ode_upper` from weighted-enstrophy-identities from the
  equation `y' = y²(C − κy)` to the corresponding inequality.

## Verification

```
lake build                       # 0 sorry
lake env lean AxiomAudit.lean    # 765 theorems, only propext / Classical.choice / Quot.sound
```

A draft companion paper is in `paper/` (marked DRAFT; it tracks the build in progress).

License: Apache-2.0.

## Copyright, license and scope

Copyright 2026 Benjamin Stanley Frohman (ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)). Licensed under the Apache License, Version 2.0; see `LICENSE` and `NOTICE`.

What is proved vs. conditional: Proved results and the open named `Prop`s are listed above. This is a modified model, not unmodified Navier–Stokes. Every hypothesis is a named `Prop` passed as an explicit argument. Nothing in this repository claims to solve the Clay Millennium problem or global regularity for unmodified 3D Navier–Stokes.
