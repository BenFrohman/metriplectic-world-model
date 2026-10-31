# Metriplectic World Model

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
   * `EntropyCasimir` for the concrete Arnold bracket is **open**. Under the choice-based `FunctionalDerivative` it cannot be proved as stated.
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
* `EntropyCasimir P S`: the entropy is a Casimir of `P`.
* `KineticEnergyCurlIdentity ω` (ported): `curl(δH/δω) = u`.

10. **Biot–Savart and Helmholtz in the current encoding** (`HelmholtzObstruction.lean`).
   * `not_curl_biotSavart_eq` is **proved**: `curl (BiotSavart ω) = ω` fails for some `CoadjointOrbit`. The witness is `pointSpike`: `e₀` at the origin, `0` elsewhere. It is admitted because `div` uses `fderiv`, which is `0` where the field is not differentiable. Its Biot–Savart velocity is `0`, since the integrand vanishes almost everywhere, but the field is nonzero at the origin.
   * So the identity, the helicity derivative `2u`, and Helmholtz uniqueness (smooth or a.e.) can only hold on a restricted class of orbits, for example smooth and compactly supported ω and variations.
   * `CurlBiotSavartOn S` names that restricted identity. `helicity_casimir_of_curlBiotSavart` is **proved conditional** on it: helicity is a Casimir of `ArnoldBracketOf` at ω in `S` when `D S = u`. The factor 2 does not affect the Casimir property.
   * **Open:** `CurlBiotSavartOn` for smooth compactly supported ω. It needs the Newton potential, `Δ(1/|x|) = −4πδ`, which Mathlib does not have. Also open: that `D S = 2u` is the true Gâteaux derivative of helicity, which needs Biot–Savart self-adjointness (a Fubini argument with a singular kernel). Also open: the restricted Helmholtz uniqueness (de Rham / Poincaré lemma plus the fundamental lemma for div-free test fields). The class of variations ε in `IsGateauxRepresentative` would also have to be restricted.

11. **The restricted class and the first Newton-potential piece** (`TestClass.lean`).
   * `IsTestOrbit ω`: smooth (`C^∞`), compactly supported and divergence-free. `not_isTestOrbit_pointSpike` is **proved**: the counterexample from item 10 is excluded.
   * `IsGateauxRepOn` is the Gâteaux condition, tested only on variations in the class.
   * Restated named `Prop`s, both **open**:
     * `StreamFunctionRepModGradOn ω hω`: `C²` representatives are unique modulo `C²` gradients, with `curl ψ = u`.
     * `CurlBiotSavartTest := CurlBiotSavartOn IsTestOrbit`.
   * `helicity_casimir_test` is **proved conditional** on `CurlBiotSavartTest`.
   * `integrableOn_ball_norm_rpow_neg` is **proved**: for `s < 3`, `‖x‖^(-s)` is integrable on every ball of ℝ³. So the Newton kernel `1/(4π|x|)` and the Biot–Savart kernel magnitude `|x|⁻²` are locally integrable. This is the first step toward the Newton potential.
   * **Remaining steps toward `CurlBiotSavartTest`** (steps 1–2 now done, see item 12; 3–5 open):
     1. `1/|x|` is smooth and harmonic away from 0.
     2. Differentiate the convolution `N * ω` under the integral sign, for compactly supported smooth ω.
     3. Green's identity on `ℝ³ \ B_ε` with `ε → 0`, giving `Δ(N * ω) = ω`.
     4. `curl curl = ∇div − Δ`, together with `div ω = 0`.
     5. Identify `curl(N * ω)` with the repo's `BiotSavart`.

12. **Newton-potential steps 1 and 2** (`NewtonKernel.lean`). All **proved**, no sorry:
   * `scalarLaplacian_newtonRadial`: with `newtonRadial y = (‖y‖²)^(-1/2) = 1/|y|`, the sum of second partials `Σᵢ ∂ᵢ∂ᵢ (1/|y|) = 0` for every `y ≠ 0`. `contDiffAt_newtonRadial` proves it is `C^∞` there. This is **step 1**.
   * `contDiff_newtonPotential` and `hasFDerivAt_newtonPotential`: for a smooth, compactly supported scalar `g`, `newtonRadial ⋆ g` is `C^∞`, and its derivative is `newtonRadial ⋆ Dg` (differentiation under the integral). This is **step 2**. It applies componentwise to ω and uses `locallyIntegrable_newtonRadial`.
   * **Still open:** step 3, `Δ(N ⋆ g) = −4π g`. Mathlib has the divergence theorem only on boxes, with no Green's identity on `ℝ³ \ B_ε` and no spherical surface integrals, so this needs substantial new infrastructure. Steps 4–5 are also open. `CurlBiotSavartTest` therefore remains a **hypothesis**.

## Coined names

**Author's name:** `Pi_u` is Benjamin Frohman's own May 31 name (`Tether_May31.lean.txt:43`). In this repo it is the orthogonal projection `x − (⟪u,x⟫/‖u‖²)•u`. Lemmas derived from it (e.g. `Pi_u_form_symm_degen`) carry the name.

**Coined in this build (not the author's names):** `split_exists_unique`, `canonical_metric_bracket`, `canonical_metric_bracket_sign`, `Pi_u_form_symm_degen` (name derived from `Pi_u`), `realization_of_rate`, `gateaux_rep_of_not_differentiable`, `not_streamFunctionRepresentative`, `IsSmoothOrbit`, `grad`, `curl_grad_eq_zero`, `curl_add_grad`, `StreamFunctionRepModGrad`, `kineticEnergyCurlIdentity_of_modGrad`, `ModelVorticityPDE`, `StretchingLogLoss`, `maxpoint_rate_logLoss`, `classicalBracket_antisymm`, `ClassicalBracket_antisymm`, `ViscousBracket`, `viscousBracket_symm`, `viscousBracket_nonneg`, `not_streamFunctionRepModGrad`, `ArnoldBracketOf`, `arnoldBracketOf_antisymm`, `arnoldBracketOf_eq_zero_of_curl_parallel`, `entropyCasimir_arnold`, `spike`, `fderiv_spike`, `pointSpike`, `pointSpike_val_zero`, `velocity_pointSpike`, `not_curl_biotSavart_eq`, `CurlBiotSavartOn`, `helicity_casimir_of_curlBiotSavart`, `IsTestOrbit`, `not_isTestOrbit_pointSpike`, `IsGateauxRepOn`, `StreamFunctionRepModGradOn`, `CurlBiotSavartTest`, `helicity_casimir_test`, `integrableOn_ball_norm_rpow_neg`, `newtonRadial`, `scalarLaplacian`, `contDiffAt_newtonRadial`, `inner_single_one`, `hasFDerivAt_normSq_rpow`, `normSq_rpow_partial`, `fderiv_newtonRadial_single`, `scalarLaplacian_newtonRadial`, `newtonRadial_eq`, `locallyIntegrable_newtonRadial`, `newtonPotential`, `contDiff_newtonPotential`, `hasFDerivAt_newtonPotential`.

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
lake env lean AxiomAudit.lean    # 577 theorems, only propext / Classical.choice / Quot.sound
```

There is no paper yet. A paper will be drafted after the formalization is final, and it will
match the formalization exactly.

License: Apache-2.0.

## Copyright, license and scope

Copyright 2026 Benjamin Stanley Frohman (ORCID [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)). Licensed under the Apache License, Version 2.0; see `LICENSE` and `NOTICE`.

What is proved vs. conditional: Proved results and the open named `Prop`s are listed above. This is a modified model, not unmodified Navier–Stokes. Every hypothesis is a named `Prop` passed as an explicit argument. Nothing in this repository claims to solve the Clay Millennium problem or global regularity for unmodified 3D Navier–Stokes.
