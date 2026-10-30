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

## Open named `Prop`s

Each one is passed as an explicit argument. None is proved here.

* `TetheredMaxRate C κ M M'`: `M` is differentiable and satisfies `M' ≤ C M² − κ M³` for `t ≥ 0`.
* `MaxPointRealization C κ Cabs M M'`: for every `t ≥ 0`, there is maximizer data satisfying
  the five may-form `Prop`s: `EnergyIdentity`, `StretchingCZ`, `ViscousAtMax`,
  `TetherFeedback` and `CrossControlled`.
  * `StretchingCZ` is a pure `y³` bound. It is false as an `L∞` estimate for Navier–Stokes,
    and it is an assumption of this model as well.
  * `TetherFeedback` holds only in the tethered model.
* `ModelContinuation Smooth M`: a continuation criterion of Beale–Kato–Majda type for the model.
* `EntropyCasimir P S`: the entropy is a Casimir of `P`.
* `KineticEnergyCurlIdentity ω` (ported): `curl(δH/δω) = u`.

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
lake env lean AxiomAudit.lean    # 586 theorems, only propext / Classical.choice / Quot.sound
```

There is no paper yet. A paper will be drafted after the formalization is final, and it will
match the formalization exactly.

License: Apache-2.0.
