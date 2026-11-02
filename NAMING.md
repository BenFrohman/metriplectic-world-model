# Naming glossary

One open Navier–Stokes statement has carried several names. This file maps each name to the
canonical one. **Nothing here is proved by this file; the canonical statement is OPEN.**

## Canonical names

| Role | Canonical name | Lean identifier | Symbol |
|---|---|---|---|
| Core object | **Frohmanian Tether** | `FrohmanianTether` | $\mathfrak{F}\mathbb{T}$ (𝔉𝕋, "F-Tether") |
| Open statement | **Frohmanian Tether Hypothesis**, parts (A) and (B) | `FrohmanianTetherHypothesis`, `FrohmanianTetherHypothesisA`, `FrohmanianTetherHypothesisB` (in `periodic-ns-classical-continuation`, `BendingRate.lean`) | — |
| Result, once proved | **Frohmanian Tether Theorem** | `FrohmanianTetherTheorem` — *reserved; not declared, because nothing is proved yet* | — |
| General version | Symplectic Tether Theorem | `SymplecticTetherTheorem` | — |

Source of the canonical names and the 𝔉𝕋 symbol (Benjamin Frohman's T/F monogram):
`Definitions/Frohmanian_Tether_Naming_Symbol_Standard.md`, dated 2026-06-03 (NS_Millennium_Proof working tree).

### The open statement

Let $\tau = \omega/|\omega|$ be the vorticity direction and $S$ the strain. For every smooth
maximal solution on $\mathbb{T}^3$ with finite lifespan $T^*$:

- **(A)** the bending strain $(I-\tau\otimes\tau)S\tau$ stays bounded where $|\omega|$ is large, on $[0,T^*)$;
- **(B)** that bound gives a $\tfrac12$-Hölder vorticity direction.

Both parts are **open**.

## Old names → canonical name

Dates for May/June items are folder labels, not server timestamps; git history starts 2026-07-20.

| Old name | Maps to | First dated appearance (source) |
|---|---|---|
| `TetherKernel`, `c2_degeneracy` (C2 condition) | Frohmanian Tether (kernel / condition C2) | 2026-05-28 folder label, `ns_snapshot_0528/Full_Proof_Skeleton.lean:66`; in git at NS_Millennium_Proof `a481f5d` (2026-10-21) |
| `Pi_u`, `theorem_2_3_uniqueness_of_the_minimal_correction` | Frohmanian Tether (projection / uniqueness step) | 2026-05-31 folder label, `Tether_May31.lean.txt` |
| Frohmanian Tether / Frohmanian Tether Theorem / Symplectic Tether Theorem | canonical (this table) | naming standard 2026-06-03; `FrohmanianTether` in git at `38927eb` (2026-07-20) |
| Frohmanian Symplectic Tether | Frohmanian Tether | `frohmanian-symplectic-tether-regularity` `e0a5667` (2026-10-25) |
| `DirectionCurvatureBound` (`HasDirectionCurvatureCoercivity`, `PeriodicDirectionDepletionBound`) | Frohmanian Tether Hypothesis (older formulation) | `b04619c` / `e3d50ad` (2026-10-28) |
| `PeriodicBendingRateHiddenProperty` | `FrohmanianTetherHypothesis` (legacy name, kept) | `periodic-ns-classical-continuation` `3b4c457` (2026-10-31) |
| `PeriodicOrthogonalStrainControl` | `FrohmanianTetherHypothesisA` | same commit |
| `OrthogonalStrainToDirectionHolder` | `FrohmanianTetherHypothesisB` | same commit |

## Rules

- Only the newest repo (`periodic-ns-classical-continuation`) carries the canonical Lean names, as
  aliases; the legacy names stay and nothing is deleted.
- Older repos and Zenodo versions keep their code names as historical records and point here.
- Helper-lemma names are not coined in public text.
- No Lean upstream package exists: no leanprover / leanprover-community (Mathlib, Reservoir)
  package, PR or branch carries any of these names (checked 2026-11-02).
