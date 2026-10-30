/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

module

public import Mathlib.Logic.Basic   -- for minimal Prop infrastructure if needed

/-!
Original work by Benjamin Stanley Frohman.
Lean 4 encoding of the NS global regularity proof.

This file is part of the Lean 4 formalization of the Frohmanian Symplectic Tether Theorem.

See the root document `LaTeX_Lean_Relationship.md` (especially Sections 2–6)
for the precise correspondence between this module and the May 31 2026 LaTeX manuscript
+ the three source documents.

This module is the single centralized, auditable home for every intentional axiom
used in the entire development.

## formal verification Posture (Mandatory Reading for Referees)

The Frohmanian Symplectic Tether formalization follows the strictest possible
discipline on axioms:

- **Zero intentional axioms** are used in the novel geometric core
  (the Tether construction 𝔗_F, the 5-step canonicity/uniqueness proof,
   the metriplectic bracket properties in `FieldMetriplectic.lean`,
   degeneracy on the mollified sup-norm proxy, invariance under SDiff(T³),
   and the non-circular two-layer global regularity corollary).

- All classical supporting facts (local existence, Beale–Kato–Majda criterion,
   Calderón–Zygmund estimates, Gagliardo–Nirenberg interpolation, parabolic
   regularity, etc.) are treated as documented black boxes. They are either
   imported from mathlib4 or enter the theorems that use them as explicitly
   stated hypotheses. They are **never** declared as axioms and never proved by `sorry`.

- Any future intentional axiom (for example, a deep unique-continuation property
  that has not yet been formalized in mathlib) will be added here only after
  written justification in both the LaTeX manuscript and this file, and only
  when it is genuinely required for a conditional result.

This file exists so that a Navier–Stokes referee can read **one** short file and know
exactly the complete, minimal list of everything that was assumed rather than proved.

See also `Blueprint.md` (Validation and Trust Strategy + Classical vs Novel Separation)
and the four living audit checklists.
-/

namespace FrohmanianTether

/-!
## Current Status (as of generation date)

**The formalization currently uses ZERO intentional axioms in the dependency tree
of any novel claim.**

The build has 0 `sorry`. Local existence, the Beale–Kato–Majda continuation
criterion, and the tethered Riccati majorant of `‖ω‖_∞` enter as explicitly
stated hypotheses of the theorems that use them. They are hypotheses, not proofs,
and every result that depends on them is conditional on them.

No axiom is used to justify the existence, uniqueness, or canonicity of the
Frohmanian Symplectic Tether 𝔗_F itself.
-/

-- =============================================================================
-- SECTION: INTENTIONAL AXIOMS (Currently Empty by Design)
-- =============================================================================

-- Metriplectic assumptions, if any, belong to the later Frohmanian Core paper.
-- None are declared in this repository.

/-!
## How to Add a New Intentional Axiom (formal verification Checklist)

1. Write a one-paragraph justification in the LaTeX manuscript under a clearly
   labeled "Assumptions" section.
2. Add the axiom here with a descriptive name (never `Axiom1`, `Axiom2`, ...).
3. Add a matching `@[inherit_doc]` theorem or block explaining:
   - Why it is necessary
   - Which literature results support it
   - Exactly which theorems in the development depend on it
   - Why it does **not** create circularity with the novel Tether geometry
4. Update `LaTeX_Lean_Relationship.md` (run the generator script).
5. Update `Blueprint.md` (add the axiom to the dependency graph and checklists).
6. Re-run `lake build` and record the new `#print axioms` output for the
   affected top-level theorems.
7. Add a note in `Development_vs_Final.md` (or equivalent) distinguishing the
   development state from the submission state.

This process guarantees that the final submitted artifact will contain the
smallest possible, fully documented list of assumptions.
-/

end FrohmanianTether
