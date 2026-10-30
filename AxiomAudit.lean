/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/
-- Axiom audit over every theorem in the built module tree (new + ported).
-- Run: `lake env lean AxiomAudit.lean`. Fails if any theorem uses an axiom outside
-- {propext, Classical.choice, Quot.sound}.
import Lean
import MetriplecticWorldModel

open Lean Elab Command

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut stats : Std.HashMap Name (Nat × Nat) := {}
  let mut bad : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    let some idx := env.getModuleIdxFor? n | continue
    let mod := env.header.moduleNames[idx.toNat]!
    unless (`MetriplecticWorldModel).isPrefixOf mod || (`FrohmanianSymplecticTether).isPrefixOf mod
      || (`TetherMayForm).isPrefixOf mod do continue
    unless ci matches .thmInfo _ do continue
    let axs ← liftCoreM <| Lean.collectAxioms n
    let nonstd := axs.filter (fun a => a ∉ [``propext, ``Classical.choice, ``Quot.sound])
    let (c, b) := stats.getD mod (0, 0)
    stats := stats.insert mod (c + 1, if nonstd.isEmpty then b else b + 1)
    unless nonstd.isEmpty do bad := bad.push s!"{n} : {nonstd}"
  for (m, (c, b)) in stats.toList do
    IO.println s!"{m}: theorems={c} nonstandard={b}"
  for s in bad do
    IO.println s
  let total := stats.fold (fun acc _ (c, _) => acc + c) 0
  IO.println s!"TOTAL theorems={total} nonstandard={bad.size}"
  unless bad.isEmpty do
    throwError "axiom audit FAILED: {bad.size} theorem(s) use non-standard axioms"

#print axioms MetriplecticWorldModel.model_global_regularity
#print axioms MetriplecticWorldModel.model_global_regularity_of_realization
#print axioms MetriplecticWorldModel.uniform_ceiling
#print axioms MetriplecticWorldModel.kappa_zero_no_ceiling
#print axioms MetriplecticWorldModel.velocityTether_entropy_production
#print axioms MetriplecticWorldModel.instance_global_regularity
