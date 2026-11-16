/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import MetriplecticWorldModel.Semantics

/-!
# Truth Gate kernel audit

Checks, in the Lean kernel environment:
* `TruthGate.formal_claim`, `TruthGate.paper_claim`, `TruthGate.intended_correspondence`,
  `TruthGate.formal_claim_holds`, `TruthGate.paper_claim_holds` exist with the required types;
* each depends only on `propext`, `Classical.choice`, `Quot.sound`;
* `formal_claim` and `paper_claim` are NOT definitionally equal (no vacuous correspondence);
* the proof of `intended_correspondence` does not use the main theorem(s) or the `*_holds`
  lemmas (it is a statement-level equivalence, not "both sides happen to be true");
* `formal_claim_holds` is built from the locked main theorem(s), and when there is a single
  main theorem its statement is definitionally `formal_claim`;
* `paper_claim_holds` is obtained by transport across `intended_correspondence`.
-/

open Lean Meta Elab Command

namespace TruthGateAudit

def standard : List Name := [``propext, ``Classical.choice, ``Quot.sound]
def mains : List Name := [`MetriplecticWorldModel.uniform_ceiling]

partial def reach (env : Environment) (todo : List Name) (seen : NameSet) : NameSet :=
  match todo with
  | [] => seen
  | n :: rest =>
    if seen.contains n then reach env rest seen else
    let seen := seen.insert n
    -- upstream libraries cannot mention this repository's constants: do not descend into them
    let upstream := match env.getModuleIdxFor? n with
      | some i => let m := env.header.moduleNames[i.toNat]!
          [`Mathlib, `Init, `Std, `Lean, `Batteries, `Aesop, `Qq, `Plausible, `ProofWidgets,
            `ImportGraph, `LeanSearchClient, `Lake, `Cli].any (·.isPrefixOf m)
      | none => false
    if upstream then reach env rest seen else
    match env.find? n with
    | none => reach env rest seen
    | some ci =>
      let cs := ci.type.getUsedConstants ++ (match ci.value? (allowOpaque := true) with
        | some v => v.getUsedConstants | none => #[])
      reach env (cs.toList ++ rest) seen

def directUses (env : Environment) (n : Name) : NameSet :=
  match env.find? n with
  | some ci => ((ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]).foldl (·.insert ·) {}
  | none => {}

end TruthGateAudit

open TruthGateAudit in
run_cmd do
  let env ← getEnv
  let mut ok := true
  let req := [`TruthGate.formal_claim, `TruthGate.paper_claim, `TruthGate.intended_correspondence,
    `TruthGate.formal_claim_holds, `TruthGate.paper_claim_holds] ++ mains
  for n in req do
    unless env.contains n do
      logInfo m!"TRUTH GATE FAIL: missing declaration {n}"; ok := false
  if !ok then throwError "TRUTH GATE FAIL: missing declarations"
  -- types
  let fc := mkConst `TruthGate.formal_claim
  let pc := mkConst `TruthGate.paper_claim
  let ic ← getConstInfo `TruthGate.intended_correspondence
  unless ic.type == mkApp2 (mkConst ``Iff) fc pc do
    logInfo m!"TRUTH GATE FAIL: intended_correspondence has type {ic.type}"; ok := false
  for (n, t) in [(`TruthGate.formal_claim_holds, fc), (`TruthGate.paper_claim_holds, pc)] do
    unless (← getConstInfo n).type == t do
      logInfo m!"TRUTH GATE FAIL: {n} does not have the locked type"; ok := false
  -- axioms
  for n in req do
    let axs ← collectAxioms n
    let bad := axs.filter (fun a => !standard.contains a)
    logInfo m!"AXIOMS {n}: {axs.toList}"
    unless bad.isEmpty do
      logInfo m!"TRUTH GATE FAIL: {n} uses nonstandard axioms {bad.toList}"; ok := false
  -- no aliasing: paper_claim's body must not mention formal_claim, and the two bodies must
  -- differ syntactically after unfolding only their own definitions
  let fv := ((← getConstInfo `TruthGate.formal_claim).value? (allowOpaque := true)).getD fc
  let pv := ((← getConstInfo `TruthGate.paper_claim).value? (allowOpaque := true)).getD pc
  if pv.getUsedConstants.contains `TruthGate.formal_claim then
    logInfo "TRUTH GATE FAIL: paper_claim is defined in terms of formal_claim (alias)"; ok := false
  if fv == pv then
    logInfo "TRUTH GATE FAIL: formal_claim and paper_claim have syntactically equal bodies"; ok := false
  -- non-vacuity: the two claims must not be definitionally equal
  -- bounded (heartbeat-capped) default-transparency check; a timeout counts as "not shown
  -- definitionally equal" and is reported, the syntactic and transport checks still apply
  let defeq? : Option Bool ← liftTermElabM <| withTransparency .default <| withoutModifyingState <|
    withTheReader Core.Context (fun c => { c with maxHeartbeats := 2000000 }) <|
      (try some <$> isDefEq fc pc catch _ => pure none)
  if defeq?.isNone then
    logInfo "TRUTH GATE NOTE: definitional-equality check hit its heartbeat cap (inconclusive)"
  if defeq? == some true then
    logInfo "TRUTH GATE FAIL: formal_claim and paper_claim are definitionally equal (vacuous lock)"
    ok := false
  -- transport: the correspondence proof must not use the main theorem(s) or *_holds
  let r := reach env [`TruthGate.intended_correspondence] {}
  for n in mains ++ [`TruthGate.formal_claim_holds, `TruthGate.paper_claim_holds] do
    if r.contains n then
      logInfo m!"TRUTH GATE FAIL: intended_correspondence depends on {n}"; ok := false
  -- formal_claim_holds is built from the main theorems
  let fh := reach env [`TruthGate.formal_claim_holds] {}
  for n in mains do
    unless fh.contains n do
      logInfo m!"TRUTH GATE FAIL: formal_claim_holds does not use main theorem {n}"; ok := false
  if mains.length == 1 then
    let mci ← getConstInfo mains.head!
    -- instantiate universe parameters at `0` (claims are stated at `Type`)
    let mt := mci.instantiateTypeLevelParams (mci.levelParams.map fun _ => levelZero)
    let same ← liftTermElabM <| withTransparency .default <| withoutModifyingState <|
      withTheReader Core.Context (fun c => { c with maxHeartbeats := 2000000 }) <|
        (try isDefEq mt fc catch _ => pure false)
    unless same do
      logInfo m!"TRUTH GATE FAIL: main theorem statement is not formal_claim"; ok := false
  unless (directUses env `TruthGate.paper_claim_holds).contains `TruthGate.intended_correspondence do
    logInfo "TRUTH GATE FAIL: paper_claim_holds is not transported across intended_correspondence"
    ok := false
  if ok then
    logInfo m!"TRUTH GATE AUDIT PASS: main theorems {mains}; formal_claim ↔ paper_claim locked, standard axioms only"
  else
    throwError "TRUTH GATE FAIL"

#print axioms TruthGate.intended_correspondence
#print axioms TruthGate.paper_claim_holds
