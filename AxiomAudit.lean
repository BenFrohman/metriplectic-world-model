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
#print axioms MetriplecticWorldModel.split_exists_unique
#print axioms MetriplecticWorldModel.canonical_metric_bracket
#print axioms MetriplecticWorldModel.canonical_metric_bracket_sign
#print axioms MetriplecticWorldModel.realization_of_rate
#print axioms MetriplecticWorldModel.not_streamFunctionRepresentative
#print axioms MetriplecticWorldModel.scalarLaplacian_newtonRadial
#print axioms MetriplecticWorldModel.contDiffAt_newtonRadial
#print axioms MetriplecticWorldModel.locallyIntegrable_newtonRadial
#print axioms MetriplecticWorldModel.contDiff_newtonPotential
#print axioms MetriplecticWorldModel.hasFDerivAt_newtonPotential
#print axioms MetriplecticWorldModel.scalarLaplacian_regNewton
#print axioms MetriplecticWorldModel.regNewton_le
#print axioms MetriplecticWorldModel.tendsto_regNewton
#print axioms MetriplecticWorldModel.integral_regRadial
#print axioms MetriplecticWorldModel.integral_neg_scalarLaplacian_regNewton
#print axioms MetriplecticWorldModel.tendsto_regPeak_approxIdentity
#print axioms MetriplecticWorldModel.integral_mul_scalarLaplacian_eq
#print axioms MetriplecticWorldModel.regNewton_conv_laplacian
#print axioms MetriplecticWorldModel.tendsto_regNewton_conv
#print axioms MetriplecticWorldModel.scalarLaplacian_newtonPotential
#print axioms MetriplecticWorldModel.scalarLaplacian_newtonPotential_eq
#print axioms MetriplecticWorldModel.gradKer_bound
#print axioms MetriplecticWorldModel.locallyIntegrable_norm_rpow_neg_two
#print axioms MetriplecticWorldModel.integrable_rpow_neg_two_mul
#print axioms MetriplecticWorldModel.tendsto_gradKer_conv
#print axioms MetriplecticWorldModel.regNewton_conv_deriv
#print axioms MetriplecticWorldModel.newtonPotential_deriv_eq
#print axioms MetriplecticWorldModel.newtonVec_coord
#print axioms MetriplecticWorldModel.directionalCoord_newtonVec
#print axioms MetriplecticWorldModel.integrable_gradKer_mul
#print axioms MetriplecticWorldModel.gradKer_zero_eq
#print axioms MetriplecticWorldModel.biotSavart_eq_curl_newtonVec
#print axioms MetriplecticWorldModel.fderiv_fderiv_swap
#print axioms MetriplecticWorldModel.curl_curl_newtonVec
#print axioms MetriplecticWorldModel.curlBiotSavartTest
#print axioms MetriplecticWorldModel.helicity_casimir_test_closed
#print axioms MetriplecticWorldModel.biotSavart_selfAdjoint
#print axioms MetriplecticWorldModel.helicity_gateaux
#print axioms MetriplecticWorldModel.curl_eq_of_isGateauxRepOn
#print axioms MetriplecticWorldModel.curl_eq_two_of_helicity_rep
#print axioms MetriplecticWorldModel.helicity_casimir_of_rep
#print axioms MetriplecticWorldModel.helicity_casimir_canonical
#print axioms MetriplecticWorldModel.kineticEnergy_reps_curl_eq
#print axioms MetriplecticWorldModel.streamFunctionRepModGradOn_of_exists
#print axioms MetriplecticWorldModel.curlFreeIsGradient
#print axioms MetriplecticWorldModel.decays_newtonPotential
#print axioms MetriplecticWorldModel.IsTestOrbit.integral_coord_eq_zero
#print axioms MetriplecticWorldModel.integral_pairing_curl_symm
#print axioms MetriplecticWorldModel.integral_inner_biotSavart_eq
#print axioms MetriplecticWorldModel.keStream_isGateauxRep
#print axioms MetriplecticWorldModel.curl_keStream
#print axioms MetriplecticWorldModel.streamFunctionRepModGradOn
#print axioms MetriplecticWorldModel.hasDerivAt_eq_of_touch_below
#print axioms MetriplecticWorldModel.eventually_forall_abs_sub_lt
#print axioms MetriplecticWorldModel.danskin_upper_dini
#print axioms MetriplecticWorldModel.deriv2_nonpos_of_isLocalMax
#print axioms MetriplecticWorldModel.hasDerivAt_line
#print axioms MetriplecticWorldModel.inner_fderiv_eq_zero_of_max
#print axioms MetriplecticWorldModel.inner_convective_eq_zero_of_max
#print axioms MetriplecticWorldModel.inner_second_deriv_nonpos_of_max
#print axioms MetriplecticWorldModel.inner_laplacian_nonpos_of_max
#print axioms MetriplecticWorldModel.vorticity_danskin_upper_dini
#print axioms MetriplecticWorldModel.sup_mul_deriv_eq_inner
#print axioms MetriplecticWorldModel.maxPointRealization_of_field
#print axioms MetriplecticWorldModel.entropyCasimir_of_arnoldCasimirField
#print axioms MetriplecticWorldModel.arnoldCasimirField_of_curl_parallel
#print axioms MetriplecticWorldModel.arnoldCasimirField_helicity
#print axioms MetriplecticWorldModel.ceiling_of_upper_dini
#print axioms MetriplecticWorldModel.sup_eq_sSup_image
#print axioms MetriplecticWorldModel.sup_continuous_of_uniform_support
#print axioms MetriplecticWorldModel.field_uniform_ceiling
#print axioms MetriplecticWorldModel.fieldTetherFeedback_cubicTether
#print axioms MetriplecticWorldModel.field_uniform_ceiling_cubicTether
#print axioms MetriplecticWorldModel.field_uniform_ceiling_of_netRate
#print axioms MetriplecticWorldModel.fieldNetRate_of_logLoss_cubicTether
#print axioms MetriplecticWorldModel.field_uniform_ceiling_logLoss_cubicTether
