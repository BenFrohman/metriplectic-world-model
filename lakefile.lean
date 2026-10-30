import Lake
open Lake DSL

package «MetriplecticWorldModel» where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.30.0-rc1"

/-- Ported from frohmanian-symplectic-tether-regularity (velocity tether). -/
lean_lib «FrohmanianSymplecticTether» where
  globs := #[.submodules `FrohmanianSymplecticTether]

/-- Ported from may-form (tethered maximizer data, `TetherFeedback`). -/
lean_lib «TetherMayForm» where
  globs := #[.submodules `TetherMayForm]

@[default_target]
lean_lib «MetriplecticWorldModel» where
  roots := #[`MetriplecticWorldModel]
