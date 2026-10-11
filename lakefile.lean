import Lake
open Lake DSL

package exactZCDP where
  moreLeanArgs := #["-j1"]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target]
lean_lib ExactZCDP
