import Lake
open Lake DSL

package «mathlib4-all-tactics» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Mathlib4AllTactics» {
  -- add any library configuration options here
}
