import Lake
open Lake DSL

package hybrid {
  -- add package configuration options here
}

lean_lib Hybrid {
  -- add library configuration options here
}

@[default_target]
lean_lib hybrid

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"