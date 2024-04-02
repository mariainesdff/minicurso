import Lake
open Lake DSL

package «minicurso» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Minicurso» {
  -- add any library configuration options here
}
