import Lake
open Lake DSL

package «meta-complexity-lean4» where
  -- Package configuration

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «MetaComplexityMaster20» where
  -- Library configuration

lean_lib «MetaComplexityMaster19» where
  -- Library configuration
