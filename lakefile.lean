import Lake.DSL
open System Lake DSL

package ccdeconstructed

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"v4.3.0-rc1"

require quote4 from git
  "https://github.com/leanprover-community/quote4"

@[default_target]
lean_lib CCDeconstructed
