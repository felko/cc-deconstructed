import Lake.DSL
open System Lake DSL

package ccdeconstructed

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"v4.3.0-rc2"

require Qq from git
  "https://github.com/leanprover-community/quote4"

@[default_target]
lean_lib CCDeconstructed
