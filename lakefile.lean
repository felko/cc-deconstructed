import Lake.DSL
open System Lake DSL

package ccdeconstructed

require std from git
  "https://github.com/leanprover/std4" @ "v4.3.0"

require LeanCopilot from git
  "https://github.com/lean-dojo/LeanCopilot.git" @ "v1.0.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"@"v4.3.0"

require Qq from git
  "https://github.com/leanprover-community/quote4"

@[default_target]
lean_lib CCDeconstructed where
  moreLinkArgs := #[s!"-L{__dir__}/.lake/build/lib", "-lctranslate2"]
