import Lake
open Lake DSL

abbrev linter : Array LeanOption := #[
  ⟨`linter.hashCommand, true⟩,
  ⟨`linter.missingEnd, true⟩,
  ⟨`linter.cdot, true⟩,
  ⟨`linter.dollarSyntax, true⟩,
  ⟨`linter.style.lambdaSyntax, true⟩,
  ⟨`linter.longLine, true⟩,
  ⟨`linter.oldObtain, true,⟩,
  ⟨`linter.refine, true⟩,
  ⟨`linter.setOption, true⟩
]

/-- Lean and linter options used throughout StatsMLlib. -/
abbrev options := #[
    ⟨`pp.unicode.fun, true⟩, -- pretty-prints `fun a ↦ b`
    ⟨`autoImplicit, false⟩
  ] ++ -- options that are used in `lake build`
    linter.map fun s ↦ { s with name := `weak ++ s.name }


package «StatsMLlib» where
  -- add any package configuration options here
  leanOptions := options
  moreServerOptions := linter

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.33.0"

@[default_target]
lean_lib «StatsMLlib» where
  globs := #[.submodules `StatsMLlib]

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "v4.33.0"
