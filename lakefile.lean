import Lake
open Lake DSL

-- Dependencies
require "leanprover-community" / "mathlib"
require "leanprover" / "verso"
require aesop from git "https://github.com/leanprover-community/aesop"

-- mostly borrowed from mathlib
abbrev opts : Array LeanOption := #[
  -- pretty-prints `fun a ↦ b`
  ⟨`pp.unicode.fun, true⟩,
  ⟨`relaxedAutoImplicit, true⟩,
  -- ⟨`linter.allScriptsDocumented, true⟩,
  -- ⟨`linter.pythonStyle, true⟩,
  -- ⟨`linter.style.longFile, .ofNat 1500⟩,
  ⟨`weak.linter.mathlibStandardSet, true⟩,
  ⟨`maxSynthPendingDepth, false⟩,
  ⟨`weak.linter.style.longLine, false⟩,
  -- (`weak.linter.style.emptyLine, false),
  ⟨`weak.linter.style.multiGoal, false⟩ -- FIXME: I don't know why this fires
]


-- Main package
package "geometry-is-your-friend" where
  version := v!"0.2.0"
  -- Global lean options for pretty-printing, synthesis, etc.
  leanOptions := opts
  -- any additional package configuration here

lean_exe "dumpdecls" where
  root := `scripts.DumpDecls

lean_exe "atlasprobe" where
  root := `scripts.AtlasProbe

lean_exe "dumpimports" where
  root := `scripts.DumpImports

lean_exe "dumptactics" where
  root := `scripts.DumpTactics
  -- SubVerso's `processCommands` ends up running `IO.getRandomBytes`
  -- (and other initializers) via the interpreter, which requires this
  -- flag. Without it every module fails with a native-impl error.
  supportInterpreter := true

@[default_target]
lean_lib «Geometry» where
  srcDir := "."    -- points to main src folder
  -- You can also specify includeDirs if needed, e.g., for diagrams
  -- includeDirs := #[ "geometry/**/diagrams" ]

-- Atlas is a top-level library so it can be extracted into its own
-- package later without touching the Geometry namespace. For now it
-- lives in this same repo with its own `lean_lib`.
lean_lib «Atlas» where
  srcDir := "."
  roots := #[`Atlas]

-- Smoke test for Atlas. Separate library so the test file doesn't
-- accidentally get pulled into Geometry's transitive closure.
lean_lib «AtlasTest» where
  srcDir := "."
  roots := #[`AtlasTest]

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"


