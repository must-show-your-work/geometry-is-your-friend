import Lake
open Lake DSL

-- Dependencies — order matters: project-specific deps first, Mathlib
-- LAST so its transitive versions of aesop/batteries/plausible/etc. win
-- the manifest resolution. Lake will warn otherwise ("project pins
-- different versions of some dependencies than Mathlib").
--
-- We don't `require aesop` explicitly — it comes transitively from
-- Mathlib. Adding it here would re-introduce the version-skew warning.

-- Verso pinned to a recent main HEAD (the reservoir-default revision
-- 4abb984 shipped with duplicate `root := Main` on several `lean_exe`s
-- and Lake errors trying to build it). Keep this aligned with atlas's
-- pin so the manifests resolve consistently.
require verso from git
  "https://github.com/leanprover/verso.git" @ "c004fc5a02584e08def4bfe5c0632d7e208efb58"

-- Atlas is now an external dep — path-based while the must-show-your-work
-- org doesn't yet have remotes. Sibling repo at ../atlas. Once the org
-- has GitHub remotes, swap this for `from git "https://github.com/
-- must-show-your-work/atlas.git" @ "main"`.
require atlas from "../atlas"

require checkdecls from git "https://github.com/PatrickMassot/checkdecls.git"

-- SubVerso is already in the manifest as a transitive (inherited)
-- dep of verso, but `lean_exe "dumptactics"` imports `SubVerso.*`
-- modules directly. Lake's lean_exe target only sees explicitly
-- required deps, not inherited ones, so the import resolution
-- fails ("missing subverso dependency"). Require it explicitly to
-- bring its modules onto the exe's import path. Pin matches the
-- rev in lake-manifest.json so the manifest stays consistent.
require subverso from git
  "https://github.com/leanprover/subverso" @ "main"

-- LeanTeX (kmill/LeanTeX) drives the AST-based latex pipeline that
-- replaces the regex pile in atlas/scripts/card.js. Upstream is
-- pinned at v4.18; our `must-show-your-work/LeanTeX` fork carries
-- the v4.31 compatibility patches (see `shed/forks/LeanTeX.md` for
-- the takeover notes). Used by `scripts/DumpTypeTeX.lean` (Lean-
-- side dumper) and per-domain `latex_pp_rules` declarations.
require leantex from git
  "https://github.com/must-show-your-work/LeanTeX" @ "main"

meta if get_config? env = some "dev" then
require «doc-gen4» from git
  "https://github.com/leanprover/doc-gen4" @ "main"

-- Mathlib LAST — its transitive pins (aesop/batteries/plausible/etc.)
-- now take precedence over anything declared above.
require "leanprover-community" / "mathlib"

-- mostly borrowed from mathlib
abbrev baseOpts : Array LeanOption := #[
  -- pretty-prints `fun a ↦ b`
  ⟨`pp.unicode.fun, true⟩,
  ⟨`relaxedAutoImplicit, true⟩,
  -- ⟨`linter.allScriptsDocumented, true⟩,
  -- ⟨`linter.pythonStyle, true⟩,
  -- ⟨`linter.style.longFile, .ofNat 1500⟩,
  ⟨`weak.linter.mathlibStandardSet, true⟩,
  ⟨`maxSynthPendingDepth, false⟩,
  ⟨`weak.linter.style.longLine, false⟩,
  -- Whitespace between commands (esp. inside `atlas commentary := by …`
  -- blocks) is useful for readability; the Mathlib lint that bans it
  -- is mostly annoying for our style.
  ⟨`weak.linter.style.emptyLine, false⟩,
  ⟨`weak.linter.style.multiGoal, false⟩, -- FIXME: I don't know why this fires
  -- `linter.style.header` covers Mathlib's three header checks: copyright
  -- format, module-docstring-first, and a re-parse of the imports area.
  -- The re-parse stumbles into every `atlas commentary := by` block
  -- ("unexpected token ':='; expected atlasNum") and also flags the
  -- absence of a Mathlib-shaped copyright block + module docstring. None
  -- of these are real problems for us — disable.
  ⟨`weak.linter.style.header, false⟩
]

abbrev opts : Array LeanOption := baseOpts


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

-- (Atlas + AtlasTest lean_libs removed — now provided by the
-- `require atlas` dependency above. Local Atlas.lean / AtlasTest.lean
-- deleted; `import Atlas` resolves to the dep.)


