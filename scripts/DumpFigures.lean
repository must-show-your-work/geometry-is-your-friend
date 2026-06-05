import Lean
import Geometry
import Geometry.DumpCache
import Atlas
import Figures
import Figures.SVG
import Geometry.Construction.DSL
import Geometry.Construction.Lowering

/-! Dump every atlas-figure to `blueprint/figures.json`.

    For each `(kind, number) → IR Expr` entry in `Atlas.baseIRExprExt`
    (populated by `atlas commentary := by … figure := by construction
    { … }`), evaluate the IR to a `Construction`, render it to SVG via
    `Lowering.lower` + the `Renderable Construction String` instance,
    and emit a sidecar JSON keyed by the decl's FQN. `export_graph.py`
    reads this and injects `figure_svg` into each node's data.

    Sidecar (not in-DB) because:
    - Figures are bulky (~5–20KB SVG each); keeping them out of the
      Kuzu DB keeps the graph DB cheap to ingest.
    - Re-rendering on demand happens often during dev; isolating it
      lets `just graph` or a dedicated `just figures` rebuild only the
      figure pass when the visualization stack changes. -/

namespace DumpFigures

open Lean Meta

/-- JSON-escape a string: escape `"`, `\`, control chars. Same shape
as DumpDecls.jsonEscape but local so this file can build standalone. -/
private def jsonEscape (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    match c with
    | '"'  => acc ++ "\\\""
    | '\\' => acc ++ "\\\\"
    | '\n' => acc ++ "\\n"
    | '\r' => acc ++ "\\r"
    | '\t' => acc ++ "\\t"
    | c    => if c.toNat < 0x20 then acc ++ s!"\\u{Nat.toDigits 16 c.toNat}"
              else acc.push c

/-- Walk a `SimplePersistentEnvExtension`'s entries across all
imported modules, mirroring DumpDecls's `markersFromImports`. -/
private def entriesFromImports {α} [Inhabited α]
    (ext : SimplePersistentEnvExtension α (Array α)) (env : Environment) :
    Array α := Id.run do
  let mut acc : Array α := #[]
  let mut i : Nat := 0
  let n := env.allImportedModuleNames.size
  while i < n do
    for e in PersistentEnvExtension.getModuleEntries ext env i do
      acc := acc.push e
    i := i + 1
  -- Local entries (declared in this run's working file, if any).
  for e in ext.getState env do
    acc := acc.push e
  return acc

/-- Look up the decl FQN whose atlas attribute matches (kind, num).
Atlas stores a `NameMap AtlasEntry` keyed by decl name; we invert
it on demand. Returns the first hit (atlas's number→decl mapping
SHOULD be unique, but in pathological cases — paired propositions
sharing a number — the first wins). -/
private def findDeclForTarget (env : Environment) (kind num : String) :
    Option Name :=
  let imported := Atlas.atlasStateFromImports env
  let live     := Atlas.atlasExt.getState env
  let byName := imported.byName.foldl (init := live.byName) fun acc n e =>
    match acc.find? n with
    | some _ => acc
    | none   => acc.insert n e
  byName.foldl (init := none) fun acc n e =>
    if acc.isSome then acc
    else if e.kind == kind && e.number == num then some n
    else none

/-- Render one IR Expr to a bare SVG string (no inline `<style>`
block). `e` is the elaborated `Construction` term Atlas stored when
the `figure := by construction { … }` field was processed. The
atlas viewer supplies its own CSS for the `.txt`/`.lbl`/`.callout`
classes via `toc.html`, so we strip the inline styles at dump time
and let the host theme drive the look. -/
private def renderOne (e : Expr) : MetaM String := do
  let stringTy := mkConst ``String
  let renderApp := mkApp (mkConst ``Geometry.Construction.renderBare) e
  let svg ← unsafe Meta.evalExpr String stringTy renderApp
  return svg

end DumpFigures

open DumpFigures Lean Meta

def main : IO Unit := do
  -- `lake env lean --run` sets LEAN_PATH so importModules finds
  -- Geometry + Atlas without us touching searchPathRef.
  -- Include Lowering explicitly so the `Renderable Construction String`
  -- instance is in the env's instance table. `import Geometry` alone
  -- doesn't pull it because Geometry doesn't re-export construction.
  let imports : Array Import := #[
    { module := `Geometry },
    { module := `Geometry.Construction.Lowering },
    { module := `Atlas }
  ]
  let env ← importModules imports {}
  let fp := Geometry.DumpCache.defaultFingerprint env

  Geometry.DumpCache.runIfChanged "figures" fp do
    let entries := entriesFromImports Atlas.baseIRExprExt env
    let coreCtx : Core.Context := { fileName := "<dumpfigures>", fileMap := default }
    let coreState : Core.State := { env := env }
    let metaAction : MetaM (Array String) := do
      let mut out : Array String := #[]
      for ((kind, num), e) in entries do
        match findDeclForTarget env kind num with
        | none =>
          IO.eprintln s!"[dumpfigures] no decl found for ({kind}, {num}); skipping"
        | some declName =>
          try
            let svg ← renderOne e
            let entry := s!"\"{jsonEscape declName.toString}\":\"{jsonEscape svg}\""
            out := out.push entry
          catch ex =>
            let msg ← ex.toMessageData.toString
            IO.eprintln s!"[dumpfigures] failed to render ({kind} {num}) for {declName}: {msg}"
      return out
    let (entries, _) ← metaAction.run'.toIO coreCtx coreState
    let json := "{\n  " ++ String.intercalate ",\n  " entries.toList ++ "\n}"
    IO.FS.createDirAll "blueprint"
    IO.FS.writeFile "blueprint/figures.json" json
    IO.eprintln s!"Wrote {entries.size} figures to blueprint/figures.json"
