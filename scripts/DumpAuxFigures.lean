import Lean
import Geometry
import Atlas
import Figures
import Figures.SVG
import Geometry.Construction.DSL
import Geometry.Construction.Lowering
import Geometry.Construction.ProgressiveFigure

/-! Dump every `auxillary { … }` block as a small SVG keyed by
    (decl, line, description) into `blueprint/aux-figures.json`.

    For each `(declName, AuxillaryAddendum)` entry recorded in
    `auxillaryAddendaExt` (populated by the `auxillary` tactic), look
    up that decl's base IR via the atlas state + `baseIRExprExt`, then
    render base + addendum via `Geometry.Construction.renderAuxBare`.
    Result: an SVG per aux block showing the figure with the addendum
    layered on top of the base.

    `export_graph.py` reads this and attaches it as `aux_figures`
    on each decl's data; the viewer's renderProofTriColumn drops the
    SVGs into the RHS commentary column at the matching line.

    Sidecar (not in-DB) for the same bulk reasons as `figures.json`. -/

namespace DumpAuxFigures

open Lean Meta

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

/-- Walk a SimplePersistentEnvExtension's entries across all imported
    modules. Same shape as DumpFigures's helper. -/
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
  for e in ext.getState env do
    acc := acc.push e
  return acc

/-- Per-decl (kind, num) lookup from the merged atlas state. Used to
find the decl's base IR Expr keyed by (kind, num) in `baseIRExprExt`. -/
private def targetForDecl (env : Environment) (declName : Name) :
    Option (String × String) :=
  let imported := Atlas.atlasStateFromImports env
  let live     := Atlas.atlasExt.getState env
  let byName := imported.byName.foldl (init := live.byName) fun acc n e =>
    match acc.find? n with
    | some _ => acc
    | none   => acc.insert n e
  match byName.find? declName with
  | some e => some (e.kind, e.number)
  | none   => none

/-- Render base + addendum to a bare SVG (no inline `<style>` block,
    no background fill). `baseExpr` is the Lean Expr stored in
    `baseIRExprExt`; we evalExpr it to a Construction value, then
    hand both to `renderAuxBare`. -/
private def renderOne (baseExpr : Lean.Expr) (addendum : Geometry.Construction.DSL.Construction) :
    MetaM String := do
  let constructionTy := mkConst ``Geometry.Construction.DSL.Construction
  let base ← unsafe Meta.evalExpr Geometry.Construction.DSL.Construction
                                  constructionTy baseExpr
  return Geometry.Construction.renderAuxBare base addendum

end DumpAuxFigures

open DumpAuxFigures Lean Meta

def main : IO Unit := do
  let imports : Array Import := #[
    { module := `Geometry },
    { module := `Geometry.Construction.Lowering },
    { module := `Geometry.Construction.ProgressiveFigure },
    { module := `Atlas }
  ]
  let env ← importModules imports {}
  let auxEntries := entriesFromImports
                    Geometry.Construction.auxillaryAddendaExt env
  let coreCtx : Core.Context := { fileName := "<dumpauxfigures>", fileMap := default }
  let coreState : Core.State := { env := env }

  -- Group aux entries by decl name so the JSON groups all aux blocks
  -- for a single proof together.
  let mut grouped : Std.HashMap Name (Array Geometry.Construction.AuxillaryAddendum) := {}
  for (declName, aux) in auxEntries do
    grouped := grouped.insert declName ((grouped.getD declName #[]).push aux)

  let metaAction : MetaM (Array String) := do
    let mut out : Array String := #[]
    for (declName, addenda) in grouped do
      match targetForDecl env declName with
      | none =>
        IO.eprintln s!"[dumpauxfigures] no atlas (kind, num) for {declName}; skipping {addenda.size} aux blocks"
      | some (kind, num) =>
        match Atlas.baseIRExprFor env kind num with
        | none =>
          IO.eprintln s!"[dumpauxfigures] no base IR for ({kind}, {num}); decl {declName} has aux blocks but no base figure"
        | some baseExpr =>
          let mut perDecl : Array String := #[]
          for aux in addenda do
            try
              let svg ← renderOne baseExpr aux.addendum
              let desc := match aux.description with
                | some d => "\"" ++ jsonEscape d ++ "\""
                | none   => "null"
              -- `s!"{{...}}"` brace-escape interaction with embedded
              -- `\"` was tripping the parser; build by concatenation.
              let entry :=
                "{\"line\":" ++ toString aux.line
                ++ ",\"svg\":\"" ++ jsonEscape svg
                ++ "\",\"description\":" ++ desc ++ "}"
              perDecl := perDecl.push entry
            catch ex =>
              let msg ← ex.toMessageData.toString
              IO.eprintln s!"[dumpauxfigures] failed to render aux at line {aux.line} of {declName}: {msg}"
          if !perDecl.isEmpty then
            let arr := "[" ++ String.intercalate "," perDecl.toList ++ "]"
            let entry := "\"" ++ jsonEscape declName.toString ++ "\":" ++ arr
            out := out.push entry
    return out

  let (entries, _) ← metaAction.run'.toIO coreCtx coreState
  let json := "{\n  " ++ String.intercalate ",\n  " entries.toList ++ "\n}"
  IO.FS.createDirAll "blueprint"
  IO.FS.writeFile "blueprint/aux-figures.json" json
  IO.eprintln s!"Wrote aux-figures for {entries.size} decls to blueprint/aux-figures.json"
