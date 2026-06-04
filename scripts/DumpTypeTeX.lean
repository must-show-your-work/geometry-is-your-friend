import Lean
import Geometry
import Atlas
import LeanTeX

/-! Dump every atlas-tagged decl's type as LaTeX (via LeanTeX's
    AST-walking pretty printer) to `blueprint/type-tex.json`.

    For each `(declName, AtlasEntry)` in the merged atlas state, look
    up the decl's `ConstantInfo`, take its type expression, run
    `LeanTeX.run_latexPP` on it, and emit the resulting LaTeX string
    keyed by the decl's FQN.

    `export_graph.py` reads this and attaches the strings as a
    `type_tex` field on each node, alongside the existing `type_pp`
    (the Lean pretty-printer's textual form, which the regex-based
    `card.js::leanToLatex` consumes). The viewer renders `type_tex`
    when present (the LeanTeX path) and falls back to the regex
    pipeline otherwise, so the two render paths can run side by side
    behind the `?compare=1` URL flag.

    Once the AST path is the default and the regex path is removed,
    the fallback can go and `type_pp` can be dropped from the node
    data. -/

namespace DumpTypeTeX

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

end DumpTypeTeX

open DumpTypeTeX Lean Meta

unsafe def main : IO Unit := do
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let imports : Array Import := #[
    { module := `Geometry },
    { module := `Atlas },
    { module := `LeanTeX }
  ]
  -- `loadExts := true` is the load-bearing flag: without it the env's
  -- attribute extension state stays at the empty initial value, so
  -- `latex_pp_app` / `latex_pp` attribute registrations from
  -- imported .oleans are invisible to dispatch and LeanTeX falls
  -- back to `defaultLatexPP` on every node. Requires
  -- `enableInitializersExecution` above (the interpreter has to be
  -- able to materialise the registered handlers' closures).
  let env ← importModules imports {} (loadExts := true)
  let imported := Atlas.atlasStateFromImports env
  let live     := Atlas.atlasExt.getState env
  let byName := imported.byName.foldl (init := live.byName) fun acc n e =>
    match acc.find? n with
    | some _ => acc
    | none   => acc.insert n e

  let coreCtx : Core.Context := { fileName := "<dumptypetex>", fileMap := default }
  let coreState : Core.State := { env := env }

  let metaAction : MetaM (Array String) := do
    let mut out : Array String := #[]
    let mut considered := 0
    let mut failed     := 0
    for (declName, _) in byName do
      considered := considered + 1
      match env.find? declName with
      | none =>
        IO.eprintln s!"[dumptypetex] {declName}: not in env"
        failed := failed + 1
      | some info =>
        try
          let tex ← LeanTeX.run_latexPP info.type {}
          let entry := "\"" ++ jsonEscape declName.toString ++ "\":\""
                    ++ jsonEscape tex ++ "\""
          out := out.push entry
        catch ex =>
          let msg ← ex.toMessageData.toString
          IO.eprintln s!"[dumptypetex] {declName}: {msg}"
          failed := failed + 1
    IO.eprintln s!"[dumptypetex] considered={considered} succeeded={out.size} failed={failed}"
    return out

  let (entries, _) ← metaAction.run'.toIO coreCtx coreState
  let json := "{\n  " ++ String.intercalate ",\n  " entries.toList ++ "\n}"
  IO.FS.createDirAll "blueprint"
  IO.FS.writeFile "blueprint/type-tex.json" json
  IO.eprintln s!"Wrote {entries.size} type-tex entries to blueprint/type-tex.json"
