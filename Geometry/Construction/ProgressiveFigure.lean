/-
Geometry/Construction/ProgressiveFigure.lean — per-tactic-line figure
widgets so the InfoView's figure progressively reflects the auxillary
state at the cursor's position.

Mechanism:
1. `auxillary { … }` tactic pushes `(declName, line, addendum)` to
   `auxillaryAddendaExt` instead of saving its own widget.
2. Atlas's `with_atlas_panels`, after `evalTacticSeq seq`, calls
   `figureProgressionHookRef`. We register that hook here.
3. The hook walks `seq` to find each tactic's source line, computes
   the cumulative figure for that line (base ++ all auxillaries with
   line ≤ this), renders to Html, saves a widget at that tactic.

Result: cursor on any proof line shows the figure as of that step.
Lines preceding the first auxillary show the base; subsequent lines
show the running stack.
-/

import Atlas
import Figures
import Figures.SVG
import Geometry.Construction.DSL
import Geometry.Construction.Syntax
import Geometry.Construction.Lowering
import Geometry.Construction.AtlasField
import ProofWidgets.Component.HtmlDisplay

namespace Geometry.Construction

open Lean Elab Tactic Meta ProofWidgets Server

structure AuxillaryAddendum where
  line : Nat
  addendum : DSL.Construction
  deriving Inhabited

initialize auxillaryAddendaExt :
    SimplePersistentEnvExtension
      (Name × AuxillaryAddendum)
      (Array (Name × AuxillaryAddendum)) ←
  Atlas.registerArrayExt `Geometry.Construction.auxillaryAddendaExt

/-- Push an auxillary addendum into the per-decl tracking extension. -/
def pushAddendum (declName : Name) (line : Nat) (addendum : DSL.Construction) :
    TermElabM Unit := do
  modifyEnv (auxillaryAddendaExt.addEntry · (declName, { line, addendum }))

/-- All addenda recorded for this decl, in source-push order. -/
private def addendaFor (env : Environment) (declName : Name) :
    Array AuxillaryAddendum :=
  (auxillaryAddendaExt.getState env).filterMap fun (n, a) =>
    if n == declName then some a else none

/-- Recursively collect every Syntax node that has a source position,
ignoring tacticSeq wrapper kinds. Used to identify tactic lines. -/
private partial def collectStepSyntax (stx : Syntax) : Array Syntax :=
  -- Stop descending into atoms / missing nodes; otherwise recurse.
  if stx.getKind == ``Lean.Parser.Tactic.tacticSeq
     || stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented
     || stx.getKind == `null then
    stx.getArgs.foldl (fun acc s => acc ++ collectStepSyntax s) #[]
  else
    match stx with
    | .node _ _ _ => #[stx]
    | _           => #[]

private def wrap (h : Html) : Html :=
  Html.element "div"
    #[("style", Json.str "text-align: center; margin: 0.5em 0;")]
    #[h]

/-- Render a `Construction` to a wrapped Html block (centered, with
margin) for embedding in the InfoView. -/
private def renderConstructionHtml (c : DSL.Construction) :
    TermElabM Html := do
  let svgStr : String := Figures.Renderable.render
    (Lowering.lower c (canvasW := 1280) (canvasH := 720))
  match Atlas.SvgParser.parse svgStr with
  | .ok h => return wrap h
  | .error msg => throwError s!"progressive figure: SVG parse failed: {msg}"

/-- Same as `renderConstructionHtml` but for a base+addendum pair so
addendum constructs render with dashed style. -/
private def renderAuxHtml (base addendum : DSL.Construction) :
    TermElabM Html := do
  let svgStr : String := Figures.Renderable.render
    (Lowering.lowerAuxiliary base addendum (canvasW := 1280) (canvasH := 720))
  match Atlas.SvgParser.parse svgStr with
  | .ok h => return wrap h
  | .error msg => throwError s!"progressive figure: SVG parse failed: {msg}"

/-- Hook implementation: for each tactic line in `seq`, save a panel
widget showing the cumulative figure at that line. -/
private def saveProgressiveFigures (declName : Name) (seq : Syntax) :
    TacticM Unit := do
  let env ← getEnv
  let base? ← getBase
  let some base := base? | return
  let addenda := addendaFor env declName
  let fileMap ← getFileMap
  let steps := collectStepSyntax seq
  for stx in steps do
    let some pos := stx.getPos? | continue
    let line := fileMap.toPosition pos |>.line
    let activeAddenda := addenda.filter (·.line ≤ line)
    let html ←
      if activeAddenda.isEmpty then
        renderConstructionHtml base
      else
        let combinedStmts := activeAddenda.foldl
          (fun acc a => acc ++ a.addendum.stmts) #[]
        renderAuxHtml base { stmts := combinedStmts }
    Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return json% { html: $(← rpcEncode html) })
      stx

initialize do
  Atlas.Refs.figureProgressionHookRef.set saveProgressiveFigures

end Geometry.Construction
