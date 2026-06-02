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

/-- Deep-search for any nested `tacticSeq` within a syntax tree.
Used to identify whether a tactic contains a sub-tactic block (e.g.
the `·` case tactic wraps a `tacticSeq`). -/
private partial def findNestedTacticSeqs (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Lean.Parser.Tactic.tacticSeq
     || stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
    #[stx]
  else
    stx.getArgs.foldl (fun acc s => acc ++ findNestedTacticSeqs s) #[]

/-- Collect tactic steps to attach widgets at. Recurses into nested
`tacticSeq` blocks (so `·` case bodies are walked) but does NOT save
a widget at a tactic that wraps a nested block — only the innermost
tactics get widgets. Otherwise the outer wrapper (`·`) and its inner
tactics would both be active at the same cursor position, stacking
duplicate identical widgets. -/
private partial def collectStepSyntax (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Lean.Parser.Tactic.tacticSeq
     || stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented
     || stx.getKind == `null then
    stx.getArgs.foldl (fun acc s => acc ++ collectStepSyntax s) #[]
  else
    let nestedSeqs := stx.getArgs.foldl
      (fun acc s => acc ++ findNestedTacticSeqs s) #[]
    if nestedSeqs.isEmpty then
      match stx with
      | .node _ _ _ => #[stx]
      | _           => #[]
    else
      nestedSeqs.foldl (fun acc s => acc ++ collectStepSyntax s) #[]

/-- Collect every `tacticSeq`-kind node in the proof tree. Each is a
"scope" — a block of tactics that share lexical visibility. The
top-level seq + each `· …` case body each appear here. -/
private partial def collectScopes (stx : Syntax) : Array Syntax :=
  let here : Array Syntax :=
    if stx.getKind == ``Lean.Parser.Tactic.tacticSeq
       || stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented then
      #[stx]
    else
      #[]
  here ++ stx.getArgs.foldl (fun acc s => acc ++ collectScopes s) #[]

/-- Smallest scope containing the given line (the innermost enclosing
`tacticSeq`). Returns its source range as (startLine, endLine). -/
private def enclosingScope (scopes : Array Syntax) (fileMap : FileMap)
    (line : Nat) : Option (Nat × Nat) :=
  scopes.filterMap (fun s => do
    let p1 ← s.getPos?
    let p2 ← s.getTailPos?
    let l1 := fileMap.toPosition p1 |>.line
    let l2 := fileMap.toPosition p2 |>.line
    if l1 ≤ line && line ≤ l2 then some (l1, l2) else none)
  |>.foldl (init := none) fun best cur =>
    match best with
    | none => some cur
    | some b => if cur.2 - cur.1 < b.2 - b.1 then some cur else some b

/-- Scope-aware in-scope test: an auxillary at line `auxLine` is in
scope at `stepLine` iff the auxillary's enclosing scope contains the
step's enclosing scope AND `auxLine ≤ stepLine`. -/
private def inScope (scopes : Array Syntax) (fileMap : FileMap)
    (auxLine stepLine : Nat) : Bool :=
  if auxLine > stepLine then false
  else
    match enclosingScope scopes fileMap auxLine, enclosingScope scopes fileMap stepLine with
    | some (aL1, aL2), some (sL1, sL2) =>
      -- Aux scope contains step scope ↔ aux range covers step range.
      aL1 ≤ sL1 && sL2 ≤ aL2
    | _, _ => false

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
private def saveProgressiveFigures
    (kind num : String) (declName : Name) (seq : Syntax) :
    TacticM Unit := do
  let env ← getEnv
  -- Look up the base IR Expr by (kind, num) and evaluate as a
  -- Construction value. Per-target keying means corollaries without
  -- their own `construction { … }` get no base (and therefore no
  -- figure widgets) — no leakage from neighboring theorems.
  let some baseExpr := Atlas.baseIRExprFor env kind num | return
  let base ← unsafe Meta.evalExpr DSL.Construction
    (mkConst ``DSL.Construction) baseExpr
  let addenda := addendaFor env declName
  let fileMap ← getFileMap
  let scopes := collectScopes seq
  let steps := collectStepSyntax seq
  for stx in steps do
    let some pos := stx.getPos? | continue
    let line := fileMap.toPosition pos |>.line
    -- Scope-aware filter: an auxillary is in scope iff its enclosing
    -- `tacticSeq` contains the current step's enclosing `tacticSeq`
    -- (i.e. they share lexical lineage), AND the aux was declared at
    -- or before this step.
    let activeAddenda := addenda.filter fun a =>
      inScope scopes fileMap a.line line
    let html ←
      if activeAddenda.isEmpty then
        renderConstructionHtml base
      else
        let combinedStmts := activeAddenda.foldl
          (fun acc a => acc ++ a.addendum.stmts) #[]
        renderAuxHtml base { stmts := combinedStmts }
    Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return Json.mkObj [("html", Atlas.htmlToJson html)])
      stx

initialize do
  Atlas.Refs.figureProgressionHookRef.set saveProgressiveFigures

end Geometry.Construction
