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
import Geometry.Construction.Cache
import Geometry.Construction.AtlasField
import Geometry.Construction.IncrementalProofFigure
import Geometry.Construction.FromProofState
import ProofWidgets.Component.HtmlDisplay

namespace Geometry.Construction

open Lean Elab Tactic Meta ProofWidgets Server

structure AuxillaryAddendum where
  line : Nat
  addendum : DSL.Construction
  -- Optional descriptive caption from `auxillary "..." { ... }`.
  -- Surfaces as accessibility narration in the figure widget and as
  -- a small caption next to the rendered SVG. Future Type→DSL
  -- extraction (Joe 2026-06-02) can also consume this.
  description : Option String := none
  deriving Inhabited

initialize auxillaryAddendaExt :
    SimplePersistentEnvExtension
      (Name × AuxillaryAddendum)
      (Array (Name × AuxillaryAddendum)) ←
  Atlas.registerArrayExt `Geometry.Construction.auxillaryAddendaExt

/-- Push an auxillary addendum into the per-decl tracking extension. -/
def pushAddendum (declName : Name) (line : Nat) (addendum : DSL.Construction)
    (description : Option String := none) :
    TermElabM Unit := do
  modifyEnv (auxillaryAddendaExt.addEntry · (declName, { line, addendum, description }))

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

/-- Look up cached positions for `c`; on miss, run the Rigidity-based
solver, cache the result, and return the freshly-solved positions. -/
private def cachedSolve (c : DSL.Construction) :
    TermElabM (Array (Figures.Name × Figures.Pos2)) := do
  let env ← getEnv
  match Cache.lookup env c with
  | some v => return v
  | none =>
    let positions ← Figures.Construction.Lowering.solvePositionsM c
    Cache.store c positions
    return positions

/-- Optional debug overlay (DSL + LCtx) appended below the figure when
`geometry.proofFigure.debug` is on. `lctxStr` empty ⇒ no LCtx block. -/
private def withDebug (figHtml : Html) (c : DSL.Construction)
    (parseInfo lctxStr : String) (debug : Bool) : Html :=
  if !debug then figHtml else
    let dslView := IncrementalProofFigure.debugBlock
      s!"DSL ({c.stmts.size} stmts) — {parseInfo}" (DSL.printConstruction c)
    let lctxView := IncrementalProofFigure.debugBlock "LCtx" lctxStr
    let debugPanel : Html := Html.element "div"
      #[("style", Json.str "text-align: left; max-width: 1280px; margin: 0 auto;")]
      #[dslView, lctxView]
    Html.element "div"
      #[("style", Json.str "text-align: center; margin: 0.5em 0;")]
      #[figHtml, debugPanel]

/-- Render a `Construction` to a wrapped Html block (centered, with
margin) for embedding in the InfoView. Uses `Geometry.Construction.Cache`
to skip the solver on re-elabs of the same construction. `lctxStr` is
appended as a debug overlay when non-empty. -/
private def renderConstructionHtml (c : DSL.Construction)
    (lctxStr : String := "") (debug : Bool := false) :
    TermElabM Html := do
  let positions ← cachedSolve c
  let svgStr : String := Figures.Renderable.render
    (Lowering.lower c (canvasW := 1280) (canvasH := 720)
      (cachedPositions := some positions))
  match Atlas.SvgParser.parse svgStr with
  | .ok h =>
    let parseInfo := s!"SVG ok ({svgStr.length} bytes)"
    return withDebug (wrap h) c parseInfo lctxStr debug
  | .error msg => throwError s!"progressive figure: SVG parse failed: {msg}"

/-- Same as `renderConstructionHtml` but for a base+addendum pair so
addendum constructs render with dashed style. Cache key is the
concatenation of base + addendum stmts via `lowerAuxiliary`'s
internal `combined` construction. -/
private def renderAuxHtml (base addendum : DSL.Construction)
    (lctxStr : String := "") (debug : Bool := false) :
    TermElabM Html := do
  let combined : DSL.Construction := { stmts := base.stmts ++ addendum.stmts }
  let positions ← cachedSolve combined
  let svgStr : String := Figures.Renderable.render
    (Lowering.lowerAuxiliary base addendum (canvasW := 1280) (canvasH := 720)
      (cachedPositions := some positions))
  match Atlas.SvgParser.parse svgStr with
  | .ok h =>
    let parseInfo := s!"SVG ok ({svgStr.length} bytes)"
    return withDebug (wrap h) combined parseInfo lctxStr debug
  | .error msg => throwError s!"progressive figure: SVG parse failed: {msg}"

/-- Hook implementation: for each tactic line in `seq`, save a panel
widget showing the cumulative figure at that line. -/
private def traceMsg (msg : String) (stx : Syntax) : TacticM Unit := do
  let html : Html := Html.element "div"
    #[("style", Json.str "padding: 0.5em; background: #fdf6e3; color: #073642; font-family: monospace; font-size: 0.85em;")]
    #[Html.text msg]
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return Json.mkObj [("html", Atlas.htmlToJson html)])
    stx

def saveProgressiveFigures
    (kind num : String) (declName : Name) (seq : Syntax)
    (initialGoalTy : Expr) (initialMVar : MVarId) :
    TacticM Unit := do
  let env ← getEnv
  let some baseExpr := Atlas.baseIRExprFor env kind num
    | IncrementalProofFigure.saveTheoremFigure kind num declName seq
        initialGoalTy initialMVar
  let baseExprEvaled ← unsafe Meta.evalExpr Figures.Construction.DSL.Construction
    (mkConst ``Figures.Construction.DSL.Construction) baseExpr
  let addenda := addendaFor env declName
  -- Infer-marker base with NO auxillaries: nothing for the progressive
  -- loop to track — render once via saveTheoremFigure (single static
  -- widget, preserves the debug-overlay path).
  if baseExprEvaled.isInfer ∧ addenda.isEmpty then
    IncrementalProofFigure.saveTheoremFigure kind num declName seq
      initialGoalTy initialMVar
    return
  -- For an infer base WITH auxillaries, replace base with the
  -- proof-state-inferred construction so the auxillary stack overlays
  -- on top of the same shapes the theorem signature implies.
  let base ←
    if baseExprEvaled.isInfer then
      initialMVar.withContext do
        FromProofState.extract (goalTy := some initialGoalTy)
    else
      pure baseExprEvaled
  let debug := IncrementalProofFigure.geometry.proofFigure.debug.get (← getOptions)
  let lctxStr ← if debug ∧ baseExprEvaled.isInfer then
    initialMVar.withContext IncrementalProofFigure.formatLCtx
  else
    pure ""
  let fileMap ← getFileMap
  let scopes := collectScopes seq
  let steps := collectStepSyntax seq
  -- Dedup by source line: chained leaf tactics on one line (e.g.
  -- `· contrapose!; intro _; exact ConL`) would otherwise each emit
  -- an identical figure widget. Save once per line; subsequent leaf
  -- tactics on that line are skipped.
  let mut seenLines : Std.HashSet Nat := {}
  for stx in steps do
    let some pos := stx.getPos? | continue
    let line := fileMap.toPosition pos |>.line
    if seenLines.contains line then continue
    seenLines := seenLines.insert line
    -- Scope-aware filter: an auxillary is in scope iff its enclosing
    -- `tacticSeq` contains the current step's enclosing `tacticSeq`
    -- (i.e. they share lexical lineage), AND the aux was declared at
    -- or before this step.
    let activeAddenda := addenda.filter fun a =>
      inScope scopes fileMap a.line line
    let figHtml ←
      if activeAddenda.isEmpty then
        renderConstructionHtml base lctxStr debug
      else
        let combinedStmts := activeAddenda.foldl
          (fun acc a => acc ++ a.addendum.stmts) #[]
        renderAuxHtml base { stmts := combinedStmts } lctxStr debug
    -- Concatenate descriptions from the active addenda — each
    -- `auxillary "desc" { … }` contributes a small italic caption
    -- under the figure. Empty list ⇒ no captions, no extra DOM.
    let captions : Array String :=
      activeAddenda.filterMap (·.description)
    let html : Html := if captions.isEmpty then figHtml else
      Html.element "div"
        #[("style", Json.str "text-align: center;")]
        (#[figHtml] ++ captions.map (fun c =>
          Html.element "div"
            #[("style", Json.str
                "font-style: italic; color: var(--ink-muted, #586e75); margin-top: 0.25em; font-size: 0.85em;")]
            #[Html.text c]))
    Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return Json.mkObj [("html", Atlas.htmlToJson html)])
      stx

initialize do
  Atlas.Refs.figureProgressionHookRef.set saveProgressiveFigures

end Geometry.Construction
