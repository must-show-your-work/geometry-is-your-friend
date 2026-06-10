/-
Geometry/Construction/IncrementalProofFigure.lean — per-tactic-step
figure widget derived from the proof state, no hand-authored DSL
required.

Walks the InfoTree produced by `evalTacticSeq` after `with_atlas_panels`,
finds each tactic step's `goalsBefore`, runs `FromProofState.extract` in
that mvar's local context, lowers + renders, and attaches a panel widget
at the step's syntax position.
-/

import Geometry.Construction.FromProofState
import Geometry.Construction.Lowering
import Geometry.Construction.Cache
import ProofWidgets.Component.HtmlDisplay
import Atlas

namespace Geometry.Construction.IncrementalProofFigure

open Lean Elab Tactic Meta ProofWidgets Server

private def wrap (h : Html) : Html :=
  Html.element "div"
    #[("style", Json.str "text-align: center; margin: 0.5em 0;")]
    #[h]

private def renderConstructionHtml (c : DSL.Construction) : MetaM Html := do
  let positions := Lowering.solvePositions c
  let svgStr : String := Figures.Renderable.render
    (Lowering.lower c (canvasW := 1280) (canvasH := 720)
      (cachedPositions := some positions))
  match Atlas.SvgParser.parse svgStr with
  | .ok h => return wrap h
  | .error msg => throwError s!"proof-state figure: SVG parse failed: {msg}"

private partial def collectStepSyntax (stx : Syntax) : Array Syntax :=
  if stx.getKind == ``Lean.Parser.Tactic.tacticSeq
     || stx.getKind == ``Lean.Parser.Tactic.tacticSeq1Indented
     || stx.getKind == `null then
    stx.getArgs.foldl (fun acc s => acc ++ collectStepSyntax s) #[]
  else
    match stx with
    | .node _ _ _ => #[stx]
    | _           => #[]

/-- Build line → (ContextInfo, TacticInfo) by folding the InfoTrees.
Earliest TacticInfo at each line wins — that's the outermost tactic,
whose `goalsBefore` is the pre-state for that line. -/
private def perLineTacticInfo (fileMap : FileMap) (seq : Syntax)
    (trees : Array InfoTree) :
    Std.HashMap Nat (ContextInfo × TacticInfo) := Id.run do
  let mut m : Std.HashMap Nat (ContextInfo × TacticInfo) := {}
  let some seqStart := seq.getPos? | return m
  let some seqEnd := seq.getTailPos? | return m
  let seqStartLine := fileMap.toPosition seqStart |>.line
  let seqEndLine := fileMap.toPosition seqEnd |>.line
  for tree in trees do
    m := tree.foldInfo (init := m) fun ctx info acc =>
      match info with
      | .ofTacticInfo ti =>
        match ti.stx.getPos? with
        | none => acc
        | some pos =>
          let lineNum := fileMap.toPosition pos |>.line
          if lineNum < seqStartLine || lineNum > seqEndLine then acc
          else if acc.contains lineNum then acc
          else acc.insert lineNum (ctx, ti)
      | _ => acc
  return m

/-- Hook entry point: per-step proof-state figure widgets. -/
def saveProofStateFigures (seq : Syntax) : TacticM Unit := do
  let fileMap ← getFileMap
  let trees := (← getInfoState).trees.toArray
  let perLine := perLineTacticInfo fileMap seq trees
  let mut seenLines : Std.HashSet Nat := {}
  for stx in collectStepSyntax seq do
    let some pos := stx.getPos? | continue
    let lineNum := fileMap.toPosition pos |>.line
    if seenLines.contains lineNum then continue
    seenLines := seenLines.insert lineNum
    let some (ctx, ti) := perLine[lineNum]? | continue
    let some goal := ti.goalsBefore.head? | continue
    let html ← ctx.runMetaM {} do
      goal.withContext do
        let c ← FromProofState.extract
        renderConstructionHtml c
    Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return Json.mkObj [("html", Atlas.htmlToJson html)])
      stx

end Geometry.Construction.IncrementalProofFigure
