/-
Geometry/Construction/IncrementalProofFigure.lean — post-hoc figure
widget for proof-state-driven figures.

After `evalTacticSeq` completes inside `with_atlas_panels`, walk the
populated InfoTree to find every `TacticInfo` node — including those
inside macro expansions (`clearly`, `by_contra!`, etc.). For each, save
a panel widget at the tactic's SURFACE source position with the figure
derived from that step's `goalsBefore` LocalContext.

This replaces the earlier per-step pre-hook, which couldn't see inside
macros because the macro hadn't expanded yet when the hook fired.

Set `set_option geometry.proofFigure.debug true` to render DSL + LCtx
overlays under each figure for diagnosing matcher coverage.
-/

import Geometry.Construction.FromProofState
import Geometry.Construction.Lowering
import Geometry.Construction.Cache
import ProofWidgets.Component.HtmlDisplay
import Atlas

namespace Geometry.Construction.IncrementalProofFigure

open Lean Elab Tactic Meta ProofWidgets Server

register_option geometry.proofFigure.debug : Bool := {
  defValue := false
  descr    := "Render DSL + LCtx debug overlays under each inferred proof-state figure."
}

private def debugBlock (title : String) (body : String) : Html :=
  Html.element "div"
    #[("style", Json.str "margin: 0.25em 0; font-family: monospace; font-size: 0.8em;")]
    #[ Html.element "div"
         #[("style", Json.str "color: #586e75; padding: 0 0 0.15em 0.25em;")]
         #[Html.text title]
     , Html.element "pre"
         #[("style", Json.str "margin: 0; padding: 0.5em; background: #fdf6e3; color: #073642; white-space: pre-wrap;")]
         #[Html.text body] ]

private def formatLCtx : MetaM String := do
  let lctx ← getLCtx
  let mut out : Array String := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← Meta.ppExpr (← instantiateMVars d.type)
    out := out.push s!"{d.userName} : {ty}"
  return String.intercalate "\n" out.toList

private def wrap (children : Array Html) : Html :=
  Html.element "div"
    #[("style", Json.str "text-align: center; margin: 0.5em 0;")]
    children

private def renderConstructionHtml (c : DSL.Construction) (lctxStr : String)
    (debug : Bool) : MetaM Html := do
  let scene ← Figures.Construction.Lowering.lowerM c
    (canvasW := 1280) (canvasH := 720)
  let svgStr : String := Figures.Renderable.render scene
  let (figHtml, parseInfo) ← match Atlas.SvgParser.parse svgStr with
    | .ok h => pure (h, s!"SVG ok ({svgStr.length} bytes)")
    | .error msg => pure (Html.text s!"(no SVG: {msg})", s!"SVG parse error: {msg}")
  if !debug then return wrap #[figHtml]
  let dslView  := debugBlock s!"DSL ({c.stmts.size} stmts) — {parseInfo}" (DSL.printConstruction c)
  let lctxView := debugBlock "LCtx" lctxStr
  let debugPanel : Html := Html.element "div"
    #[("style", Json.str "text-align: left; max-width: 1280px; margin: 0 auto;")]
    #[dslView, lctxView]
  return wrap #[figHtml, debugPanel]

/-- Walk the populated InfoTrees and save a figure widget at each
TacticInfo's source position. Called POST-HOC after `evalTacticSeq`
finishes so the trees include macro-internal steps. -/
def saveInfoTreeFigures (kind num : String) (declName : Name) (_seq : Syntax) :
    TacticM Unit := do
  let env ← getEnv
  -- DSL-figured targets are handled by the ProgressiveFigure post-hoc
  -- hook; skip here.
  if (Atlas.baseIRExprFor env kind num).isSome then return
  let theoremTy : Option Expr := (env.find? declName).map (·.type)
  let fileMap ← getFileMap
  let trees := (← getInfoState).trees.toArray
  -- Collect every TacticInfo node across all trees, paired with its
  -- enclosing ContextInfo.
  let infos := trees.foldl (init := (#[] : Array (ContextInfo × TacticInfo)))
    fun acc t =>
      t.foldInfo (init := acc) fun ctx info acc' =>
        match info with
        | .ofTacticInfo ti => acc'.push (ctx, ti)
        | _ => acc'
  -- Dedup by source line: chained leaf tactics on one line should
  -- only emit one widget at that line.
  let mut seenLines : Std.HashSet Nat := {}
  for (ctx, ti) in infos do
    let some pos := ti.stx.getPos? | continue
    let line := fileMap.toPosition pos |>.line
    if seenLines.contains line then continue
    seenLines := seenLines.insert line
    let some goal := ti.goalsBefore.head? | continue
    let htmlOpt? ← try
      let html ← ctx.runMetaM {} do
        goal.withContext do
          let goalTy ← goal.getType
          let c ← FromProofState.extract
            (goalTy := some goalTy) (theoremTy := theoremTy)
          let debug := geometry.proofFigure.debug.get (← getOptions)
          let lctxStr ← if debug then formatLCtx else pure ""
          renderConstructionHtml c lctxStr debug
      pure (some html)
    catch _ => pure none
    match htmlOpt? with
    | some html =>
      Widget.savePanelWidgetInfo
        (hash HtmlDisplayPanel.javascript)
        (return Json.mkObj [("html", Atlas.htmlToJson html)])
        ti.stx
    | none => pure ()

end Geometry.Construction.IncrementalProofFigure
