/-
Geometry/Construction/IncrementalProofFigure.lean — figure-per-theorem
widget derived from the theorem signature.

For targets WITHOUT a hand-authored `figure := by construction { … }`
block, save ONE panel widget at the proof body's start position
showing the figure inferred from the theorem's full type (Pi binders
+ conclusion). The figure stays the same throughout the proof body —
it illustrates what the theorem CLAIMS, not what's currently in scope.

Incremental per-step updates were explored and shelved (see tasks
#102 / #103): the per-step pre-hook can't see hypothesis-introducing
macros' internals, and the post-hoc InfoTree walker doesn't have
populated trees at this vantage point. The figure-per-theorem
primitive is what works today.

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
  descr    := "Render DSL + LCtx debug overlays under the inferred proof-state figure."
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

private def traceMsg (msg : String) (stx : Syntax) : TacticM Unit := do
  let html : Html := Html.element "div"
    #[("style", Json.str "padding: 0.5em; background: #fdf6e3; color: #073642; font-family: monospace; font-size: 0.85em;")]
    #[Html.text msg]
  Widget.savePanelWidgetInfo
    (hash HtmlDisplayPanel.javascript)
    (return Json.mkObj [("html", Atlas.htmlToJson html)])
    stx

def saveTheoremFigure (_kind _num : String) (_declName : Name) (seq : Syntax)
    (initialGoalTy : Expr) (initialMVar : MVarId) : TacticM Unit := do
  try
    -- Restore the LCtx as it was at proof entry (binder fvars in scope)
    -- via the snapshotted mvar's context. `getLCtx` inside `extract`
    -- then walks all the theorem's premises (distinct, between,
    -- incidence hypotheses, etc.).
    let html ← initialMVar.withContext do
      let c ← FromProofState.extract (goalTy := some initialGoalTy)
      let debug := geometry.proofFigure.debug.get (← getOptions)
      let lctxStr ← if debug then formatLCtx else pure ""
      renderConstructionHtml c lctxStr debug
    Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return Json.mkObj [("html", Atlas.htmlToJson html)])
      seq
  catch _ => pure ()

end Geometry.Construction.IncrementalProofFigure
