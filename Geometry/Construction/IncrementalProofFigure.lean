/-
Geometry/Construction/IncrementalProofFigure.lean — per-tactic-step
figure widget derived from the proof state.

Registers `Atlas.Refs.figureProgressionPerStepHookRef`. The hook fires
BEFORE each tactic step inside `with_atlas_panels` with live TacticM
state (current LCtx = entering state for the step). For targets WITHOUT
a DSL-authored `construction { … }` figure, the hook extracts a
Construction from the LCtx + goal, lowers + renders, and saves a panel
widget at the step's syntax position.

Targets with a DSL figure skip this hook entirely — the post-hoc DSL
path in `ProgressiveFigure` already covers them.

Set `set_option geometry.proofFigure.debug true` (per-file or per-decl)
to see the inferred DSL + LCtx overlays under each figure — useful when
diagnosing matcher coverage. Default `false` keeps production renderings
(atlas serve, GH Pages) clean.
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
  Html.element "details"
    #[("style", Json.str "margin: 0.25em 0; font-family: monospace; font-size: 0.8em;")]
    #[ Html.element "summary"
         #[("style", Json.str "cursor: pointer; color: #586e75;")]
         #[Html.text title]
     , Html.element "pre"
         #[("style", Json.str "margin: 0.25em 0 0; padding: 0.5em; background: #fdf6e3; color: #073642; white-space: pre-wrap;")]
         #[Html.text body] ]

/-- Format the LCtx as one line per non-implementation-detail decl:
`name : type`. Used in the proof-state debug overlay so we can see what
`extract` had to work with at each step. -/
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
  let positions := Lowering.solvePositions c
  let svgStr : String := Figures.Renderable.render
    (Lowering.lower c (canvasW := 1280) (canvasH := 720)
      (cachedPositions := some positions))
  let figHtml ← match Atlas.SvgParser.parse svgStr with
    | .ok h => pure h
    | .error _ => pure (Html.text "(no SVG)")
  if !debug then return wrap #[figHtml]
  let dslView  := debugBlock s!"DSL ({c.stmts.size} stmts)" (DSL.printConstruction c)
  let lctxView := debugBlock "LCtx" lctxStr
  let debugPanel : Html := Html.element "div"
    #[("style", Json.str "text-align: left; max-width: 1280px; margin: 0 auto;")]
    #[dslView, lctxView]
  return wrap #[figHtml, debugPanel]

/-- Per-step hook implementation: fires BEFORE each tactic step.
Skips if the DSL path owns this target. Otherwise reads the current
LCtx, extracts a Construction, renders, saves a widget at the step's
position. -/
def perStepHook (kind num : String) (stx : Syntax) : TacticM Unit := do
  let env ← getEnv
  if (Atlas.baseIRExprFor env kind num).isSome then return
  try
    withMainContext do
      let goalTy ← (← getMainGoal).getType
      let c ← FromProofState.extract (goalTy := some goalTy)
      let debug := geometry.proofFigure.debug.get (← getOptions)
      let lctxStr ← if debug then formatLCtx else pure ""
      let html ← renderConstructionHtml c lctxStr debug
      Widget.savePanelWidgetInfo
        (hash HtmlDisplayPanel.javascript)
        (return Json.mkObj [("html", Atlas.htmlToJson html)])
        stx
  catch _ => pure ()

initialize do
  Atlas.Refs.figureProgressionPerStepHookRef.set perStepHook

end Geometry.Construction.IncrementalProofFigure
