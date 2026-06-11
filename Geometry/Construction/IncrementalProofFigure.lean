/-
Geometry/Construction/IncrementalProofFigure.lean — per-tactic-step
figure widget derived from the proof state.

Registers `Atlas.Refs.figureProgressionPerStepHookRef`. The hook fires
BEFORE each tactic step inside `with_atlas_panels` with live TacticM
state (current LCtx = entering state for the step). For targets WITHOUT
a DSL-authored `construction { … }` figure, the hook extracts a
Construction from the LCtx, lowers + renders, and saves a panel widget
at the step's syntax position.

Targets with a DSL figure skip this hook entirely — the post-hoc DSL
path in `ProgressiveFigure` already covers them.

Future work (Joe's `infer` opt-in UX): replace the auto-fallback with
an explicit `inferModeExt` lookup so the user can mix proof-state
derivation with `focus` / caption additions in the figure block.
-/

import Geometry.Construction.FromProofState
import Geometry.Construction.Lowering
import Geometry.Construction.Cache
import ProofWidgets.Component.HtmlDisplay
import Atlas

namespace Geometry.Construction.IncrementalProofFigure

open Lean Elab Tactic Meta ProofWidgets Server

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

private def wrap (h : Html) (debug : Html) : Html :=
  Html.element "div"
    #[("style", Json.str "text-align: center; margin: 0.5em 0;")]
    #[h, debug]

private def renderConstructionHtml (c : DSL.Construction) (lctxStr : String) :
    MetaM Html := do
  let positions := Lowering.solvePositions c
  let svgStr : String := Figures.Renderable.render
    (Lowering.lower c (canvasW := 1280) (canvasH := 720)
      (cachedPositions := some positions))
  let dslStr := DSL.printConstruction c
  let dslView := debugBlock s!"DSL ({c.stmts.size} stmts)" dslStr
  let lctxView := debugBlock "LCtx" lctxStr
  let debug : Html := Html.element "div"
    #[("style", Json.str "text-align: left; max-width: 1280px; margin: 0 auto;")]
    #[dslView, lctxView]
  match Atlas.SvgParser.parse svgStr with
  | .ok h => return wrap h debug
  | .error _ =>
    -- Parse failed — still show the debug info so we can see WHY there
    -- was no figure (e.g. extract produced nothing → Lowering produced
    -- an empty SVG that the parser rejected).
    return wrap (Html.text "(no SVG)") debug

/-- Per-step hook implementation: fires BEFORE each tactic step.
Skips if the DSL path owns this target. Otherwise reads the current
LCtx, extracts a Construction, renders, saves a widget at the step's
position. -/
def perStepHook (kind num : String) (stx : Syntax) : TacticM Unit := do
  let env ← getEnv
  if (Atlas.baseIRExprFor env kind num).isSome then return
  try
    withMainContext do
      let c ← FromProofState.extract
      let lctxStr ← formatLCtx
      let html ← renderConstructionHtml c lctxStr
      Widget.savePanelWidgetInfo
        (hash HtmlDisplayPanel.javascript)
        (return Json.mkObj [("html", Atlas.htmlToJson html)])
        stx
  catch _ => pure ()

initialize do
  Atlas.Refs.figureProgressionPerStepHookRef.set perStepHook

end Geometry.Construction.IncrementalProofFigure
