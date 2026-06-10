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
      let html ← renderConstructionHtml c
      Widget.savePanelWidgetInfo
        (hash HtmlDisplayPanel.javascript)
        (return Json.mkObj [("html", Atlas.htmlToJson html)])
        stx
  catch _ => pure ()

initialize do
  Atlas.Refs.figureProgressionPerStepHookRef.set perStepHook

end Geometry.Construction.IncrementalProofFigure
