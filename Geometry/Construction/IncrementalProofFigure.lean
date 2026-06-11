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

/-- Per-step hook: fires BEFORE each tactic step inside
`with_atlas_panels` with live TacticM state (current LCtx = entering
state for the step). Saves a figure widget at the step's source
position.

KNOWN LIMITATION: this hook fires at the OUTER step level. For
hypothesis-introducing macros (`clearly`, `by_contra!`, etc.), the
macro hasn't expanded yet at fire time, so hypotheses the macro
introduces internally won't appear in the figure within the macro body.
The post-hoc InfoTree approach would catch these but the trees aren't
populated at the hook's vantage point (verified 2026-06-11 — trees=N
but tacticInfos=0). Macro-internal figures stay out of scope until
either Lean exposes per-step state during elab, or we re-architect via
command-level post-elab hooks. -/
def perStepHook (kind num : String) (stx : Syntax) : TacticM Unit := do
  let env ← getEnv
  if (Atlas.baseIRExprFor env kind num).isSome then return
  try
    withMainContext do
      let goalTy ← (← getMainGoal).getType
      let theoremTy ← match ← Lean.Elab.Term.getDeclName? with
        | some n => pure ((← getEnv).find? n |>.map (·.type))
        | none   => pure none
      let c ← FromProofState.extract
        (goalTy := some goalTy) (theoremTy := theoremTy)
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

/-- Post-hoc fallback: tries an InfoTree walk but the trees aren't
populated at this vantage point so it's currently a no-op. Kept as the
dispatch entry from `ProgressiveFigure` for the day the architecture
supports it. -/
def saveInfoTreeFigures (kind num : String) (_declName : Name) (_seq : Syntax) :
    TacticM Unit := do
  let env ← getEnv
  if (Atlas.baseIRExprFor env kind num).isSome then return
  -- TODO(#100 followup): when Lean exposes mid-elab TacticInfos, walk
  -- them here to catch macro-internal positions.
  pure ()

end Geometry.Construction.IncrementalProofFigure
