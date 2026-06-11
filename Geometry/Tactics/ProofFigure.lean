/-
Geometry/Tactics/ProofFigure.lean — `proof_figure` tactic.

Drops a figure-widget at the cursor showing the current proof state as
a geometric diagram. Walks the `LocalContext` via
`FromProofState.extract`, lowers the resulting Construction to SVG via
`Lowering.lower`, and attaches a panel widget via the same
`HtmlDisplayPanel` channel the progressive figure widget uses.

V0 scope: explicit tactic invocation. The user writes `proof_figure` at
the position where they want the figure displayed. A future pass can
hook this into every tactic boundary automatically (mirroring the
progressive-figure pipeline).
-/

import Geometry.Construction.FromProofState
import Geometry.Construction.Lowering
import Geometry.Construction.Cache
import ProofWidgets.Component.HtmlDisplay
import Atlas

namespace Geometry.Construction

syntax (name := proofFigureTac) "proof_figure" : tactic

open Lean Meta Elab.Tactic ProofWidgets in
elab_rules : tactic
  | `(tactic| proof_figure) => withMainContext do
    let goalTy ← (← getMainGoal).getType
    let ctor ← FromProofState.extract (goalTy := some goalTy)
    let scene ← Figures.Construction.Lowering.lowerM ctor
      (canvasW := 1280) (canvasH := 720)
    let svgStr : String := Figures.Renderable.render scene
    let figHtml ← match Atlas.SvgParser.parse svgStr with
      | .ok h => pure h
      | .error msg => throwError s!"proof_figure: SVG parse failed: {msg}"
    let html : Html := Html.element "div"
      #[("style", Json.str "text-align: center; margin: 0.5em 0;")]
      #[figHtml]
    Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return Json.mkObj [("html", Atlas.htmlToJson html)])
      (← getRef)

end Geometry.Construction

#allow_unused_tactic! Geometry.Construction.proofFigureTac
