/-
Geometry/Construction/AtlasTactic.lean — `auxillary` tactic.

Renders a Construction at the current proof point as a widget in the
InfoView. Use for figures that aren't the canonical theorem diagram —
extra rays, intermediate setups, "what if" branches — i.e. the lines
a student would draw on the page when working through the proof.

  example := by
    …
    auxillary {
      exists A B C : Point
      assert distinct A B C
      construct seg := segment A B
    }
    …

Spelling matches Joe's preferred form ("auxillary"). MVP: standalone
body; inheritance/extension flavor is a separate task.
-/

import Figures
import Figures.SVG
import Geometry.Construction.DSL
import Geometry.Construction.Syntax
import Geometry.Construction.Lowering
import Geometry.Construction.AtlasField
import Atlas
import ProofWidgets.Component.HtmlDisplay

namespace Geometry.Construction

open Lean Elab Tactic Meta ProofWidgets Server

syntax (name := auxillaryTac) "auxillary" "{" constructionStmt* "}" : tactic

@[tactic auxillaryTac]
def elabAuxillary : Tactic := fun stx => do
  match stx with
  | `(tactic| auxillary { $stmts:constructionStmt* }) => do
    -- Elaborate the addendum as a Construction value.
    let addendumStx ← `(construction { $stmts:constructionStmt* })
    let addendumExpr ← Term.elabTermAndSynthesize addendumStx none
    let addendum ← unsafe evalExpr DSL.Construction
      (mkConst ``DSL.Construction) addendumExpr
    -- Pull the base construction set during the commentary's
    -- `construction { … }` elab. Without a base, render addendum
    -- alone — the auxillary still works, just no inheritance.
    let base? ← IO.toEIO (fun (e : IO.Error) => Lean.Exception.error stx e.toString)
      getBase
    let scene : Figures.Scene Figures.Pos2 := match base? with
      | some base => Lowering.lowerAuxiliary base addendum
      | none      => Lowering.lower addendum
    let svgStr := Figures.Renderable.render scene
    let svgHtml ← match Atlas.SvgParser.parse svgStr with
      | .ok h => pure h
      | .error msg => throwError s!"auxillary: SVG parse failed: {msg}"
    let wrap := Html.element "div"
      #[("style", Json.str "text-align: center; margin: 0.5em 0;")]
      #[svgHtml]
    Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return json% { html: $(← rpcEncode wrap) })
      stx
  | _ => throwUnsupportedSyntax

end Geometry.Construction
