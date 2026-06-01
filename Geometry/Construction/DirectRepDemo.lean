/-
Geometry/Construction/DirectRepDemo.lean — End-to-end smoke test of
the `figure := by direct_rep <term>` field on the new figures stack.

Imports `Geometry.Construction.Pasch` (the hand-coordinated Pasch
`Scene`), declares a stub atlas theorem to serve as the figure's host,
and attaches the scene to that theorem via `direct_rep pasch`. atlas
dispatches via `Figures.Renderable (Scene Pos2) String` and looks up
the SVG backend instance automatically — no `.toSvg` call needed at
the use site. Pipeline:

  giyf Scene → atlas direct_rep (Renderable lookup) →
  Figures.SVG.render → atlas.SvgParser.parse → figure widget

Lake-build green here means the cross-repo wiring works.
-/

import Atlas
import Geometry.Construction.Pasch

open Atlas
open Geometry.Construction.Examples

atlas commentary := by
  via theorem 999.0
  name "direct_rep smoke test"
  preface "Smoke test for `figure := by direct_rep <Scene>` — hands the
hand-coordinated Pasch `Scene` to atlas's `direct_rep` field, which
dispatches polymorphically via `Figures.Renderable α String` to find
the SVG backend instance and produce the figure's SVG body."

  figure := by
    direct_rep pasch
    title "Pasch (direct_rep)"
    index 1
    caption "Hand-coordinated Scene. X lies on segment AB, L passes through X — positions chosen by us, since the geometric DSL that would compute these from declarative constraints isn't built yet."

/-- Stub theorem to host the commentary above. Tactic-mode proof (not
just `:= trivial`) so atlas's `with_atlas_panels` wrapper fires and the
figure appears in the InfoView on the proof side too. -/
atlas theorem 999.0 "direct_rep smoke test placeholder"
  : True := by trivial
