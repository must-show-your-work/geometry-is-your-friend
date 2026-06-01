/-
Geometry/Construction/Pasch.lean — Pasch's theorem (atlas 3.0, see
Ch3/Prop/Pasch.lean) encoded as a `Figures.Scene`.

This is a HAND-COORDINATED scene: positions are chosen by us so that
the geometric constraints (X between A and B; L incident with X)
visibly hold. The eventual giyf geometric DSL will compile higher-level
syntax (`exists A B C : Point; assert between A X B; …`) into a Scene
like this one — running its own constraint solver to assign positions.
Until then, this is the hand-built reference for the IR + SVG path.

The `Scene.constraints` array carries the symbolic intent as opaque
metadata, so a future GeoGebra backend can pick it up and wire
interactivity (e.g. draggable X constrained to AB). Default SVG
backend ignores `constraints` entirely.
-/

import Figures
import Figures.SVG

namespace Geometry.Construction.Examples

open Figures

/-- Pasch's theorem figure as a 2D scene. Hand-laid:
- `A`, `B`, `C` form a clearly scalene triangle (side lengths
  ~372 / 380 / 340) so the diagram doesn't accidentally suggest
  isoceles/equilateral — Pasch holds for any triangle.
- `BC` is horizontal — a stable visual baseline; good drafting practice.
- `X` lies on segment `AB` (~35% from A toward B).
- `L` passes through `X` at a downward-right slope; SVG renderer
  extends to the canvas edges.

The `Scene.constraints` array records the symbolic relationships
(`between A X B`, `incident X L`, `distinct`, `noncollinear`) as
opaque metadata, available to backends that consume it. -/
def pasch : Scene Pos2 :=
  let A : Pos2 := (220, 60)
  let B : Pos2 := (440, 360)
  let C : Pos2 := (60, 360)
  -- X on segment AB at t = 0.35.
  let X : Pos2 := ⟨A.x + 0.35 * (B.x - A.x), A.y + 0.35 * (B.y - A.y)⟩
  -- Two reference points on L through X; renderer extends to viewport.
  let lDir : Pos2 := (200, 70)
  let L1 : Pos2 := ⟨X.x - lDir.x, X.y - lDir.y⟩
  let L2 : Pos2 := ⟨X.x + lDir.x, X.y + lDir.y⟩
  {
    shapes := #[
      .point   "A" A,
      .point   "B" B,
      .point   "C" C,
      .point   "X" X,
      .segment "segAB" A B,
      .segment "segBC" B C,
      .segment "segAC" A C,
      .line    "L" L1 L2 .bold,
    ]
    annotations := #[
      .label "A" "A",
      .label "B" "B",
      .label "C" "C",
      .label "X" "X",
      .label "L" "L",
    ]
    constraints := #[
      ⟨.app "distinct" [.name "A", .name "B", .name "C"],
        "Three distinct vertices"⟩,
      ⟨.app "¬" [.app "collinear" [.name "A", .name "B", .name "C"]],
        "Vertices not collinear"⟩,
      ⟨.app "between" [.name "A", .name "X", .name "B"],
        "X lies strictly between A and B on segment AB"⟩,
      ⟨.app "incident" [.name "X", .name "L"],
        "X lies on line L"⟩,
    ]
  }

-- SVG dump of the hand-laid scene. Cursor here to preview; pipe
-- through `IO.println` so the SVG renders with real newlines in the
-- InfoView.
#eval IO.println (Renderable.render (out := String) pasch)

end Geometry.Construction.Examples
