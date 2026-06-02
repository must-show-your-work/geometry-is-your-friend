/-
Geometry/Construction/Tests/LabelStress.lean — stress-test fixtures
for the label-layout sub-solver (Phase D).

Each `atlas commentary` block below is shaped to provoke label-segment
or label-label collisions. The figure widget renders inline in the
InfoView when the cursor is on the commentary — eyeball each one to
confirm the solver kept labels clear of construction lines.

A regression check is at the bottom: `runStressSweep` walks every
fixture, computes the minimum label-to-segment distance, and exits
non-zero if any fixture drops below `passingThreshold`. Invoke with:

  lake env lean --run Geometry/Construction/Tests/LabelStress.lean
-/

import Figures
import Figures.SVG
import Figures.Vec2
import Geometry.Construction.DSL
import Geometry.Construction.Syntax
import Geometry.Construction.Lowering
import Geometry.Construction.AtlasField
import Atlas

open Figures Geometry.Construction.DSL Geometry.Construction.Lowering Atlas

namespace Geometry.Construction.Tests.LabelStress

/-- 5 collinear points: labels on the same side of the line tend to
overlap each other in a row, and the initial canvas-center-outward
heuristic places them ON the line for a purely-horizontal figure. -/
def collinearC : Construction := construction {
  exists A B C D E : Point
  assert between A B C
  assert between B C D
  assert between C D E
  construct segAE := segment A E
}

/-- Triangle ABC with a cevian from A to a point N on segment BC,
plus an interior point M strictly between A and N. The chained
betweens (`B N C` then `A M N`) place M inside the triangle without
two competing projections on the same particle. -/
def interiorC : Construction := construction {
  exists A B C N M : Point
  assert ¬ collinear A B C
  assert between B N C
  assert between A M N
  construct segAB := segment A B
  construct segBC := segment B C
  construct segAC := segment A C
  construct segAN := segment A N
}

/-- Triangle ACE with B on side AC and D on side CE. Two interior
side-points crowd labels at the C-junction; the spring network plus
projections lay out a triangle with subdivided sides. -/
def clusterC : Construction := construction {
  exists A B C D E : Point
  assert ¬ collinear A C E
  assert between A B C
  assert between C D E
  construct segAC := segment A C
  construct segCE := segment C E
  construct segAE := segment A E
}

/-- Two segments AB and CD crossing at an interior point X, plus two
declared Lines L and M both passing through X. The two `between
A X B` and `between C X D` asserts share particle X — the lowering
collapses them into an `intersect2` projection that snaps X to the
line-line intersection in one step. L and M draw at distinct slopes
thanks to the per-line direction cycling. -/
def crossC : Construction := construction {
  exists A B C D X : Point
  exists L M : Line
  assert between A X B
  assert between C X D
  assert incident X L
  assert incident X M
  construct segAB := segment A B
  construct segCD := segment C D
}

/-- Triangle ABC with `¬ collinear A B C` and a Line L defined
entirely via two `incident` asserts on B and C. Exercises both the
multi-incidence path (L drawn through B and C, not by line_through)
and the noncollinear soft force (a no-op here since springs already
keep the triangle non-degenerate, but a regression on this fixture
would catch a future change that breaks either feature). -/
def newConstraintsC : Construction := construction {
  exists A B C : Point
  exists L : Line
  assert ¬ collinear A B C
  assert incident B L
  assert incident C L
  construct segAB := segment A B
  construct segAC := segment A C
}

private def dist (p q : Pos2) : Float :=
  ((p.x - q.x)^2 + (p.y - q.y)^2).sqrt

private def closestOnSegment (a b p : Pos2) : Pos2 :=
  let ab := Pos2.sub b a
  let len2 := Pos2.normSq ab
  if len2 < 1e-9 then a
  else
    let t := (Pos2.dot (Pos2.sub p a) ab) / len2
    let t := min 1.0 (max 0.0 t)
    Pos2.add a (Pos2.smul t ab)

/-- Minimum point-to-segment distance across every (label, visible
segment) pair. Heuristic clearance proxy — values ≥ ~14 typically
read as visually well-separated; ≤ 8 indicates a label crashing the
segment. -/
private def minLabelSegClearance (scene : Scene Pos2) : Float := Id.run do
  let segments : Array (Pos2 × Pos2) := scene.shapes.filterMap fun
    | .segment _ a b _ => some (a, b)
    | .ray _ a b _     => some (a, b)
    | .line _ a b _    => some (a, b)
    | _ => none
  let mut best : Float := 1e9
  for ann in scene.annotations do
    match ann with
    | .label target _ (some off) =>
      let anchor? := scene.shapes.findSome? fun
        | .point id pos _ => if id == target then some pos else none
        | _ => none
      match anchor? with
      | none => pure ()
      | some anchor =>
        let labelPos : Pos2 := (anchor.x + off.x, anchor.y + off.y)
        for (a, b) in segments do
          let d := dist labelPos (closestOnSegment a b labelPos)
          if d < best then best := d
    | _ => pure ()
  return best

def fixtures : List (String × Construction) :=
  [("collinear", collinearC), ("interior", interiorC),
   ("cluster", clusterC), ("cross", crossC),
   ("newConstraints", newConstraintsC)]

/-- Below this many pixels of label-to-segment distance, a label
visibly bleeds into the construction line. Glyphs are ~22px tall and
the SVG `paint-order: stroke` halo extends another 4px each side, so
~12px center-to-segment is the point where the halo starts touching
the line; below that and labels read as on the line. -/
def passingThreshold : Float := 12

def runStressSweep : IO UInt32 := do
  let mut failures : Nat := 0
  for entry in fixtures do
    let fixName := entry.1
    let c := entry.2
    let scene := lower c
    let svg := Renderable.render scene
    IO.FS.writeFile s!"/tmp/stress-{fixName}.svg" svg
    let clearance := minLabelSegClearance scene
    let pass := clearance ≥ passingThreshold
    let tag := if pass then "PASS" else "FAIL"
    IO.println s!"{tag} {fixName}: min label-segment clearance = {clearance}"
    if !pass then failures := failures + 1
  if failures == 0 then return 0 else return 1

/-- Phase E roundtrip: the cached-positions path must produce the
identical Scene as the fresh-solve path. If this ever fails it means
the cache stores positions that don't deterministically round-trip
through the rest of the lowering pipeline. -/
def runCacheRoundtrip : IO UInt32 := do
  let mut failures : Nat := 0
  for entry in fixtures do
    let fixName := entry.1
    let c := entry.2
    let fresh := lower c
    let positions := solvePositions c
    let cached := lower c (cachedPositions := some positions)
    let pointsMatch := fresh.shapes.size == cached.shapes.size
      && (Array.zip fresh.shapes cached.shapes).all fun (a, b) => match a, b with
        | .point ida pa _, .point idb pb _ =>
          ida == idb && (pa.x - pb.x).abs < 0.001 && (pa.y - pb.y).abs < 0.001
        | .segment ida a1 b1 _, .segment idb a2 b2 _ =>
          ida == idb
            && (a1.x - a2.x).abs < 0.001 && (a1.y - a2.y).abs < 0.001
            && (b1.x - b2.x).abs < 0.001 && (b1.y - b2.y).abs < 0.001
        | _, _ => true
    let tag := if pointsMatch then "PASS" else "FAIL"
    IO.println s!"{tag} {fixName}: cached path matches fresh path"
    if !pointsMatch then failures := failures + 1
  if failures == 0 then return 0 else return 1

end Geometry.Construction.Tests.LabelStress

open Geometry.Construction.Tests.LabelStress

/-! ## Inline figures

Each commentary block below renders its fixture in the InfoView so the
label-layout sub-solver can be inspected visually. The theorem numbers
are placeholders — they don't correspond to any real theorem. -/

atlas commentary := by
  via theorem 99.1
  name "Label stress — collinear"
  preface "Five collinear points A-B-C-D-E with the only construct being segment AE. Labels for B, C, D sit ON the line in the warm-start; the segment-repulsion force should push them perpendicular to clear the segment."
  figure := by
    construction {
      exists A B C D E : Point
      assert between A B C
      assert between B C D
      assert between C D E
      construct segAE := segment A E
    }
    title "Collinear"
    index 1
    caption "Five points on segment AE."

atlas commentary := by
  via theorem 99.2
  name "Label stress — triangle with cevian"
  preface "Triangle ABC with a cevian AN to a point N on segment BC, plus an interior point M strictly between A and N. The chained betweens place M inside the triangle without competing projections on the same particle."
  figure := by
    construction {
      exists A B C N M : Point
      assert ¬ collinear A B C
      assert between B N C
      assert between A M N
      construct segAB := segment A B
      construct segBC := segment B C
      construct segAC := segment A C
      construct segAN := segment A N
    }
    title "Triangle with cevian"
    index 1
    caption "M sits interior to ABC via the cevian AN."

atlas commentary := by
  via theorem 99.3
  name "Label stress — triangle with subdivided sides"
  preface "Triangle ACE with B on side AC and D on side CE. Two interior side-points crowd labels at the C-junction; tests labels for points that ride on visible segments."
  figure := by
    construction {
      exists A B C D E : Point
      assert ¬ collinear A C E
      assert between A B C
      assert between C D E
      construct segAC := segment A C
      construct segCE := segment C E
      construct segAE := segment A E
    }
    title "Subdivided triangle"
    index 1
    caption "B and D are interior points on sides AC and CE."

atlas commentary := by
  via theorem 99.5
  name "Label stress — multi-incidence + noncollinear"
  preface "Triangle ABC with `¬ collinear A B C` (soft inverse-area force, a no-op while springs already keep the triangle non-degenerate) and a Line L defined entirely by two `incident` asserts on B and C — no `line_through B C` construct. The multi-incidence path draws L through the first two anchors directly."
  figure := by
    construction {
      exists A B C : Point
      exists L : Line
      assert ¬ collinear A B C
      assert incident B L
      assert incident C L
      construct segAB := segment A B
      construct segAC := segment A C
    }
    title "Multi-incidence + noncollinear"
    index 1
    caption "L is defined by two incidence asserts; triangle ABC has the soft noncollinear guard."

atlas commentary := by
  via theorem 99.4
  name "Label stress — crossing segments and lines"
  preface "Two segments AB and CD meeting at an interior point X, plus two declared Lines L and M both passing through X. The lowering detects the two `between` asserts sharing middle particle X and emits a single line-intersection projection, so X lands exactly at the AB ∩ CD crossing. The per-line direction cycle gives L and M distinct slopes."
  figure := by
    construction {
      exists A B C D X : Point
      exists L M : Line
      assert between A X B
      assert between C X D
      assert incident X L
      assert incident X M
      construct segAB := segment A B
      construct segCD := segment C D
    }
    title "Crossing segments and lines"
    index 1
    caption "AB and CD meet at X; L and M also pass through X at distinct slopes."

def main : IO UInt32 := do
  let a ← runStressSweep
  let b ← runCacheRoundtrip
  return if a == 0 && b == 0 then 0 else 1
