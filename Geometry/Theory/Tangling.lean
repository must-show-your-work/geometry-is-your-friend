import Geometry.Theory.Collinear
import Geometry.Theory.Arrangement
import Geometry.Theory.Arrangement.Lattice

namespace Geometry.Theory

/-- Search space over Arrangements of a set of collinear points. -/
structure Tangling where
  points : Finset Point
  col : Collinear points
  known : Finset ((a : Point) ×' (b : Point) ×' (c : Point) ×' Between a b c)

namespace Tangling

/-- A Tangling of size at least n. Methods like `.arrangements` require ≥ 3. -/
def SizeGe (t : Tangling) (n : Nat) : Prop := t.points.card ≥ n

/-- Add a known Between fact among existing points; refines the search space. -/
noncomputable def addBetween (t : Tangling) {a b c : Point}
    (_ha : a ∈ t.points) (_hb : b ∈ t.points) (_hc : c ∈ t.points)
    (h : a - b - c) : Tangling :=
  { t with known := insert ⟨a, b, c, h⟩ t.known }

/-- Add a new collinear point; expands the search space. -/
noncomputable def weaveIn (t : Tangling) (P : Point)
    (hcol : Collinear (insert P t.points)) : Tangling :=
  { points := insert P t.points, col := hcol, known := t.known }

end Tangling

end Geometry.Theory
