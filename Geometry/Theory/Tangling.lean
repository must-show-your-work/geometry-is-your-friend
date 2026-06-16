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

end Tangling

end Geometry.Theory
