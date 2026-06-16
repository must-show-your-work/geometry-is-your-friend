import Geometry.Theory.Tangling

namespace Geometry.Theory.LineV2

open Geometry.Theory

/-- A line, ray, or segment. Wraps a Tangling (search space of arrangements
on the underlying collinear point set) plus optional closed bounds. -/
structure Line where
  tangling : Tangling
  leftBound : Option Point
  rightBound : Option Point

namespace Line

/-- Bound points are members of the underlying tangling. -/
def Wf (L : Line) : Prop :=
  (∀ P, L.leftBound = some P → P ∈ L.tangling.points) ∧
  (∀ P, L.rightBound = some P → P ∈ L.tangling.points)

end Line

end Geometry.Theory.LineV2
