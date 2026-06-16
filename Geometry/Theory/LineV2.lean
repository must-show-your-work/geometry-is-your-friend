import Geometry.Theory.Tangling
import Geometry.Theory.Interpendices.A

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

/-- The unbounded line through two distinct points. -/
noncomputable def mkLine (A B : Point) (h : A ≠ B := by assumption) : Line :=
  { tangling := { points := {A, B}, col := via lemma 1.0.5 h, known := ∅ },
    leftBound := none, rightBound := none }

/-- The ray from A through B, closed at A, unbounded past B. -/
noncomputable def mkRay (A B : Point) (h : A ≠ B := by assumption) : Line :=
  { tangling := { points := {A, B}, col := via lemma 1.0.5 h, known := ∅ },
    leftBound := some A, rightBound := none }

/-- The closed segment between A and B. -/
noncomputable def mkSegment (A B : Point) (h : A ≠ B := by assumption) : Line :=
  { tangling := { points := {A, B}, col := via lemma 1.0.5 h, known := ∅ },
    leftBound := some A, rightBound := some B }

end Geometry.Theory.LineV2
