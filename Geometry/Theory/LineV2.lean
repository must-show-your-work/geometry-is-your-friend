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

namespace Line

/-- Membership against the chosen Line via Tangling's Collinear witness; the
bound filter is a TODO refinement layered on later. -/
def contains (L : Line) (P : Point) : Prop := P ∈ L.tangling.col.line

instance : Membership Point Line where mem L P := L.contains P

end Line

/-- Trichotomy classifier — every pair of lines is parallel, meets at a unique
point, or coincides. Replaces lemma 2.0.1's Or-disjunction. -/
inductive Trichotomy (L M : Line) : Type where
  | parallel    (h : ∀ P, ¬(L.contains P ∧ M.contains P)) : Trichotomy L M
  | meet (X : Point) (h : ∀ P, (L.contains P ∧ M.contains P) ↔ P = X) : Trichotomy L M
  | coincident  (h : L = M) : Trichotomy L M

/-- L and M share a unique point. -/
def Intersects (L M : Line) (X : Point) : Prop :=
  ∀ P, (L.contains P ∧ M.contains P) ↔ P = X

/-- L and M share no points. -/
def Parallel (L M : Line) : Prop := ∀ P, ¬(L.contains P ∧ M.contains P)

/-- Rays AB and AC are opposite if they're distinct but lie on the same line. -/
def OppositeRay (A B C : Point) (hb : A ≠ B := by assumption)
    (hc : A ≠ C := by assumption) : Prop :=
  mkRay A B hb ≠ mkRay A C hc ∧ mkLine A B hb = mkLine A C hc

/-- ∠ B A C — distinct, non-opposite rays from a common vertex A. -/
def Angle (A B C : Point) (hb : A ≠ B := by assumption)
    (hc : A ≠ C := by assumption) : Prop :=
  distinct A B C ∧ mkRay A B hb ≠ mkRay A C hc ∧ ¬OppositeRay A B C hb hc

end Geometry.Theory.LineV2
