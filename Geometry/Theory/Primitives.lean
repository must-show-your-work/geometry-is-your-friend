import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs

/-!
# Primitives

Foundational opaque types and the universal relations / notations that the
rest of the theory layers over: `Point`, `Line` (as a set of points), the
`on` / `off` / `has` / `avoids` membership family, and the bare `Between`
relation with its `-` infix notation.

Everything here is type/relation *declaration* — no axioms about how these
behave. The axioms about incidence live in `Geometry/Theory/Axioms/Incidence.lean`;
the axioms about betweenness live in `Geometry/Theory/Axioms/Betweenness.lean`.
-/

namespace Geometry.Theory

/-- A point is the fundamental, opaque type we're working with. -/
axiom Point : Type

/-- Greenberg reasons classically throughout. Granting decidable equality on `Point`
    via `Classical.decEq` lets us use `Finset Point` and the associated decidable
    membership/cardinality machinery. -/
noncomputable instance : DecidableEq Point := Classical.decEq Point

/-- Ed: In the text, the author ends up using the 'Line is a Set of points' to define segments, rays, and implicitly
uses the intuitive idea ("A line is the set of collinear points that contain at least two known points"). However, Ch2
uses an opaque 'Line' type and reasons only about it's properties without definition. I try to replicate this in my
implementation of Ch2, but do define it as a set 'up front' -/
@[reducible] def Line := Set Point

-- TODO: Review binding values for all this notation
syntax:50 (name := onNotation) term:51 " on " term:50 : term

-- Macro rules for "on" notation — start with the bare `P on L` case; the
-- segment/ray/extension/line cases are added in `Geometry/Theory/Constructors.lean`.
macro_rules (kind := onNotation)
  | `($P on $L) => `($P ∈ $L)

notation:80 P:81 " off " L:81 => P ∉ L
notation:80 L:81 " has " P:81 => P ∈ L
notation:80 L:81 " avoids " P:81 => P ∉ L

/-! ## Betweenness primitive -/

/-- Bare betweenness relation. Axioms about its behavior live in
    `Geometry/Theory/Axioms/Betweenness.lean`. -/
axiom Between : Point -> Point -> Point -> Prop
-- Ed: In the text, the author uses `*`, but Lean reserves that, so I've chosen `-`. `∗` is available, but I don't want
-- to type `\ast` every time.
notation:65 A:66 " - " B:66 " - " C:65 => Between A B C

/-! ## Examples -/

section Examples
variable (P : Point) (L : Line) (A B C : Point)

example : (P on L) ↔ (P ∈ L) := Iff.rfl
example : (P off L) ↔ (P ∉ L) := Iff.rfl
example : (L has P) ↔ (P ∈ L) := Iff.rfl
example : (L avoids P) ↔ (P ∉ L) := Iff.rfl
example : (A - B - C) ↔ Between A B C := Iff.rfl
end Examples

end Geometry.Theory
