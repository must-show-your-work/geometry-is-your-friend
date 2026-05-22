import Geometry.Theory.Primitives
import Mathlib.Data.Set.Basic

/-!
# Constructors

Derived geometric objects built on `Point` + `Between`: segments, rays,
extensions, line-through-two-points, and intersections. Each has a `def`
and a surface syntax (`segment A B`, `ray A B`, etc., plus the `the X`
prefixed forms).

The `on` macro_rules are extended here so that `P on segment A B` expands
to `P ∈ Segment A B` and similarly for the other constructors — the bare
`P on L` case lives in `Geometry/Theory/Primitives.lean`.
-/

namespace Geometry.Theory

/- Betweenness lets us define line-parts -/
@[reducible] def Segment (A B : Point) := {C | (A - C - B) ∨ A = C ∨ B = C}
@[reducible] def Extension (A B : Point) := {C | A - B - C ∧ A ≠ C ∧ B ≠ C}
@[reducible] def Ray (A B : Point) := (Segment A B) ∪ (Extension A B)
@[reducible] def LineThrough (A B : Point) := {C | C = A ∨ C = B ∨ A - C - B ∨ A - B - C ∨ C - A - B}

syntax:max "segment " term:max term:max : term
syntax:max "ray " term:max term:max : term
syntax:max "extension " term:max term:max : term
syntax:max "line " term:max term:max : term

syntax:1000 "the " "segment " term:max term:max : term
syntax:1000 "the " "ray " term:max term:max : term
syntax:1000 "the " "extension " term:max term:max : term
syntax:1000 "the " "line " term:max term:max : term

-- Extend the `on` macro_rules (declared in `Primitives.lean`) with the
-- constructor-aware cases.
macro_rules (kind := onNotation)
  | `($P on segment $A $B) => `($P ∈ Segment $A $B)
  | `($P on ray $A $B) => `($P ∈ Ray $A $B)
  | `($P on extension $A $B) => `($P ∈ Extension $A $B)
  | `($P on line $A $B) => `($P ∈ LineThrough $A $B)
  | `($P on $L) => `($P ∈ $L)

-- Macro rules for standalone geometric objects (without "the")
macro_rules
  | `(segment $A $B) => `(Segment $A $B)
  | `(ray $A $B) => `(Ray $A $B)
  | `(extension $A $B) => `(Extension $A $B)
  | `(line $A $B) => `(LineThrough $A $B)
  | `(the segment $A $B) => `(Segment $A $B)
  | `(the ray $A $B) => `(Ray $A $B)
  | `(the extension $A $B) => `(Extension $A $B)
  | `(the line $A $B) => `(LineThrough $A $B)

/-! ## Intersections -/

@[reducible] def Intersects (L M : Line) (X : Point) : Prop := L ∩ M = {X}

/-- Bare form of `L intersects M` — asserts the intersection is non-empty (i.e.
    `L` and `M` share *at least one* point, allowing the "L coincides with M"
    case). Kept as an opaque `def` so the goal stays readable; the unexpander
    below renders this as `L intersects M` in proof states.

    Going from this to a unique intersection point (`L intersects M at X`)
    requires extra work — typically `ref lemma 3.0.1` for lines,
    which uses `line_trichotomy` to rule out coincidence. -/
def IntersectsSome (L M : Set Point) : Prop := Set.Nonempty (L ∩ M)

/-- Extract a point in the intersection from a bare `intersects` hypothesis.
    Note: the returned `X` is *some* shared point, not necessarily a unique one. -/
lemma IntersectsSome.intersection_point {L M : Set Point} (h : IntersectsSome L M)
  : ∃ X, X ∈ L ∩ M := h


-- Syntax for "L intersects M at X" (specific intersection point) and the bare
-- form "L intersects M" asserting a unique shared point exists.
syntax:50 (name := intersectsAt) term:51 " intersects " term:51 " at " term:50 : term
syntax:50 (name := intersectsBare) term:51 " intersects " term:51 : term

macro_rules (kind := intersectsAt)
  | `($L intersects $M at $X) => `(Intersects $L $M $X)

macro_rules (kind := intersectsBare)
  | `($L intersects $M) => `(IntersectsSome $L $M)

-- Pretty-print `IntersectsSome L M` as `L intersects M` so the goal stays readable
@[app_unexpander IntersectsSome]
def IntersectsSome.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $L $M) => `($L intersects $M)
  | _ => throw ()

/-! ## Examples -/

section Examples
variable (A B P : Point) (L M : Line) (X : Point)

example : (P on segment A B) ↔ (P ∈ Segment A B) := Iff.rfl
example : (P on ray A B) ↔ (P ∈ Ray A B) := Iff.rfl
example : (P on extension A B) ↔ (P ∈ Extension A B) := Iff.rfl
example : (P on line A B) ↔ (P ∈ LineThrough A B) := Iff.rfl
example : (segment A B) = Segment A B := rfl
example : (the segment A B) = Segment A B := rfl
example : (L intersects M at X) ↔ (Intersects L M X) := Iff.rfl
example : (L intersects M) ↔ (IntersectsSome L M) := Iff.rfl
end Examples

end Geometry.Theory
