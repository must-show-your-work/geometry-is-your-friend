import Geometry.Theory.Primitives
import Mathlib.Data.Set.Basic

/-!
# Constructors

Derived geometric objects built on `Point` + `Between`: segments, rays,
extensions, line-through-two-points, and intersections. Each line-part is
a typed `structure` parameterized by its defining points, with a
`@[reducible]` `carrier : Set Point` projection holding the underlying
disjunction-set Greenberg's original defs used.

`Membership Point X` and `CoeHead X (Set Point)` instances let these
behave transparently as sets — `P ∈ segment A B` and `segment A B ⊆ line A B`
work without manual coercion.

The surface syntax (`segment A B`, `ray A B`, etc., plus the `the X`
prefixed forms) is unchanged from the original Set-Point-based defs;
only the underlying types differ. The `on` macro_rules expand
`P on segment A B` to `P ∈ (segment A B)`.
-/

namespace Geometry.Theory

/-! ## Typed line-part structures

    Each structure carries a `Unit` token to keep it in `Type` (Lean's
    structure-is-Prop rule would otherwise fire on an empty record).
    Endpoints are *type-level* parameters, not fields — recoverable by
    unification at use sites.
-/

structure Segment (A B : Point) where
  type_token : Unit := ()

structure Ray (A B : Point) where
  type_token : Unit := ()

structure Extension (A B : Point) where
  type_token : Unit := ()

structure LineThrough (A B : Point) where
  type_token : Unit := ()

@[inline] def Segment.between (A B : Point) : Segment A B := ⟨()⟩
@[inline] def Ray.from_ (A B : Point) : Ray A B := ⟨()⟩
@[inline] def Extension.past (A B : Point) : Extension A B := ⟨()⟩
@[inline] def LineThrough.through (A B : Point) : LineThrough A B := ⟨()⟩

/-! ## Carriers — projection to `Set Point`

    Reducible defs that unfold to the same set-theoretic content as
    Greenberg's original `Segment`/`Ray`/`Extension`/`LineThrough`. The
    bodies are *literally* the old definitions — no semantic shift.
-/

@[reducible] def Segment.carrier {A B : Point} (_s : Segment A B) : Set Point :=
  {C | (A - C - B) ∨ A = C ∨ B = C}

@[reducible] def Extension.carrier {A B : Point} (_e : Extension A B) : Set Point :=
  {C | A - B - C ∧ A ≠ C ∧ B ≠ C}

@[reducible] def Ray.carrier {A B : Point} (_r : Ray A B) : Set Point :=
  {C | (A - C - B) ∨ A = C ∨ B = C} ∪ {C | A - B - C ∧ A ≠ C ∧ B ≠ C}

@[reducible] def LineThrough.carrier {A B : Point} (_L : LineThrough A B) : Set Point :=
  {C | C = A ∨ C = B ∨ A - C - B ∨ A - B - C ∨ C - A - B}

/-! ## Membership instances -/

instance {A B : Point} : Membership Point (Segment A B) where
  mem s P := P ∈ s.carrier

instance {A B : Point} : Membership Point (Ray A B) where
  mem r P := P ∈ r.carrier

instance {A B : Point} : Membership Point (Extension A B) where
  mem e P := P ∈ e.carrier

instance {A B : Point} : Membership Point (LineThrough A B) where
  mem L P := P ∈ L.carrier

/-! ## `CoeHead` instances — typed line-parts behave as `Set Point` -/

instance {A B : Point} : CoeHead (Segment A B) (Set Point) where
  coe s := s.carrier

instance {A B : Point} : CoeHead (Ray A B) (Set Point) where
  coe r := r.carrier

instance {A B : Point} : CoeHead (Extension A B) (Set Point) where
  coe e := e.carrier

instance {A B : Point} : CoeHead (LineThrough A B) (Set Point) where
  coe L := L.carrier

/-! ## Cross-type subset is via explicit `(↑x : Set Point)` ascription.

    `HasSubset` is a unary typeclass — same type both sides — so writing
    `ray A B ⊆ line A B` (different typed structures) doesn't elaborate.
    The `CoeHead X (Set Point)` instances above let call sites coerce
    explicitly: `(↑(ray A B) : Set Point) ⊆ line A B` (or the symmetric
    ascription on the RHS). Affects only the few subset-between-line-parts
    lemmas (1.0.18, 2.0.5); the typical `P on x` / `s ≠ L` use cases work
    without ascription.
-/

/-! ## `mem_def` bridges — `Iff.rfl` to the underlying disjunction

    Tagged `@[simp, obvious]` so tactics see through to the same shape
    Greenberg's set-based defs exposed directly.
-/

@[simp, obvious] theorem Segment.mem_def {A B : Point} {s : Segment A B} {P : Point} :
  P ∈ s ↔ (A - P - B) ∨ A = P ∨ B = P := Iff.rfl

@[simp, obvious] theorem Ray.mem_def {A B : Point} {r : Ray A B} {P : Point} :
  P ∈ r ↔ ((A - P - B) ∨ A = P ∨ B = P) ∨ (A - B - P ∧ A ≠ P ∧ B ≠ P) := Iff.rfl

@[simp, obvious] theorem Extension.mem_def {A B : Point} {e : Extension A B} {P : Point} :
  P ∈ e ↔ A - B - P ∧ A ≠ P ∧ B ≠ P := Iff.rfl

@[simp, obvious] theorem LineThrough.mem_def {A B : Point} {L : LineThrough A B} {P : Point} :
  P ∈ L ↔ P = A ∨ P = B ∨ A - P - B ∨ A - B - P ∨ P - A - B := Iff.rfl

/-! ## Surface syntax — unchanged from the Set-Point era -/

syntax:max "segment " term:max term:max : term
syntax:max "ray " term:max term:max : term
syntax:max "extension " term:max term:max : term
syntax:max "line " term:max term:max : term

syntax:1000 "the " "segment " term:max term:max : term
syntax:1000 "the " "ray " term:max term:max : term
syntax:1000 "the " "extension " term:max term:max : term
syntax:1000 "the " "line " term:max term:max : term

-- Extend the `on` macro_rules (declared in `Primitives.lean`) — surface
-- shape unchanged, expansion now targets `Membership.mem` on the typed
-- value (`Segment.between A B` etc.).
macro_rules (kind := onNotation)
  | `($P on segment $A $B) => `($P ∈ Segment.between $A $B)
  | `($P on ray $A $B) => `($P ∈ Ray.from_ $A $B)
  | `($P on extension $A $B) => `($P ∈ Extension.past $A $B)
  | `($P on line $A $B) => `($P ∈ LineThrough.through $A $B)
  | `($P on $L) => `($P ∈ $L)

-- Standalone constructors (and `the X` forms) elaborate to typed values.
macro_rules
  | `(segment $A $B) => `(Segment.between $A $B)
  | `(ray $A $B) => `(Ray.from_ $A $B)
  | `(extension $A $B) => `(Extension.past $A $B)
  | `(line $A $B) => `(LineThrough.through $A $B)
  | `(the segment $A $B) => `(Segment.between $A $B)
  | `(the ray $A $B) => `(Ray.from_ $A $B)
  | `(the extension $A $B) => `(Extension.past $A $B)
  | `(the line $A $B) => `(LineThrough.through $A $B)

/-! ## Intersections -/

@[reducible] def Intersects (L M : Set Point) (X : Point) : Prop := L ∩ M = {X}

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

/-- Forget the witness: `L intersects M at X` ⇒ `L intersects M`. Use via dot
    notation as `h.bare` at call sites where the bare (witness-free) form is
    expected. -/
theorem Intersects.bare {L M : Set Point} {X : Point}
  (h : Intersects L M X) : IntersectsSome L M :=
  ⟨X, by rw [h]; rfl⟩

/-- Bare intersection is symmetric. Tagged `@[symm]` so the `symm` tactic picks
    it up; `h.symm` works via dot notation. -/
@[symm] theorem IntersectsSome.symm {L M : Set Point}
  (h : IntersectsSome L M) : IntersectsSome M L := by
  obtain ⟨X, hL, hM⟩ := h
  exact ⟨X, hM, hL⟩


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

example : (P on segment A B) ↔ (P ∈ Segment.between A B) := Iff.rfl
example : (P on ray A B) ↔ (P ∈ Ray.from_ A B) := Iff.rfl
example : (P on extension A B) ↔ (P ∈ Extension.past A B) := Iff.rfl
example : (P on line A B) ↔ (P ∈ LineThrough.through A B) := Iff.rfl
example : (segment A B) = Segment.between A B := rfl
example : (the segment A B) = Segment.between A B := rfl
example : (L intersects M at X) ↔ (Intersects L M X) := Iff.rfl
example : (L intersects M) ↔ (IntersectsSome L M) := Iff.rfl

-- `symm` tactic + dot notation for the bare intersection.
example {L M : Set Point} (h : L intersects M) : M intersects L := by symm; exact h
example {L M : Set Point} (h : L intersects M) : M intersects L := h.symm
end Examples

end Geometry.Theory
