/- The core geometric theory presented in the text is contained here as simple structures/axia taken as needed into
proofs. -/

import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.List.Basic

import Geometry.Theory.Distinct

namespace Geometry.Theory

/-- A point is the fundamental, opaque type we're working with. -/
axiom Point : Type

/-- Ed: In the text, the author ends up using the 'Line is a Set of points' to define segments, rays, and implicitly
uses the intuitive idea ("A line is the set of collinear points that contain at least two known points"). However, Ch2
uses an opaque 'Line' type and reasons only about it's properties without definition. I try to replicate this in my
implementation of Ch2, but do define it as a set 'up front' -/
@[reducible] def Line := Set Point

-- TODO: Review binding values for all this notation
syntax:50 (name := onNotation) term:51 " on " term:50 : term

-- Macro rules for "on" notation - we need to specify these rules incrementally, so that
-- I can introduce collinear as a definition.
macro_rules (kind := onNotation)
  | `($P on $L) => `($P ∈ $L)


---- COLLINEARITY (FINITE) AND POINTWISE (INFINITE)

-- Collinear: finite list of points on a common line
def Collinear (points : List Point) : Prop := ∃ L : Line, ∀ p ∈ points, p ∈ L

-- Syntax: collinear A B C (space-separated)
syntax "collinear" ident+ : term

macro_rules
  | `(collinear $xs*) => `(Collinear [$xs,*])

-- Pretty printer
open Lean in
@[app_unexpander Collinear]
def unexpandCollinear : PrettyPrinter.Unexpander
  | `(Collinear [$[$xs],*]) => do
    let ids := xs.map (⟨·.raw⟩ : TSyntax `term → TSyntax `ident)
    `(collinear $ids*)
  | _ => throw ()

-- Extract the line from collinearity
noncomputable def Collinear.line {points : List Point} (h : Collinear points) : Line := Classical.choose h

lemma Collinear.on_line {points : List Point} (h : Collinear points) : ∀ p ∈ points, p on h.line := Classical.choose_spec h

@[simp] lemma Collinear.mem {points : List Point} (h : Collinear points) (p : Point) (hp : p ∈ points := by simp) :
  p on h.line := h.on_line p hp

example : collinear A B C ↔ ∃ L : Line, A on L ∧ B on L ∧ C on L := by
  constructor
  · intro colABC; use colABC.line;
    exact ⟨colABC.mem A, colABC.mem B, colABC.mem C⟩
  · rintro ⟨L, AonL, BonL, ConL⟩
    use L
    intro P PinABC
    -- FIXME: I dislike that this is necessary, but I don't have a way of `rcases`-ing my way through the list membership
    simp only [List.mem_cons, List.not_mem_nil, or_false] at PinABC
    rcases PinABC with eq | eq | eq
    repeat rwa [eq]

---- END COLLINEARITY

notation:80 P " off " L => P ∉ L
notation:80 L " has " P => P ∈ L
notation:80 L " avoids " P => P ∉ L

-- -- GEOMETRIC AXIOMS

-- -- -- INCIDENCE GEOMETRY

-- p. 69-70, Ed. The author provides these as very terse statements, I've tried to give informal
-- respellings as documentation.
/--
For any two distinct points P and Q, there exists a unique line L which has P and Q
-/
@[simp] axiom I1 : ∀ P Q : Point, P ≠ Q -> ∃! L : Line, (P on L) ∧ (Q on L)
/-- For any line, there are at least two distinct points on it -/
@[simp] axiom I2 : ∀ L : Line, ∃ A B : Point, A ≠ B ∧ (A on L) ∧ (B on L)
/-- There exists three distinct points not on any single line ("There exists
three non-collinear points", but without mentioning the undefined notion of collinearity) -/
@[simp] axiom I3 : ∃ A B C : Point, (A ≠ B ∧ A ≠ C ∧ B ≠ C) ∧ (∀ (L : Line), (A on L) → (B on L) → (C off L))

/--
p.70 "Three ... lines ... are _concurrent_ if there exists a point incident with all of them"

Ed. Author technically makes this apply to any number of lines, if it ever comes up maybe it's worth
a refactor to any finite set of lines?
-/
@[reducible] def Concurrent (L M N : Line) : Prop :=
    ∃ P : Point, (P on L) ∧ (P on M) ∧ (P on N)

/--
p. 20, "Two lines `l` and `m` are parallel if they do not intersect, i.e., if no point lies on both
of them. We denote this by `l ‖ m`"

p. 70, "Lines `l` and `m` are _parallel_ if they are distinct lines and no point is incident to both
of them."

Ed. This gets defined twice, the definitions are equivalent
-/
@[reducible] def Parallel (L M : Line) : Prop := L ≠ M ∧ ∀ P : Point, ¬((P on L) ∧ (P on M))

notation:20 L " ∥ " M => Parallel L M
notation:20 L " ∦ " M => ¬(Parallel L M)


/- BETWEENNESS GEOMETRY -/

axiom Between : Point -> Point -> Point -> Prop
-- Ed: In the text, the author uses `*`, but Lean reserves that, so I've chosen `-`. `∗` is available, but I don't want
-- to type `\ast` every time.
notation:65 A:66 " - " B:66 " - " C:65 => Between A B C
-- Segment, Ray, Extension, LineThrough

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

-- Re-running
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



/--
p.108a "If A - B - C, then A,B,C are distinct points on the same line...
-/
@[simp] axiom B1a {A B C : Point} : A - B - C -> distinct A B C ∧ collinear A B C


/--
p.108b ... and [A - B - C iff] C - B - A.""

Ed. Note, I separated these parts of the axiom to make rewriting
a bit easier. The author even notes, "The second part (C * B * A) makes the obvious remark
that 'betwen A and C' means the same as 'between C and A'" Making it a separate axiom means
I won't have to dig it out of the pile of parts that is 1a.
-/
@[simp] axiom B1b {A B C : Point} : A - B - C ↔ C - B - A


/--
p.108 "Given any two distinct points B and D, there exist points A, C, and E lying on →ₗBD such that
A * B * D, B * C * D, and B * D * E".

Ed. I like to call this the 'density' axiom because, used recursively, it posits
something like the density of rationals -- for any two distinct points on a
line, there is always a point between them.
-/
@[simp] axiom B2 : ∀ B D : Point, B ≠ D ->
  ∃ A C E : Point, collinear A B C D E ∧ distinct A B C D E ∧ (A - B - D) ∧ (B - C - D) ∧ (B - D - E)


/-- Construct a point 'to the left' of points BD on the induced line B D -/
lemma B2.left : ∀ B D : Point, B ≠ D -> ∃ A : Point, collinear A B D ∧ distinct A B D ∧ (A - B - D) := by
      intro B D BneD
      have ⟨A, _, _, colABCDE, distinctABCDE, ABD, _, _⟩ := B2 B D BneD
      use A
      simp_all only [ne_eq, B1b, B1a, and_self]

/-- Construct a point 'in between' points BD on the induced line B D -/
lemma B2.center : ∀ B D : Point, B ≠ D -> ∃ C : Point, collinear B C D ∧ distinct B C D ∧ (B - C - D) := by
      intro B D BneD
      have ⟨_, C, _, colABCDE, distinctABCDE, _, BCD, _⟩ := B2 B D BneD
      use C
      simp_all only [ne_eq, B1b, B1a, and_self]


/-- Construct a point 'to the right' points BD on the induced line B D -/
lemma B2.right : ∀ B D : Point, B ≠ D -> ∃ E : Point, collinear B D E ∧ distinct B D E ∧ (B - D - E) := by
      intro B D BneD
      have ⟨_, _, E, colABCDE, distinctABCDE, _, _, BDE⟩ := B2 B D BneD
      use E
      simp_all only [ne_eq, B1b, B1a, and_self]

-- lemma B2.center
-- lemma B2.right

/-- p.108 "If A, B, and C are three distinct points lying on the same line, then
 one and only one of the points is between the other two."
-/
@[simp] axiom B3 : ∀ A B C : Point, distinct A B C ∧ collinear A B C ->
  ( (A - B - C) ∧ ¬(B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧  (B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧ ¬(B - A - C) ∧  (A - C - B))

/--
p.110 "Definition. Let L be any line, and A and B points that do not lie on L. If A = B or if the segment A B
contains no points that lie on L, we say that A and B are _on the same side_ of L; whereas, if A ≠ B and segment A B
does intersect L, we say that A and B are _on opposite sides_ of L (see Figure 3.6). The law of the excluded middle
(Logic Rule 10) tells us that A and B are either on the same side or on opposite sides of L"
-/
@[reducible] def SameSide (A B : Point) (L : Line)
  := (A off L) ∧ (B off L) ∧ ((A = B) ∨ (∀ P : Point, (P on segment A B) -> (L avoids P)))

/--
"Splits" and "Guards", L "splits" A and B if A and B are on opposite sides of the 'wall' L, it 'guards'
them if they are both on the same side of the wall (we presume all points are allied with other points
on their side of the line).
-/
notation:20 L " splits " A " and " B => ¬(SameSide A B L)
notation:20 L " guards " A " and " B => SameSide A B L

/--
Ed. The author refers to the law of the excluded middle, Lean does not include it by default and
generally I want to avoid including it everywhere, this is a limited application of it which
should help our purpose.
-/
@[simp] axiom LotEMGuards : (L splits A and B) ∨ (L guards A and B)

/--
p.110 "Betweenness Axiom 4 (Plane Separation). For every line L and for any
three points A, B, and C not on L: (i) If A and B are on the same side of L and
if B and C are on the same side of L, the A and C are on the same side of L..."
-/
@[simp] axiom B4i {A B C : Point} {L : Line} :
  (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L guards A and B) ∧ (L guards B and C) -> (L guards A and C)
/--
"... (ii) If A and B are on opposite sides of L and if B and C are opposite
sides of L, then A and C are on the same side of L."
-/
@[simp] axiom B4ii {A B C : Point} {L : Line} :
  (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L splits A and B) ∧ (L splits B and C) -> (L guards A and C)

@[reducible] def Intersects (L M : Line) (X : Point) : Prop := L ∩ M = {X}

-- Syntax for "L intersects M at X"
syntax (name := intersectsAt) term " intersects " term " at " term : term

macro_rules (kind := intersectsAt)
  | `($L intersects $M at $X) => `(Intersects $L $M $X)



end Geometry.Theory
