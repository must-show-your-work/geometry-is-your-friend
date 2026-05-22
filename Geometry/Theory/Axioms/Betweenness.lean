import Geometry.Theory.Primitives
import Geometry.Theory.Collinear
import Geometry.Theory.Constructors
import Geometry.Theory.Distinct
import Geometry.Tactics.Obvious
import Atlas

/-!
# Betweenness axioms

Greenberg's betweenness axioms (B-1a, B-1b, B-2, B-3, B-4i, B-4ii) plus the
three density-axiom witness lemmas (1.0.5, 1.0.6, 1.0.7) extracted from B-2.

Same-side / opposite-side definitions and the `splits` / `guards` notation
also live here — they're the conceptual layer that B-4i and B-4ii depend on.
Page 108–110 of the text.
-/

namespace Geometry.Theory

open Atlas

atlas commentary := by
  ref axiom B-1a
  page 108
  name "A-B-C implies A B C are distinct and collinear"
  preface "If A - B - C, then A,B,C are distinct points on the same line..."

atlas axiom B-1a "A-B-C implies A B C are distinct and collinear"
  {A B C : Point} : A - B - C -> distinct A B C ∧ collinear A B C
attribute [simp, obvious] «A-B-C implies A B C are distinct and collinear»


atlas commentary := by
  ref axiom B-1b
  page 108
  name "Betweenness Commutativity"
  preface "... and [A - B - C iff] C - B - A.\"\""
  notes "Note, I separated these parts of the axiom to make rewriting
a bit easier. The author even notes, \"The second part (C * B * A) makes the obvious remark
that 'betwen A and C' means the same as 'between C and A'\" Making it a separate axiom means
I won't have to dig it out of the pile of parts that is 1a."

atlas axiom B-1b "Betweenness Commutativity"
  {A B C : Point} : A - B - C ↔ C - B - A
attribute [simp, obvious] «Betweenness Commutativity»

/-- Endpoint-reversal projection of B-1b — exposes B-1b's commutativity
    via dot notation: `BCD.symm` instead of `(«Betweenness Commutativity»).mp BCD`.
    Not atlas-tagged (this is a structural projection on the underlying
    `Between` relation, not book content). -/
def Between.symm {A B C : Point} (h : A - B - C) : C - B - A :=
  («Betweenness Commutativity»).mp h


atlas commentary := by
  ref axiom B.2
  page 108
  name "Two distinct points admit a left, middle, and right witness on their line"
  preface "Given any two distinct points B and D, there exist points A, C, and E lying on →ₗBD such that
A * B * D, B * C * D, and B * D * E."
  notes "I like to call this the 'density' axiom because, used recursively, it posits
something like the density of rationals -- for any two distinct points on a
line, there is always a point between them."

atlas axiom B.2 "Two distinct points admit a left, middle, and right witness on their line"
  : ∀ B D : Point, B ≠ D ->
  ∃ A C E : Point, collinear A B C D E ∧ distinct A B C D E ∧ (A - B - D) ∧ (B - C - D) ∧ (B - D - E)
attribute [simp] «Two distinct points admit a left, middle, and right witness on their line»


atlas commentary := by
  ref lemma 1.0.5
  name "Density axiom witness: a point left of two distinct points"
  preface "Construct a point 'to the left' of points BD on the induced line B D"

atlas lemma 1.0.5 "Density axiom witness: a point left of two distinct points"
  : ∀ B D : Point, B ≠ D -> ∃ A : Point, collinear A B D ∧ distinct A B D ∧ (A - B - D) := by
      intro B D BneD
      have ⟨A, _, _, colABCDE, distinctABCDE, ABD, _, _⟩ := ref axiom B.2 B D BneD
      use A
      obvious


atlas commentary := by
  ref lemma 1.0.6
  name "Density axiom witness: a point between two distinct points"
  preface "Construct a point 'in between' points BD on the induced line B D"

atlas lemma 1.0.6 "Density axiom witness: a point between two distinct points"
  : ∀ B D : Point, B ≠ D -> ∃ C : Point, collinear B C D ∧ distinct B C D ∧ (B - C - D) := by
      intro B D BneD
      have ⟨_, C, _, colABCDE, distinctABCDE, _, BCD, _⟩ := ref axiom B.2 B D BneD
      use C
      obvious


atlas commentary := by
  ref lemma 1.0.7
  name "Density axiom witness: a point right of two distinct points"
  preface "Construct a point 'to the right' points BD on the induced line B D"

atlas lemma 1.0.7 "Density axiom witness: a point right of two distinct points"
  : ∀ B D : Point, B ≠ D -> ∃ E : Point, collinear B D E ∧ distinct B D E ∧ (B - D - E) := by
      intro B D BneD
      have ⟨_, _, E, colABCDE, distinctABCDE, _, _, BDE⟩ := ref axiom B.2 B D BneD
      use E
      obvious


atlas commentary := by
  ref axiom B.3
  page 108
  name "Three distinct collinear points have exactly one between-arrangement"
  preface "If A, B, and C are three distinct points lying on the same line, then
 one and only one of the points is between the other two."

atlas axiom B.3 "Three distinct collinear points have exactly one between-arrangement"
  : ∀ A B C : Point, distinct A B C ∧ collinear A B C ->
  ( (A - B - C) ∧ ¬(B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧  (B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧ ¬(B - A - C) ∧  (A - C - B))
attribute [simp] «Three distinct collinear points have exactly one between-arrangement»

/-! ## Plane separation -/

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

atlas commentary := by
  ref axiom B-4i
  page 110
  name "Same-side is transitive across a common middle point"
  preface "Betweenness Axiom 4 (Plane Separation). For every line L and for any
three points A, B, and C not on L: (i) If A and B are on the same side of L and
if B and C are on the same side of L, the A and C are on the same side of L..."

atlas axiom B-4i "Same-side is transitive across a common middle point"
  {A B C : Point} {L : Line} :
  (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L guards A and B) ∧ (L guards B and C) -> (L guards A and C)
attribute [simp] «Same-side is transitive across a common middle point»

atlas commentary := by
  ref axiom B-4ii
  page 110
  name "Two opposite-side relations chain to a same-side relation"
  preface "... (ii) If A and B are on opposite sides of L and if B and C are opposite
sides of L, then A and C are on the same side of L."

atlas axiom B-4ii "Two opposite-side relations chain to a same-side relation"
  {A B C : Point} {L : Line} :
  (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L splits A and B) ∧ (L splits B and C) -> (L guards A and C)
attribute [simp] «Two opposite-side relations chain to a same-side relation»

/-! ## Examples -/

section Examples
variable (A B : Point) (L : Line)

example : (L splits A and B) ↔ ¬(SameSide A B L) := Iff.rfl
example : (L guards A and B) ↔ SameSide A B L := Iff.rfl
end Examples

end Geometry.Theory
