import Geometry.Theory.Primitives
import Geometry.Theory.Collinear
import Geometry.Theory.Constructors
import Geometry.Theory.Distinct
import Geometry.Tactics.Obvious
import Atlas

/-!
# Betweenness axioms

Greenberg's betweenness axioms (B-1, B-2, B-3, ["B.4.i"], ["B.4.ii"]) plus the
three density-axiom witness lemmas (1.0.5, 1.0.6, 1.0.7) extracted from B-2.
B-1 returns `Between.Consequences` with `.distinct`, `.collinear`, `.symm`
projections; `Between.symm` wires the mathlib `symm` tactic.

Same-side / opposite-side definitions and the `splits` / `guards` notation
also live here — they're the conceptual layer that ["B.4.i"] and ["B.4.ii"] depend on.
Page 108–110 of the text.
-/

namespace Geometry.Theory

open Atlas

/-- `B.1`'s conclusion: three facts packaged together — distinctness,
    collinearity, and commutativity (`.symm` gives the reversed
    betweenness). `@[reducible]` over nested `And` so positional
    destructuring (`⟨d, c, s⟩`) and dot-notation both work. -/
@[reducible] def Between.Consequences (A B C : Point) : Prop :=
  distinct A B C ∧ collinear A B C ∧ (C - B - A)

namespace Between.Consequences
@[reducible] def «distinct» {A B C : Point} (h : Between.Consequences A B C) : distinct A B C := h.1
@[reducible] def «collinear» {A B C : Point} (h : Between.Consequences A B C) : collinear A B C := h.2.1
@[reducible] def «symm» {A B C : Point} (h : Between.Consequences A B C) : C - B - A := h.2.2
end Between.Consequences

atlas commentary := by
  ref axiom B.1
  page 108
  name "A-B-C implies distinctness, collinearity, and commutativity"
  preface "If A - B - C, then A, B, C are distinct points on the same line, and C - B - A."

atlas axiom B.1 "A-B-C implies distinctness, collinearity, and commutativity"
  {A B C : Point} : A - B - C -> Between.Consequences A B C
attribute [simp, obvious] «A-B-C implies distinctness, collinearity, and commutativity»

/-- `@[symm]` wires the mathlib `symm` tactic + `h.symm` dot notation
    on `h : A - B - C`. Body is just `(B.1 h).symm` via the structure
    field. -/
@[symm] def Between.symm {A B C : Point} (h : A - B - C) : C - B - A :=
  Between.Consequences.symm («A-B-C implies distinctness, collinearity, and commutativity» h)


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


-- Density witness lemmas 1.0.5 / 1.0.6 / 1.0.7 (extracted from B.2)
-- moved to `Geometry/Theory/Interpendices/A.lean` (axiom-derivable).

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
@[reducible, obvious.guards]
def Guards (A B : Point) (L : Line)
  := (A off L) ∧ (B off L) ∧ ((A = B) ∨ (∀ P : Point, (P on segment A B) -> (L avoids P)))

/-- `Splits` and `Guards` are paired: `Splits L A B := ¬(Guards A B L)`. Both
    have notation forms — `L splits A and B` and `L guards A and B` — that the
    goal-view printer renders directly (rather than unfolding to one or the
    other's def body). `Guards` is `@[reducible]` so destructuring its And-
    conjunction is transparent; `Splits` is NOT reducible, because reducibility
    would unfold it to `Guards A B L → False` and break dot-notation lookup
    for `Splits.symm` (Lean would look for `Function.symm` on the function-
    type form). Use `unfold Splits Guards` (or `simp only [Splits, Guards]`)
    when you need either layer transparent in a proof.

    L "splits" A and B if A and B are on opposite sides of the 'wall' L; L
    "guards" them if they are both on the same side (we presume all points
    are allied with other points on their side of the line). -/
@[obvious.guards]
def Splits (L : Line) (A B : Point) : Prop := ¬(Guards A B L)

notation:20 L " splits " A " and " B => Splits L A B
notation:20 L " guards " A " and " B => Guards A B L

/-- `¬(L splits A and B) ↔ L guards A and B`. Tagged `@[push, simp]` so the
    `push Not` tactic (and therefore `by_contra!`) automatically converts the
    introduced negation back into a `guards` hypothesis. -/
@[push, simp] theorem not_splits_iff_guards {A B : Point} {L : Line} :
  ¬(L splits A and B) ↔ (L guards A and B) := by
  unfold Splits
  exact Classical.not_not

/-- `¬(L guards A and B) ↔ L splits A and B`. Holds by definition of `Splits` —
    `@[simp]` for explicit invocation. Not tagged `@[push]` because that would
    create a normalization loop with `not_splits_iff_guards` (one rule undoes
    the other); `push`'s auto-pull machinery handles the reverse direction. -/
@[simp] theorem not_guards_iff_splits {A B : Point} {L : Line} :
  ¬(L guards A and B) ↔ (L splits A and B) := Iff.rfl

atlas commentary := by
  ref axiom ["B.4.i"]
  page 110
  name "Same-side is transitive across a common middle point"
  preface "Betweenness Axiom 4 (Plane Separation). For every line L and for any
three points A, B, and C not on L: (i) If A and B are on the same side of L and
if B and C are on the same side of L, the A and C are on the same side of L..."

atlas axiom ["B.4.i"] "Same-side is transitive across a common middle point"
  {A B C : Point} {L : Line}
  (AoffL : A off L := by assumption)
  (BoffL : B off L := by assumption)
  (CoffL : C off L := by assumption) :
  (L guards A and B) ∧ (L guards B and C) -> (L guards A and C)
attribute [simp] «Same-side is transitive across a common middle point»

atlas commentary := by
  ref axiom ["B.4.ii"]
  page 110
  name "Two opposite-side relations chain to a same-side relation"
  preface "... (ii) If A and B are on opposite sides of L and if B and C are opposite
sides of L, then A and C are on the same side of L."

atlas axiom ["B.4.ii"] "Two opposite-side relations chain to a same-side relation"
  {A B C : Point} {L : Line}
  (AoffL : A off L := by assumption)
  (BoffL : B off L := by assumption)
  (CoffL : C off L := by assumption) :
  (L splits A and B) ∧ (L splits B and C) -> (L guards A and C)
attribute [simp] «Two opposite-side relations chain to a same-side relation»

/-! ## Examples -/

section Examples
variable (A B : Point) (L : Line)

example : (L splits A and B) ↔ ¬(Guards A B L) := Iff.rfl
example : (L guards A and B) ↔ Guards A B L := Iff.rfl
end Examples

end Geometry.Theory
