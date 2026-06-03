import Geometry.Theory.Primitives
import Geometry.Theory.Collinear
import Geometry.Construction.AtlasField
import Atlas

/-!
# Incidence axioms

Greenberg's three incidence axioms (I.1, I.2, I.3) plus the derived concepts
of `Concurrent` and `Parallel` lines. Page 69–70 of the text.

The axioms are very terse in the original; the atlas commentary blocks
attached to each one carry the informal respelling and any editorial notes.
-/

namespace Geometry.Theory

open Atlas

-- p. 69-70, Ed. The author provides these as very terse statements, I've tried to give informal
-- respellings as documentation.
atlas commentary := by
  via axiom I.1
  name "Two distinct points determine a unique line through them"
  preface "For any two distinct points P and Q, there exists a unique line L which has P and Q"

  figure := by
    construction {
      exists P Q : Point
      exists L : Line
      assert incident P L
      assert incident Q L
    }
    title "Axiom I.1"
    index 1
    caption "Line L is the unique line through the distinct points P and Q."

atlas axiom I.1 "Two distinct points determine a unique line through them"
  : ∀ P Q : Point, P ≠ Q -> ∃! L : Line, (P on L) ∧ (Q on L)
attribute [simp] «Two distinct points determine a unique line through them»

atlas commentary := by
  via axiom I.2
  name "Every line contains at least two distinct points"
  preface "For any line, there are at least two distinct points on it"

  figure := by
    construction {
      exists A B : Point
      exists L : Line
      assert distinct A B
      assert incident A L
      assert incident B L
    }
    title "Axiom I.2"
    index 1
    caption "Line L carries at least two distinct points A and B."

atlas axiom I.2 "Every line contains at least two distinct points"
  : ∀ L : Line, ∃ A B : Point, A ≠ B ∧ (A on L) ∧ (B on L)
attribute [simp] «Every line contains at least two distinct points»

atlas commentary := by
  via axiom I.3
  name "There exist three points not all lying on a common line"
  preface "There exists three distinct points not on any single line (\"There exists three non-collinear points\", but without mentioning the undefined notion of collinearity)"

  figure := by
    construction {
      exists A B C : Point
      assert distinct A B C
      assert ¬ collinear A B C
    }
    title "Axiom I.3"
    index 1
    caption "Three points A, B, C with no single line through all three."

atlas axiom I.3 "There exist three points not all lying on a common line"
  : ∃ A B C : Point, (A ≠ B ∧ A ≠ C ∧ B ≠ C) ∧ (∀ (L : Line), (A on L) → (B on L) → (C off L))
attribute [simp] «There exist three points not all lying on a common line»

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
@[reducible, obvious.parallel]
def Parallel (L M : Line) : Prop := L ≠ M ∧ ∀ P : Point, ¬((P on L) ∧ (P on M))

notation:20 L " ∥ " M => Parallel L M
notation:20 L " ∦ " M => ¬(Parallel L M)

/-! ## Examples -/

section Examples
variable (L M N : Line)

example : Concurrent L M N ↔ ∃ P : Point, (P on L) ∧ (P on M) ∧ (P on N) := Iff.rfl
example : (L ∥ M) ↔ Parallel L M := Iff.rfl
example : (L ∦ M) ↔ ¬Parallel L M := Iff.rfl
end Examples

end Geometry.Theory
