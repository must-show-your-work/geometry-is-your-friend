import Geometry.Theory.Primitives
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert

/-!
# Collinearity

`Collinear : Finset Point → Prop` plus the space-separated `collinear A B C`
surface syntax. Conceptually tightly coupled to incidence — three points are
collinear iff some line contains them all — but kept in its own file because
it's used by *both* the incidence axioms (I.3 mentions a "common line") and
the betweenness axioms (B-1a derives collinearity from betweenness).
-/

namespace Geometry.Theory

/-- Collinear: finite set of points on a common line -/
def Collinear (points : Finset Point) : Prop := ∃ L : Line, ∀ p ∈ points, p ∈ L

-- Syntax: collinear A B C (space-separated)
syntax "collinear" ident+ : term

macro_rules
  | `(collinear $x $xs*) => do
      let allArgs := #[x] ++ xs
      let last := allArgs[allArgs.size - 1]!
      let front := allArgs.pop
      let mut acc ← `((Singleton.singleton $last : Finset _))
      for y in front.reverse do
        acc ← `(insert $y $acc)
      `(Collinear $acc)

-- Pretty printer: TODO restore after Finset-literal unexpander is written

-- Extract the line from collinearity
noncomputable def Collinear.line {points : Finset Point} (h : Collinear points) : Line := Classical.choose h

-- Natural projections from the Collinear def — not book content, not atlas'd.
lemma Collinear.on_line {points : Finset Point} (h : Collinear points)
  : ∀ p ∈ points, p on h.line := Classical.choose_spec h

@[simp] lemma Collinear.mem
  {points : Finset Point} (h : Collinear points) (p : Point) (hp : p ∈ points := by simp)
  : p on h.line := h.on_line p hp

/-! ## Examples -/

section Examples
example {A B C : Point} : collinear A B C ↔ ∃ L : Line, A on L ∧ B on L ∧ C on L := by
  constructor
  · intro colABC; use colABC.line;
    exact ⟨colABC.mem A, colABC.mem B, colABC.mem C⟩
  · rintro ⟨L, AonL, BonL, ConL⟩
    use L
    intro P PinABC
    simp only [Finset.mem_insert, Finset.mem_singleton] at PinABC
    rcases PinABC with eq | eq | eq
    repeat rwa [eq]
end Examples

end Geometry.Theory
