import Geometry.Theory.Primitives
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import LeanTeX

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

/-! ## LeanTeX rule — render as `\operatorname{collinear}\{A, B, C, …\}` -/

private partial def finsetLiteralElems (e : Lean.Expr) (acc : Array Lean.Expr) :
    Option (Array Lean.Expr) :=
  match Lean.Expr.getAppFnArgs e with
  | (``Insert.insert, args) =>
    if args.size ≥ 5 then
      finsetLiteralElems args[4]! (acc.push args[3]!)
    else none
  | (``Singleton.singleton, args) =>
    if args.size ≥ 4 then some (acc.push args[3]!) else none
  | _ => none

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.Collinear)
  | _, #[setExpr] => do
    let some elems := finsetLiteralElems setExpr #[] | failure
    if elems.size = 0 then failure
    let texs ← elems.mapM latexPP
    let inner := LatexData.intercalate ", " texs
    return LatexData.atomString "\\operatorname{collinear}\\," ++ inner

/-! ## LeanTeX rule — `Not (Collinear …)` collapses to `noncollinear(…)`.

Surface notation `noncollinear A B C` desugars at parse time to
`¬ collinear A B C` which elaborates to `Not (Collinear …)`. The
default `Not` printer would render that as `¬ collinear(A, B, C)`;
we recognize the shape and emit a single-word `noncollinear(…)` to
match the surface notation. Falls through to the default `Not`
printer when the argument isn't a `Collinear` application. -/

open LeanTeX in
latex_pp_app_rules (const := Not)
  | _, #[arg] => do
    guard <| arg.isAppOfArity ``Geometry.Theory.Collinear 1
    let setExpr := arg.getArg! 0
    let some elems := finsetLiteralElems setExpr #[] | failure
    if elems.size = 0 then failure
    let texs ← elems.mapM latexPP
    let inner := LatexData.intercalate ", " texs
    return LatexData.atomString "\\operatorname{noncollinear}\\," ++ inner

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
