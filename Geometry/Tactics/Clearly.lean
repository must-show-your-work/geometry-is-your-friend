import Geometry.Tactics
import Geometry.Theory.Primitives
import Geometry.Theory.Constructors
import Geometry.Tactics.Obvious

/-!
# `clearly` tactic

Naming + case-split scaffolding for the "assume the alternative, argue the
result is trivial, so assume the proposed" pattern Greenberg uses without
comment. Owns the auto-name conventions (`PoffL`, `AeqB`, `SegAB`, ...) for
the resulting hypotheses.

Pairs with `obvious` (which discharges the alternative branch when no
explicit body is given): `clearly P` defaults to `clearly P := by obvious`.
-/

namespace Geometry.Theory

/-- `clearly P := by body` introduces `P` as a fact for the rest of the proof, having
    discharged the negation branch — i.e. the body proves the main goal under the
    assumption `¬P`. The reading is: "clearly P, because if not, the goal is immediate
    (`body`); proceeding under `P`".

    Supported shapes for `P` (auto-named hypotheses derived from the identifiers):
    - `A ≠ B`: rest of proof gets `AneB : A ≠ B`; body sees `AeqB : A = B`.
    - `A = B`: rest of proof gets `AeqB : A = B`; body sees `AneB : A ≠ B`.
    - `P on L`: rest of proof gets `PonL : P on L`; body sees `PoffL : P off L`.
    - `P off L`: rest of proof gets `PoffL : P off L`; body sees `PonL : P on L`. -/
syntax "clearly " term " := " "by " tacticSeq : tactic
syntax "clearly " term : tactic
syntax "clearly?" term : tactic

/-- Derive an auto-name component from a term used in a `clearly` clause.
    Identifiers map to their user-name; line-part expressions get short
    capitalized prefixes (`segment A B` → `SegAB`, `line A B` → `LineAB`, etc.). -/
private partial def clearlyTermName (s : Lean.Syntax) : Lean.MacroM String := do
  match s with
  | `($id:ident) => return id.getId.toString
  | `(segment $A:ident $B:ident) => return s!"Seg{A.getId}{B.getId}"
  | `(ray $A:ident $B:ident) => return s!"Ray{A.getId}{B.getId}"
  | `(extension $A:ident $B:ident) => return s!"Ext{A.getId}{B.getId}"
  | `(line $A:ident $B:ident) => return s!"Line{A.getId}{B.getId}"
  -- Strip type ascription `(X : T)` and use the inner term's name. This
  -- handles cross-line-part comparisons like
  -- `clearly (segment A B : Set Point) ≠ (segment B C : Set Point)`.
  | `(($inner : $_)) => clearlyTermName inner
  | _ => Lean.Macro.throwError "clearly: cannot derive an auto-name from this term"

-- `macro_rules` (rather than `elab_rules`) expansion keeps the resulting tactics
-- visible to the LSP. However, see FIXME below.
--
-- FIXME: LSP doesn't render the body-side hypothesis (e.g. `ConL` inside a
-- `clearly C off L := by ...` block) in the goal panel at intermediate lines of
-- the body, even though it IS in scope (usable in the proof and visible via
-- `trace_state`). The other-side hypothesis (e.g. `CoffL` on the line after the
-- `clearly` block) renders fine. Suspected cause: macro-introduced `rcases` /
-- `case inl =>` tokens get synthetic source positions that the LSP's info-tree
-- walker doesn't query against. Workaround: put a `trace_state` at the body's
-- start to confirm the hypothesis is there.
macro_rules
  | `(tactic| clearly $prop) => `(tactic| clearly $prop := by obvious)
  | `(tactic| clearly? $prop) => `(tactic| clearly $prop := by obvious?)
  | `(tactic| clearly $lhs ≠ $rhs := by $body) => do
    let lName ← clearlyTermName lhs
    let rName ← clearlyTermName rhs
    let eqIdent := Lean.mkIdent (.mkSimple s!"{lName}eq{rName}")
    let neIdent := Lean.mkIdent (.mkSimple s!"{lName}ne{rName}")
    `(tactic| (
      rcases Classical.em ($lhs = $rhs) with $eqIdent:ident | $neIdent:ident
      case inl => $body))
  | `(tactic| clearly $lhs = $rhs := by $body) => do
    let lName ← clearlyTermName lhs
    let rName ← clearlyTermName rhs
    let eqIdent := Lean.mkIdent (.mkSimple s!"{lName}eq{rName}")
    let neIdent := Lean.mkIdent (.mkSimple s!"{lName}ne{rName}")
    `(tactic| (
      rcases Classical.em ($lhs = $rhs) with $eqIdent:ident | $neIdent:ident
      case inr => $body))
  | `(tactic| clearly $P on $L := by $body) => do
    let pName ← clearlyTermName P
    let lName ← clearlyTermName L
    let onIdent := Lean.mkIdent (.mkSimple s!"{pName}on{lName}")
    let offIdent := Lean.mkIdent (.mkSimple s!"{pName}off{lName}")
    `(tactic| (
      rcases Classical.em ($P ∈ $L) with $onIdent:ident | $offIdent:ident
      case inr => $body))
  | `(tactic| clearly $P off $L := by $body) => do
    let pName ← clearlyTermName P
    let lName ← clearlyTermName L
    let onIdent := Lean.mkIdent (.mkSimple s!"{pName}on{lName}")
    let offIdent := Lean.mkIdent (.mkSimple s!"{pName}off{lName}")
    `(tactic| (
      rcases Classical.em ($P ∈ $L) with $onIdent:ident | $offIdent:ident
      case inl => $body))

/-! ## Examples -/

section Examples
-- `clearly` introduces the named hypothesis in the proposed branch; the
-- body discharges the alternative branch. Here we use the most boring
-- possible surrounding goal (`True`) so the body just closes via `trivial`.
example (a b : Nat) : True := by
  clearly a = b := by trivial
  -- `aeqb : a = b` is now in scope (LSP rendering caveat aside).
  trivial
end Examples

end Geometry.Theory
