import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Card

import Geometry.Theory.Axioms
import Geometry.Theory.Distinct
import Geometry.Theory.Interpendices.A

import Geometry.Tactics

namespace Geometry.Theory

namespace Extending

open Lean Meta Elab.Tactic

/-- Underlying Collinear extension lemma: inserting a point known to lie on the line
    preserves collinearity. -/
@[simp] lemma _root_.Geometry.Theory.Collinear.insert {s : Finset Point} {a : Point}
    (c : Collinear s) (h : a on c.line) : Collinear (insert a s) :=
  ⟨c.line, fun p hp => by
    rcases Finset.mem_insert.mp hp with rfl | hpS
    · exact h
    · exact c.on_line p hpS⟩

syntax "extending" : tactic

/-- Dispatch on the goal type — `Distinct.insert_step` requires `DecidableEq`, so
    pulling it into a `first` branch against a `Collinear` goal makes typeclass
    resolution get stuck. Inspecting the goal first avoids that. -/
elab_rules : tactic
  | `(tactic| extending) => withMainContext do
    let target := (← instantiateMVars (← (← getMainGoal).getType)).consumeMData
    if target.isAppOfArity ``Geometry.Theory.Collinear 1 then
      evalTactic (← `(tactic| (refine Collinear.insert ?_ ?_ <;> assumption)))
    else if target.isAppOfArity ``Geometry.Theory.Distinct 3 then
      evalTactic (← `(tactic| (refine Distinct.insert_step ?_ ?_ <;>
                                  first | assumption | (simp))))
    else
      throwError "extending: goal is not `Collinear _` or `Distinct _ _`"


-- Tests

example (A B C D : Point) (cABC : collinear A B C) (hD : D on cABC.line) :
    Collinear (insert D (insert A (insert B (Singleton.singleton C : Finset Point)))) := by extending


end Extending

end Geometry.Theory
