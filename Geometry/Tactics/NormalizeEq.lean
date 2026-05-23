import Lean

/-!
# `normalize_eq` tactic

Walks the local context and flips `=` / `≠` hypotheses between free variables
so the LHS comes lex-before the RHS by user-name. Used by `obvious` as a
pre-pass so `simp_all` / `tauto` aren't tripped up by `Ne` / `Eq` orientation.
-/

namespace Geometry.Theory

/-- `normalize_eq` walks the local context and flips `=` / `≠` hypotheses between
    free variables so the LHS comes lex-before the RHS by user-name. Useful when
    a downstream tactic (`simp`, `tauto`) doesn't know about `Ne.symm` / `Eq.symm`
    and is stuck on an inequality whose orientation is "backwards". -/
syntax "normalize_eq" : tactic

open Lean Meta Elab.Tactic in
elab_rules : tactic
  | `(tactic| normalize_eq) => withMainContext do
    -- Snapshot the list of hypotheses to flip; applying them mutates the local
    -- context, so collect first and apply after.
    let lctx ← getLCtx
    let mut toFlip : Array (Name × Bool) := #[]  -- (hypothesis name, isEq?)
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let (isEq, a?, b?) ←
        if ty.isAppOfArity ``Eq 3 then
          pure (true, some (ty.getArg! 1), some (ty.getArg! 2))
        else if ty.isAppOfArity ``Ne 3 then
          pure (false, some (ty.getArg! 1), some (ty.getArg! 2))
        else
          pure (false, none, none)
      match a?, b? with
      | some a, some b =>
        if a.isFVar && b.isFVar then
          let aName := (← a.fvarId!.getUserName).toString
          let bName := (← b.fvarId!.getUserName).toString
          if aName > bName then
            toFlip := toFlip.push (ldecl.userName, isEq)
      | _, _ => pure ()
    for (hName, isEq) in toFlip do
      let hIdent := mkIdent hName
      let symIdent := mkIdent (if isEq then ``Eq.symm else ``Ne.symm)
      evalTactic (← `(tactic| replace $hIdent:ident := $symIdent:ident $hIdent:ident))

/-! ## Examples -/

section Examples
-- `normalize_eq` flips `b = a` to `a = b` when the LHS-name is greater than
-- the RHS-name. Here `b > a` lexicographically, so the hypothesis is flipped.
example (a b : Nat) (h : b = a) : a = b := by
  normalize_eq
  exact h
end Examples

end Geometry.Theory
