import Geometry.Tactics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert

/-!
# `by_exhaustion` tactic

`by_exhaustion h` where `h : P ∈ {A, B, C, ...}` (a Finset literal) splits
the proof into one goal per element, with the corresponding equality
auto-named like `clearly` does (`PeqA`, `PeqB`, ...).

Stands in for `fin_cases h` (which requires a computable `DecidableEq` and
thus doesn't apply to `Point`, which only has `Classical.decEq`).
-/

namespace Geometry.Theory

/-- `by_exhaustion h` where `h : P ∈ {A, B, C, ...}` (a Finset literal) splits
    the proof into one goal per element, with the corresponding equality
    auto-named like `clearly`: `PeqA`, `PeqB`, etc.

    Stands in for `fin_cases h` (which requires a computable `DecidableEq` and
    thus doesn't apply to `Point`). Internally: `simp` unfolds Finset membership
    to a disjunction, then `rcases` destructures with the generated names. -/
syntax "by_exhaustion " ident : tactic

open Lean Meta Elab Elab.Tactic in
elab_rules : tactic
  | `(tactic| by_exhaustion $h:ident) => withMainContext do
    -- Step 1: unfold Finset membership into a disjunction of equalities.
    evalTactic (← `(tactic|
      simp only [Finset.mem_insert, Finset.mem_singleton] at $h:ident))
    -- Step 2: walk the resulting Or chain, collecting auto-names like `<lhs>eq<rhs>`.
    withMainContext do
      let hFVar ← getFVarId h
      let hType ← instantiateMVars (← hFVar.getType)
      let getName : Expr → MetaM String := fun e => do
        match e with
        | .fvar fid => return (← fid.getUserName).toString
        | _ => return "x"
      let extractEq (e : Expr) : MetaM (Option String) := do
        if e.isAppOfArity ``Eq 3 then
          let lN ← getName (e.getArg! 1)
          let rN ← getName (e.getArg! 2)
          return some s!"{lN}eq{rN}"
        else
          return none
      let mut names : Array String := #[]
      let mut current := hType
      while current.isAppOfArity ``Or 2 do
        if let some n ← extractEq (current.getArg! 0) then
          names := names.push n
        current := current.getArg! 1
      if let some n ← extractEq current then
        names := names.push n
      if names.isEmpty then
        throwError "by_exhaustion: could not extract eq disjuncts from hypothesis type"
      -- Step 3: build and run `rcases h with name_1 | name_2 | ...` via string parse.
      let patStr := String.intercalate " | " names.toList
      let tacStr := s!"rcases {h.getId} with {patStr}"
      match Parser.runParserCategory (← getEnv) `tactic tacStr with
      | .ok stx => evalTactic stx
      | .error err =>
          throwError s!"by_exhaustion: failed to build rcases tactic from '{tacStr}': {err}"

/-! ## Examples -/

section Examples
-- Singleton/insert Finsets get split into one goal per element. With three
-- elements, the tactic exposes three named hypotheses (`xeqA`, `xeqB`, `xeqC`).
example (A B C x : Nat) (h : x ∈ ({A, B, C} : Finset Nat)) :
    x = A ∨ x = B ∨ x = C := by
  by_exhaustion h
  · left; exact xeqA
  · right; left; exact xeqB
  · right; right; exact xeqC
end Examples

end Geometry.Theory
