/- Lemmas relating to the `distinct` condition -/

import Geometry.Tactics
import Mathlib.Data.List.Basic

namespace Geometry.Theory

open Lean Meta Expr Elab.Tactic Qq

-- Lots of imperative code here, newlines help make sense of things.
set_option linter.style.emptyLine false

-- Say you have a main goal is a conjunction of 'interesting' goals and also a bunch of inequality goals.
-- Further say you have a bunch of `distinct` conditions listing variables which are pairwise distinct.
--
-- h : distinct A B C D E := by magic
-- ⊢ A ≠ B ∧ B ≠ E ∧ X ≠ A
--
-- This provides a tactic, `distinguish`, which searches the local proof environment for `distinct` hypotheses
-- and then splits the conjunction to the smallest goals it can, and tries to prove as many inequality goals
-- as possible. The above would reduce to `X ≠ A` after running `distinguish`.
--
-- `distinguish` will not try to re-write any hypotheses or use any ambient inequality hypotheses. It probably should
--
-- finally, `separate` disassembles a `distinct` goal or hypothesis into a conjunction of inequalities. This is primarily useful
-- for breaking a goal into it's inequalities where it can be attacked with `tauto` or, ideally, `distinguish`.
--
-- TODO: Reassemble the conjunction after splitting it.
-- TODO: When splitting, gather goals and place them into some inductive structure which
--    categorizes them; simple inequalities are covered now, but a disjunction containing a conjunction
--    would be possible as well if we can prove one side of it; it might be possible to 'look past' quantifiers, etc.
-- TODO: an unelaborator to pretty-print the distinct condition as the distinct condition
-- TODO: grab any other ineq hypothesis to use in the proof; even if they don't come from a `distinct` condition


structure Distinct {α : Type*} (points : List α) : Prop where
  pairwise : List.Pairwise (· ≠ ·) points

namespace Distinct

/-- Get the list of points from a Distinct hypothesis (meta-level) -/
partial def getPointsExpr (distinctExpr : Expr) : MetaM (Option (List Expr)) := do
  let hypoType ← inferType distinctExpr
  let hypoType ← whnf hypoType
  if hypoType.isAppOfArity ``Distinct 2 then
    let listExpr := hypoType.getArg! 1
    let listExpr ← whnf listExpr
    let rec extract (e : Expr) : List Expr :=
      if e.isAppOfArity ``List.cons 3 then
        let head := e.appFn!.appArg!
        let tail := e.appArg!
        head :: extract tail
      else
        []
    return some (extract listExpr)
  else
    return none

/-- Extracts a list of expressions like `X ≠ Y ∧ ...` into [ X≠Y, ...], [ non-equality goals ] -/
partial def extractIneqs (e : Expr) : MetaM (List Expr × List Expr) := do
  have qe : Q(Prop) := e
  match qe with
  | ~q(@And $lhs $rhs) => do
    let (lhsIneqs, lhsOther) ← extractIneqs lhs
    let (rhsIneqs, rhsOther) ← extractIneqs rhs
    return (lhsIneqs ++ rhsIneqs, lhsOther ++ rhsOther)
  | ~q(@Ne _ $a $b) => return ([e], [])
  | _ => return ([], [e])

/-- Finds all `Distinct` hypotheses in the local context -/
def findDistinctHypos : TacticM (List LocalDecl) := do
  let lctx ← getLCtx
  let mut distinctHypos : List LocalDecl := []
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let declType ← instantiateMVars decl.type
    if declType.isAppOfArity ``Distinct 2 then
      distinctHypos := decl :: distinctHypos
  return distinctHypos

/-- Split conjunction goal into MVars and track which are inequalities -/
partial def splitAndTagGoals : TacticM (List MVarId × List Nat) := do
  let goal ← getMainGoal

  let rec splitAndExtract (g : MVarId) (idx : Nat) : TacticM (List MVarId × List (Nat × Bool)) := do
    let goalType ← g.getType
    have goalTypeProp : Q(Prop) := goalType

    match goalTypeProp with
    | ~q($a ∧ $b) => do
      -- Split conjunction
      setGoals [g]
      evalTactic (← `(tactic| constructor))
      let [leftGoal, rightGoal] ← getGoals | throwError "Expected two goals after constructor"

      -- Recursively process both sides
      let (leftMvars, leftTags) ← splitAndExtract leftGoal idx
      let rightIdx := idx + leftMvars.length
      let (rightMvars, rightTags) ← splitAndExtract rightGoal rightIdx

      return (leftMvars ++ rightMvars, leftTags ++ rightTags)

    | ~q(@Ne _ $a $b) =>
      -- Inequality - mark as such
      return ([g], [(idx, true)])

    | _ =>
      -- Other goal - not an inequality
      return ([g], [(idx, false)])

  let (mvars, tags) ← splitAndExtract goal 0
  let ineqIndices := tags.filterMap (fun (idx, isIneq) => if isIneq then some idx else none)

  return (mvars, ineqIndices)

def runDistinct : TacticM Unit := withMainContext do
    let (allGoals, ineqIndices) ← splitAndTagGoals
    let distinctHypos ← findDistinctHypos
    let mut solvedIndices : List Nat := []

    for idx in ineqIndices do
      let goalMVar := allGoals[idx]!
      setGoals [goalMVar]

      for hypo in distinctHypos do
        -- 1. break into the fvars on either side
        let goalType ← goalMVar.getType
        have goalTypeProp : Q(Prop) := goalType
        if let ~q(@Ne _ $lhs $rhs) := goalTypeProp then
          -- 2a. if the fvars are the same, then the two things are equal, reject
          if lhs.fvarId! != rhs.fvarId! then
            -- 3. now search the `points` of the `distinct` condition and we can conclude inequality based
            -- on the pairwise relationship
            if let some points ← Distinct.getPointsExpr hypo.toExpr then
              -- establish that both lhs and rhs are in the list of distinct variables
              let lhsIn := points.any (fun p => p.isFVar && p.fvarId! == lhs.fvarId!)
              let rhsIn := points.any (fun p => p.isFVar && p.fvarId! == rhs.fvarId!)
              if lhsIn && rhsIn then
                -- we can prove it, we have the technology
                let proofGoal ← mkFreshExprMVar goalType
                let proofMVar := proofGoal.mvarId!
                setGoals [proofMVar]
                let hypoName := mkIdent hypo.userName

                -- prove using aesop + simp, this is not ideal, it should be possible to construct a direct
                -- proof, but it's not low-effort, so FIXME some other time.
                evalTactic (← `(tactic| (
                  have h := ($hypoName).pairwise
                  simp only [List.Pairwise, List.mem_cons] at h
                  aesop
                )))

                -- Check if it was solved, then assign the goal if it is.
                if ← proofMVar.isAssigned then
                  let proof ← instantiateMVars proofGoal
                  goalMVar.assign proof
          else
            -- in this case, lhs is _literally the same variable reference_ as rhs, so we are trying to prove
            -- ¬(rfl A), which is just false, so the whole conjunction is false and we should replace the goal
            -- with false. I'm not doing that now, but it's doable, I think.
            throwError "lhs is identical to rhs, you're trying to prove A ≠ A, and that's no bueno"
        else
          logInfo m!"{goalType}"
          -- 2b. do nothing, this case is not possible because we're only inspecting inequalities.
          throwError "not possible"
      -- bookkeeping to make sure we set the goals correctly later.
      -- FIXME: I think this could probably be based on whether or not the mvar is assigned?
      if ← goalMVar.isAssigned then
        solvedIndices := idx :: solvedIndices

    -- Collect unsolved goals
    let mut unsolvedGoals : List MVarId := []
    for i in [:allGoals.length] do
      if !solvedIndices.contains i then
        unsolvedGoals := unsolvedGoals ++ [allGoals[i]!]

    setGoals unsolvedGoals

-- Custom syntax for distinct/distinguish
declare_syntax_cat distinct_binder
syntax ident+ " : " term : distinct_binder

syntax "distinct" ident+ : term
macro_rules
  | `(distinct $xs*) => `(Distinct [$xs,*])

syntax "distinguish" : tactic

macro_rules
  | `(tactic| distinguish) => `(tactic| run_tac runDistinct)

/-- Extract points from a List Expr at the meta level -/
partial def extractPoints (e : Expr) : List Expr :=
  if e.isAppOfArity ``List.cons 3 then
    let head := e.appFn!.appArg!
    let tail := e.appArg!
    head :: extractPoints tail
  else
    []

syntax "separate" (" at " ident)? : tactic

elab_rules : tactic
  | `(tactic| separate $[at $h]?) => do
  match h with
    | some hId => do
      withMainContext do
        let hExpr ← elabTerm hId none
        let hType ← instantiateMVars (← inferType hExpr)
        let hType ← whnf hType
        if !hType.isAppOfArity ``Distinct 2 then
          throwError "separate: {hId} is not a `Distinct` hypothesis"
        let some points ← Distinct.getPointsExpr hExpr
          | throwError "separate: could not extract points from {hId}"

        for i in [:points.length] do
          for j in [i+1:points.length] do
            let pi := points[i]!
            let pj := points[j]!
            let ineqType ← mkAppM ``Ne #[pi, pj]
            let ineqStx ← PrettyPrinter.delab ineqType
            -- Build a name like `AneB` from the fvar usernames
            let iName := (← FVarId.getUserName pi.fvarId!).toString
            let jName := (← FVarId.getUserName pj.fvarId!).toString
            let hypName := mkIdent (Name.mkSimple (iName ++ "ne" ++ jName))
            evalTactic (← `(tactic|
              have $hypName : $ineqStx := by
                have hp := ($hId).pairwise
                simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton,
                           List.not_mem_nil, List.Pairwise.nil] at hp
                aesop))

    | none => do
      withMainContext do
        let goal ← getMainGoal
        let goalType ← instantiateMVars (← goal.getType)
        let goalType ← whnf goalType
        if !goalType.isAppOfArity ``Distinct 2 then
          throwError "separate: goal is not of the form `Distinct [...]`"

        let listExpr := goalType.getArg! 1
        let points := extractPoints listExpr

        evalTactic (← `(tactic| apply Distinct.mk))

        for _ in [:points.length] do
          try evalTactic (← `(tactic| rw [List.pairwise_cons]))
          catch _ => pure ()

        evalTactic (← `(tactic| simp only [List.mem_cons, List.mem_singleton, List.Pairwise.nil,
                                            List.not_mem_nil, forall_eq_or_imp, forall_eq,
                                            forall_const, IsEmpty.forall_iff, forall_true_iff,
                                            and_true, true_and, and_assoc] at *))
        try evalTactic (← `(tactic| exact List.Pairwise.nil))
        catch _ => pure ()


-- EXAMPLES and TESTS

example : distinct A B C D E -> A ≠ X -> A ≠ B ∧ B ≠ C ∧ X ≠ A ∧ (∀ P : Nat, P = 2 -> P > 1) ∧ C ≠ D := by
  intro h AneX
  distinguish
  -- this part doesn't matter, the assertions are just to make sure the distiguish step doesn't oversolve
  exact AneX.symm
  intro P Peq2
  rw [Peq2]; trivial

example : distinct A B C D E -> A ≠ X -> A ≠ B ∧ (B ≠ C ∧ X ≠ A) ∧ (∀ P : Nat, P = 3 -> P > 1) ∧ (C ≠ D ∨ V = W) := by
  intro h AneX
  distinguish -- should be A≠B, B≠C, X≠A, C≠D
  · exact AneX.symm
  · intro P Peq3; rw [Peq3]; trivial
  · have CneD : C ≠ D := by distinguish
    left; trivial

example (A B C D : Point) (h : distinct A B C D) : A ≠ B ∧ B ≠ C ∧ A ≠ D := by
  distinguish

example (h : distinct A B) : A ≠ B := by distinguish

example : A ≠ B ∧ A ≠ C ∧ B ≠ C -> distinct A B C := by
  intro ⟨AneB, AneC, BneC⟩
  separate
  exact ⟨AneB, AneC, BneC⟩

example : D ≠ A ∧ D ≠ B ∧ D ≠ C -> distinct A B C -> distinct A B C D := by
  intro ⟨DneA, DneB, DneC⟩ distinctABC
  separate
  distinguish
  repeat tauto -- tauto covers the .symm

example : D ≠ A ∧ D ≠ B ∧ D ≠ C -> distinct A B C -> distinct A B C D := by
  intro ⟨DneA, DneB, DneC⟩ distinctABC
  separate at distinctABC
  separate
  repeat tauto -- tauto covers the .symm


end Distinct
end Geometry.Theory

-- distinct A B -> ∀ P : Prop, A ≠ B ∨ Prop
