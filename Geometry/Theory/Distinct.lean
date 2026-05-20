/- Lemmas relating to the `distinct` condition, now over `Finset`. -/

import Geometry.Tactics
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Erase
import Atlas

namespace Geometry.Theory

open Lean Meta Expr Elab.Tactic Qq

-- Lots of imperative code here, newlines help make sense of things.
set_option linter.style.emptyLine false

-- `Distinct s n` asserts that the finite set `s` has exactly `n` elements.
-- Since `Finset` is by construction `Nodup`, asserting cardinality is what
-- captures "these `n` elements are pairwise distinct".
--
-- The `distinguish` tactic searches `Distinct` hypotheses in scope to discharge
-- pairwise inequality goals; the `separate` tactic decomposes a `Distinct` goal
-- or hypothesis into the underlying inequalities.

structure Distinct {α : Type*} (s : Finset α) (n : ℕ) : Prop where
  card_eq : s.card = n

namespace Distinct

-- Natural projections on the Distinct structure — not book content, not atlas'd.

/-- Any Finset is "distinct" with its own cardinality — purely structural. -/
lemma self_card {α : Type*} (s : Finset α) : Distinct s s.card := ⟨rfl⟩

/-- Inserting a new element bumps the cardinality by one when the element is fresh. -/
lemma insert_step {α : Type*} [DecidableEq α] {s : Finset α} {n : ℕ} {a : α}
    (d : Distinct s n) (h : a ∉ s) : Distinct (insert a s) (n + 1) :=
  ⟨by rw [Finset.card_insert_of_notMem h, d.card_eq]⟩

/-- Erasing an element drops the cardinality by one when the element was present. -/
lemma erase_step {α : Type*} [DecidableEq α] {s : Finset α} {n : ℕ} {a : α}
    (d : Distinct s (n + 1)) (h : a ∈ s) : Distinct (s.erase a) n :=
  ⟨by rw [Finset.card_erase_of_mem h, d.card_eq]; omega⟩

/-- Cast `Distinct` between propositionally-equal Finsets. Finsets are unordered, so
    two literals describing the same elements are equal even when they don't unify
    definitionally — useful when a hypothesis is produced under one insertion order
    and a consumer needs another (or when `Finset.erase` doesn't reduce to a literal). -/
lemma of_eq {α : Type*} {s t : Finset α} {n : ℕ}
    (d : Distinct s n) (h : s = t) : Distinct t n := h ▸ d

end Distinct

/-- A small simp-driven tactic that canonicalizes Finset literals by sorting
    insertions and resolving `erase` against `insert`. Useful when chapter
    proofs pass a `forgetting X` result where the expected type has a
    different insertion order. -/
syntax "finset_canon" : tactic

macro_rules
  | `(tactic| finset_canon) => `(tactic|
      simp only [Finset.insert_comm, Finset.insert_idem,
                 Finset.mem_insert, Finset.mem_singleton, ne_eq,
                 not_or, not_false_eq_true, or_self, and_self])


namespace Distinct

/-- Walk a Finset literal (chains of `Finset.insert` / `Insert.insert` ending in `∅`)
    and extract the element Exprs. Returns `none` if the structure isn't a literal. -/
partial def getPointsExpr (distinctExpr : Expr) : MetaM (Option (List Expr)) := do
  let hypoType ← inferType distinctExpr
  let hypoType ← whnf hypoType
  -- `Distinct` has 3 args: α, s, n
  if hypoType.isAppOfArity ``Distinct 3 then
    let sExpr := hypoType.getArg! 1
    return some (extractInsert sExpr)
  else
    return none
where
  extractInsert (e : Expr) : List Expr :=
    -- Insert.insert head tail, or Finset.insert head tail
    if e.isAppOfArity ``Insert.insert 5 then
      let head := e.appFn!.appArg!
      let tail := e.appArg!
      head :: extractInsert tail
    else if e.isAppOfArity ``Singleton.singleton 4 then
      let head := e.appArg!
      [head]
    else
      []

/-- Extracts a conjunction tree like `X ≠ Y ∧ ...` into ([X≠Y, ...], [non-equality goals]). -/
partial def extractIneqs (e : Expr) : MetaM (List Expr × List Expr) := do
  have qe : Q(Prop) := e
  match qe with
  | ~q(@And $lhs $rhs) => do
    let (lhsIneqs, lhsOther) ← extractIneqs lhs
    let (rhsIneqs, rhsOther) ← extractIneqs rhs
    return (lhsIneqs ++ rhsIneqs, lhsOther ++ rhsOther)
  | ~q(@Ne _ $a $b) => return ([e], [])
  | _ => return ([], [e])

/-- Finds all `Distinct` hypotheses in the local context. -/
def findDistinctHypos : TacticM (List LocalDecl) := do
  let lctx ← getLCtx
  let mut distinctHypos : List LocalDecl := []
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let declType ← instantiateMVars decl.type
    if declType.isAppOfArity ``Distinct 3 then
      distinctHypos := decl :: distinctHypos
  return distinctHypos

/-- Split conjunction goal into MVars and track which are inequalities. -/
partial def splitAndTagGoals : TacticM (List MVarId × List Nat) := do
  let goal ← getMainGoal

  let rec splitAndExtract (g : MVarId) (idx : Nat) : TacticM (List MVarId × List (Nat × Bool)) := do
    let goalType ← g.getType
    have goalTypeProp : Q(Prop) := goalType

    match goalTypeProp with
    | ~q($a ∧ $b) => do
      setGoals [g]
      evalTactic (← `(tactic| constructor))
      let [leftGoal, rightGoal] ← getGoals | throwError "Expected two goals after constructor"

      let (leftMvars, leftTags) ← splitAndExtract leftGoal idx
      let rightIdx := idx + leftMvars.length
      let (rightMvars, rightTags) ← splitAndExtract rightGoal rightIdx

      return (leftMvars ++ rightMvars, leftTags ++ rightTags)

    | ~q(@Ne _ $a $b) =>
      return ([g], [(idx, true)])

    | _ =>
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
        let goalType ← goalMVar.getType
        have goalTypeProp : Q(Prop) := goalType
        if let ~q(@Ne _ $lhs $rhs) := goalTypeProp then
          if lhs.fvarId! != rhs.fvarId! then
            if let some points ← Distinct.getPointsExpr hypo.toExpr then
              let lhsIn := points.any (fun p => p.isFVar && p.fvarId! == lhs.fvarId!)
              let rhsIn := points.any (fun p => p.isFVar && p.fvarId! == rhs.fvarId!)
              if lhsIn && rhsIn then
                let proofGoal ← mkFreshExprMVar goalType
                let proofMVar := proofGoal.mvarId!
                setGoals [proofMVar]
                let hypoName := mkIdent hypo.userName

                -- Prove via simp on Finset membership/cardinality combined with the
                -- card_eq witness, then aesop closes residual goals.
                evalTactic (← `(tactic| (
                  have h := ($hypoName).card_eq
                  simp only [Finset.card_insert_eq_ite, Finset.card_singleton,
                             Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
                             ne_eq, not_or, not_false_eq_true] at h
                  split_ifs at h <;> aesop
                )))

                if ← proofMVar.isAssigned then
                  let proof ← instantiateMVars proofGoal
                  goalMVar.assign proof
          else
            throwError "lhs is identical to rhs, you're trying to prove A ≠ A, and that's no bueno"
        else
          logInfo m!"{goalType}"
          throwError "not possible"
      if ← goalMVar.isAssigned then
        solvedIndices := idx :: solvedIndices

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
  | `(distinct $x $xs*) => do
      let allArgs : Array (TSyntax `ident) := #[x] ++ xs
      let n := Syntax.mkNumLit (toString allArgs.size)
      let last := allArgs[allArgs.size - 1]!
      let front := allArgs.pop
      let mut acc ← `((Singleton.singleton $last : Finset _))
      for y in front.reverse do
        acc ← `(insert $y $acc)
      `(Distinct $acc $n)

syntax "distinguish" : tactic

macro_rules
  | `(tactic| distinguish) => `(tactic| run_tac runDistinct)


/-- Extract the element Exprs from a Finset-literal expression. -/
partial def extractPoints (e : Expr) : List Expr :=
  if e.isAppOfArity ``Insert.insert 5 then
    let head := e.appFn!.appArg!
    let tail := e.appArg!
    head :: extractPoints tail
  else if e.isAppOfArity ``Singleton.singleton 4 then
    let head := e.appArg!
    [head]
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
        if !hType.isAppOfArity ``Distinct 3 then
          throwError "separate: {hId} is not a `Distinct` hypothesis"
        let some points ← Distinct.getPointsExpr hExpr
          | throwError "separate: could not extract points from {hId}"

        for i in [:points.length] do
          for j in [i+1:points.length] do
            let pi := points[i]!
            let pj := points[j]!
            let ineqType ← mkAppM ``Ne #[pi, pj]
            let ineqStx ← PrettyPrinter.delab ineqType
            let iName := (← FVarId.getUserName pi.fvarId!).toString
            let jName := (← FVarId.getUserName pj.fvarId!).toString
            let hypName := mkIdent (Name.mkSimple (iName ++ "ne" ++ jName))
            evalTactic (← `(tactic|
              have $hypName : $ineqStx := by
                have h := ($hId).card_eq
                simp only [Finset.card_insert_eq_ite, Finset.card_singleton,
                           Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
                           ne_eq, not_or, not_false_eq_true] at h
                split_ifs at h <;> aesop))

    | none => do
      withMainContext do
        let goal ← getMainGoal
        let goalType ← instantiateMVars (← goal.getType)
        let goalType ← whnf goalType
        if !goalType.isAppOfArity ``Distinct 3 then
          throwError "separate: goal is not of the form `Distinct _ _`"

        let sExpr := goalType.getArg! 1
        let points := extractPoints sExpr
        let n := points.length

        if n == 0 then
          throwError "separate: empty Finset"
        if n == 1 then
          evalTactic (← `(tactic| exact ⟨Finset.card_singleton _⟩))
          return

        -- Goal: `Distinct {a₁,...,aₙ} n`. Decompose into a SINGLE goal that's the
        -- conjunction of all pairwise inequalities — leaving the proof state in a
        -- form that `distinguish` can split via its existing conjunction-handling
        -- (`splitAndTagGoals`) and discharge per-inequality from `Distinct` hypotheses.
        --
        -- Strategy: use `suffices h : <conj>` to introduce the pairwise-ne conjunction
        -- as the goal, with the suffices-body constructing `Distinct.mk` via a chain
        -- of `Finset.card_insert_of_notMem` applications driven by the unpacked `h`.

        -- Names for each pair (i, j) with i < j. Used both to destructure `h` and to
        -- feed into the `simp` calls that discharge each `aᵢ ∉ {aᵢ₊₁,...,aₙ}` side.
        let mut pairNames : Array Ident := #[]
        let mut neqStxs : Array (TSyntax `term) := #[]
        for i in [:n] do
          for j in [i+1:n] do
            pairNames := pairNames.push (mkIdent (Name.mkSimple s!"h_{i}_{j}"))
            let piStx ← PrettyPrinter.delab points[i]!
            let pjStx ← PrettyPrinter.delab points[j]!
            neqStxs := neqStxs.push (← `($piStx ≠ $pjStx))

        -- Right-associated conjunction: a ∧ (b ∧ (c ∧ ...))
        let mut conjStx : TSyntax `term := neqStxs[neqStxs.size - 1]!
        for k in [1:neqStxs.size] do
          let stx := neqStxs[neqStxs.size - 1 - k]!
          conjStx ← `($stx ∧ $conjStx)

        -- Build the rw chain for the suffices-body. At level i (0 ≤ i < n-1),
        -- we discharge `aᵢ ∉ {aᵢ₊₁,...,aₙ}` via `simp` using the inequalities
        -- `h_i_{i+1}, ..., h_i_{n-1}`.
        let mut rwArgs : Array (TSyntax `Lean.Parser.Tactic.rwRule) := #[]
        let mut pairIdx := 0
        for i in [:n-1] do
          let levelCount := n - 1 - i
          let mut levelLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
          for k in [:levelCount] do
            let nm := pairNames[pairIdx + k]!
            levelLemmas := levelLemmas.push (← `(Lean.Parser.Tactic.simpLemma| $nm:ident))
          pairIdx := pairIdx + levelCount
          rwArgs := rwArgs.push (← `(Lean.Parser.Tactic.rwRule|
            Finset.card_insert_of_notMem (by simp [$levelLemmas,*])))
        rwArgs := rwArgs.push (← `(Lean.Parser.Tactic.rwRule| Finset.card_singleton))

        evalTactic (← `(tactic| (
          refine Distinct.mk ?_
          suffices h : $conjStx by
            obtain ⟨$pairNames,*⟩ := h
            rw [$rwArgs,*])))


-- EXAMPLES and TESTS

example {α : Type*} [DecidableEq α] (A B : α) (_h : distinct A B) : True := True.intro
example {α : Type*} [DecidableEq α] (A B C : α) (_h : distinct A B C) : True := True.intro


end Distinct
end Geometry.Theory
