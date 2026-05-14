/- The `arranged` operator: rearranges a Distinct or Collinear list to a target ordering.
   Mirrors the `forgetting` operator in `Forgetting.lean`, but constructs a `List.Perm` witness
   instead of a `List.Sublist` witness, and dispatches to `Distinct.perm` / `Collinear.perm`. -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Distinct
import Geometry.Theory.Forgetting
import Geometry.Theory.Collinear.Ch1
import Geometry.Theory.Line.Ch2

import Geometry.Tactics
import Geometry.Ch2.Prop

namespace Geometry.Theory

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Lean Expr Meta Elab.Term

namespace Arranged

/-- Build a `List α` expression from a list of element expressions. -/
private partial def buildList (α : Expr) (elems : List Expr) : MetaM Expr := do
  match elems with
  | [] => mkAppOptM ``List.nil #[some α]
  | x :: xs =>
    let tail ← buildList α xs
    mkAppM ``List.cons #[x, tail]

/-- Find `target` somewhere in `source` and produce a `List.Perm` proof witnessing
    `source ~ (target :: rest)`, returning both the proof and `rest`. -/
private partial def extractFromSource (α : Expr) (target : Expr) (source : Expr) :
    MetaM (Expr × Expr) := do
  if source.isAppOfArity ``List.cons 3 then
    let head := source.appFn!.appArg!
    let tail := source.appArg!
    if (← isDefEq head target) then
      -- source = target :: tail; witness is `Perm.refl source`.
      let refl ← mkAppOptM ``List.Perm.refl #[some α, some source]
      return (refl, tail)
    else
      -- Recurse on tail to extract target, then bubble head past target via swap.
      let (tailProof, tailRest) ← extractFromSource α target tail
      -- tailProof : tail ~ (target :: tailRest)
      let consProof ← mkAppOptM ``List.Perm.cons #[some α, some head, none, none, some tailProof]
      -- consProof : (head :: tail) ~ (head :: target :: tailRest)
      let swapProof ← mkAppOptM ``List.Perm.swap #[some α, some target, some head, some tailRest]
      -- swapProof : (head :: target :: tailRest) ~ (target :: head :: tailRest)
      let composed ← mkAppOptM ``List.Perm.trans
        #[some α, none, none, none, some consProof, some swapProof]
      let newRest ← mkAppM ``List.cons #[head, tailRest]
      return (composed, newRest)
  else
    throwError "arranged: target element not found in source list"

/-- Build a `List.Perm source target` witness, assuming the two lists are permutations
    of each other. Fails if `target` contains an element not present in `source` (or if
    the multiplicities don't match). -/
private partial def buildPermProof (α : Expr) (source target : Expr) : MetaM Expr := do
  if target.isAppOfArity ``List.nil 1 then
    if source.isAppOfArity ``List.nil 1 then
      mkAppOptM ``List.Perm.refl #[some α, some source]
    else
      throwError "arranged: source has more elements than target"
  else if target.isAppOfArity ``List.cons 3 then
    let head := target.appFn!.appArg!
    let targetTail := target.appArg!
    let (sourceFront, sourceRest) ← extractFromSource α head source
    -- sourceFront : source ~ (head :: sourceRest)
    let tailProof ← buildPermProof α sourceRest targetTail
    -- tailProof : sourceRest ~ targetTail
    let consProof ← mkAppOptM ``List.Perm.cons
      #[some α, some head, none, none, some tailProof]
    -- consProof : (head :: sourceRest) ~ (head :: targetTail) = target
    mkAppOptM ``List.Perm.trans
      #[some α, none, none, none, some sourceFront, some consProof]
  else
    throwError "arranged: unexpected target list structure"

syntax term " arranged " ident+ : term

elab_rules : term
  | `($col arranged $ps*) => do
    let colExpr ← elabTerm col none
    let colType ← inferType colExpr
    let targetElems ← ps.toList.mapM (fun p => elabTerm p none)
    if isAppOfArity colType ``Collinear 1 then
      let sourceList := colType.getAppArgs[0]!
      let α := Lean.mkConst ``Geometry.Theory.Point
      let targetList ← buildList α targetElems
      let permProof ← buildPermProof α sourceList targetList
      mkAppM ``Collinear.perm #[colExpr, permProof]
    else if isAppOfArity colType ``Distinct 2 then
      let α := colType.getAppArgs[0]!
      let sourceList := colType.getAppArgs[1]!
      let targetList ← buildList α targetElems
      let permProof ← buildPermProof α sourceList targetList
      mkAppOptM ``Distinct.perm
        #[some α, none, none, some colExpr, some permProof]
    else
      throwError "arranged: expected Collinear or Distinct, got {colType}"


-- Tests

example : distinct A B C D E -> distinct E D C B := by
  intro distinctABCDE
  exact distinctABCDE forgetting A arranged E D C B

example : distinct A B C -> distinct C B A := by
  intro h
  exact h arranged C B A

example : collinear A B C D -> collinear D A C B := by
  intro h
  exact h arranged D A C B

example : distinct A B C D E -> distinct E A D B C := by
  intro h
  exact h arranged E A D B C


end Arranged

end Geometry.Theory
