/- Lemmas relating to collinearity requiring only the content of Ch1 -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Line.Ch2

import Geometry.Tactics
import Geometry.Ch2.Prop

namespace Geometry.Theory

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Lean Expr Meta Elab.Term

namespace Forgetting

private partial def filterForgotten (forgottenExprs : List Expr) (e : Expr) : MetaM Expr := do
  if e.isAppOfArity ``List.cons 3 then
    let head := e.appFn!.appArg!
    let tail := e.appArg!
    let filteredTail ← filterForgotten forgottenExprs tail
    let forgotten ← forgottenExprs.anyM (fun f => isDefEq head f)
    if forgotten then
      return filteredTail
    else
      mkAppM ``List.cons #[head, filteredTail]
  else
    return e

private partial def buildSublistProof (forgottenExprs : List Expr) (filtered original : Expr) : MetaM Expr := do
  if original.isAppOfArity ``List.cons 3 then
    let head := original.appFn!.appArg!
    let tail := original.appArg!
    let forgotten ← forgottenExprs.anyM (fun f => isDefEq head f)
    if forgotten then
      let rest ← buildSublistProof forgottenExprs filtered tail
      mkAppOptM ``List.Sublist.cons #[none, none, none, some head, some rest]
    else
      -- filtered must also be cons since head is kept
      if filtered.isAppOfArity ``List.cons 3 then
        let filteredTail := filtered.appArg!
        let rest ← buildSublistProof forgottenExprs filteredTail tail
        mkAppOptM ``List.Sublist.cons₂ #[none, none, none, some head, some rest]
      else
        throwError "buildSublistProof: filtered list shorter than expected"
  else
    let α := original.appArg!
    mkAppOptM ``List.Sublist.slnil #[some α]

syntax term " forgetting " ident,+ : term

elab_rules : term
  | `($col forgetting $[$ps],*) => do
    let colExpr ← elabTerm col none
    let colType ← inferType colExpr
    let forgottenExprs ← ps.toList.mapM (fun p => elabTerm p none)
    if isAppOfArity colType ``Collinear 1 then
      let listExpr := colType.getAppArgs[0]!
      let filteredList ← filterForgotten forgottenExprs listExpr
      let sublistProof ← buildSublistProof forgottenExprs filteredList listExpr
      mkAppM ``Collinear.sublist #[colExpr, sublistProof]
    else if isAppOfArity colType ``Distinct 2 then
      let listExpr := colType.getAppArgs[1]!
      let α := colType.getAppArgs[0]!
      let filteredList ← filterForgotten forgottenExprs listExpr
      let sublistProof ← buildSublistProof forgottenExprs filteredList listExpr
      mkAppOptM ``Distinct.sublist #[some α, none, none, some colExpr, some sublistProof]
    else
      throwError "forgetting: expected Collinear or Distinct, got {colType}"


example : distinct A B C D -> distinct A B C := by
  intro dABCD
  exact dABCD forgetting D

example : distinct A B C D E F G H I J -> distinct A B C D E F G H := by
  intro dABCD
  exact (dABCD forgetting J) forgetting I

example : distinct A B C D E F G H I J -> distinct A B C D E F G H := by
  intro dABCD
  exact dABCD forgetting I, J

end Forgetting

end Geometry.Theory

