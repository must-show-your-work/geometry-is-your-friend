/- The `forgetting` operator: drops named elements from a `Distinct` or `Collinear`
   over `Finset`. Under Finset the operation is just `Finset.erase`, and the
   side conditions are decidable. -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Erase
import Mathlib.Data.Finset.Card

import Geometry.Theory.Axioms
import Geometry.Theory.Distinct
import Geometry.Theory.Collinear.Ch1

import Geometry.Tactics

namespace Geometry.Theory

namespace Forgetting

open Lean Meta Elab Term

syntax term " forgetting " ident+ : term

/-- `forgetting`: drops named elements from a `Distinct` or `Collinear` Finset.
    Single-element: dispatches to `Collinear.subset` or `Distinct.erase_step`.
    Multi-element: chained via left-associative single-element applications.

    When the consumer expects a Finset literal in a different insertion order than
    `s.erase X` reduces to, we fall back to `.of_eq` and discharge the Finset
    equality via `Finset.eq_of_subset_of_card_le`: the subset direction
    (`s.erase X ⊆ target`) needs only forward disjunctive reasoning (no `Ne.symm`,
    so `tauto` works), and the cardinality side is closed by simp + omega.

    Multi-element calls chain left-associatively. Type-dispatch happens via
    elaboration on `$col`'s type, so `Distinct`-specific machinery (`DecidableEq`,
    `card_eq`) doesn't get applied to `Collinear` hypotheses. -/
elab_rules : term
  | `($col forgetting $p:ident) => do
    let colExpr ← elabTerm col none
    let colType ← instantiateMVars (← inferType colExpr)
    let colType := colType.consumeMData
    if colType.isAppOfArity ``Geometry.Theory.Collinear 1 then
      let stx ← `(by
        first
        | exact Collinear.subset $col (Finset.erase_subset $p _)
        | (refine Collinear.of_eq (Collinear.subset $col (Finset.erase_subset $p _)) ?_;
           apply Finset.eq_of_subset_of_card_le
           · intro x hx;
             simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx ⊢;
             tauto
           · rw [Finset.card_erase_of_mem (by simp)];
             simp_all [Finset.card_insert_eq_ite, Finset.card_singleton,
                       Finset.mem_insert, Finset.mem_singleton, eq_comm]
             try omega))
      elabTerm stx none
    else if colType.isAppOfArity ``Geometry.Theory.Distinct 3 then
      let stx ← `(by
        first
        | exact Distinct.erase_step (a := $p) $col (by simp)
        | (refine Distinct.of_eq (Distinct.erase_step (a := $p) $col (by simp)) ?_;
           apply Finset.eq_of_subset_of_card_le
           · intro x hx;
             simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hx ⊢;
             tauto
           · rw [Finset.card_erase_of_mem (by simp), ($col).card_eq];
             simp only [Finset.card_insert_eq_ite, Finset.card_singleton,
                        Finset.mem_insert, Finset.mem_singleton];
             split_ifs <;> omega))
      elabTerm stx none
    else
      throwError "forgetting: expected `Collinear _` or `Distinct _ _` term, got {colType}"
  | `($col forgetting $p:ident $q:ident $ps:ident*) => do
    let stx ← `(($col forgetting $p) forgetting $q $ps*)
    elabTerm stx none


-- Tests

example (A B C : Point) (c : collinear A B C) : Collinear (({A, B, C} : Finset _).erase B) :=
  c forgetting B

end Forgetting

end Geometry.Theory
