import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs

namespace Geometry.Theory

/-- A point is the fundamental, opaque type we're working with. -/
axiom Point : Type

/-- Greenberg reasons classically throughout. Granting decidable equality on `Point`
    via `Classical.decEq` lets us use `Finset Point` and the associated decidable
    membership/cardinality machinery. -/
noncomputable instance : DecidableEq Point := Classical.decEq Point

structure Line where
  toSet : Set Point

instance : Membership Point Line where
  mem L P := P ∈ L.toSet

instance : HasSubset Line where
  Subset L M := L.toSet ⊆ M.toSet

instance : Inter Line where
  inter L M := ⟨L.toSet ∩ M.toSet⟩

instance : Union Line where
  union L M := ⟨L.toSet ∪ M.toSet⟩

instance : EmptyCollection Line where
  emptyCollection := ⟨∅⟩

instance : Singleton Point Line where
  singleton p := ⟨{p}⟩

@[simp, obvious] theorem Line.mem_def {L : Line} {P : Point} : P ∈ L ↔ P ∈ L.toSet := Iff.rfl

@[simp, obvious] theorem Line.subset_def {L M : Line} : L ⊆ M ↔ L.toSet ⊆ M.toSet := Iff.rfl

@[simp, obvious] theorem Line.inter_toSet (L M : Line) : (L ∩ M).toSet = L.toSet ∩ M.toSet := rfl

@[simp, obvious] theorem Line.union_toSet (L M : Line) : (L ∪ M).toSet = L.toSet ∪ M.toSet := rfl

@[simp, obvious] theorem Line.empty_toSet : (∅ : Line).toSet = ∅ := rfl

@[simp, obvious] theorem Line.singleton_toSet (P : Point) : ({P} : Line).toSet = {P} := rfl

@[ext] theorem Line.ext_set {L M : Line} (h : L.toSet = M.toSet) : L = M := by
  cases L; cases M; congr

theorem Line.eq_iff_toSet {L M : Line} : L = M ↔ L.toSet = M.toSet :=
  ⟨fun h => by rw [h], Line.ext_set⟩

@[simp, obvious] theorem Line.singleton_eq_singleton {P Q : Point} :
    ({P} : Line) = ({Q} : Line) ↔ P = Q := by
  rw [Line.eq_iff_toSet]; simp [Line.singleton_toSet, Set.singleton_eq_singleton_iff]

@[simp, obvious] theorem Line.mem_singleton {P Q : Point} :
    P ∈ ({Q} : Line) ↔ P = Q := by
  simp [Line.mem_def]

theorem Line.inter_comm (L M : Line) : L ∩ M = M ∩ L := by
  ext; simp [Set.mem_inter_iff, And.comm]

theorem Line.eq_of_subset {L M : Line} (h₁ : L ⊆ M) (h₂ : M ⊆ L) : L = M :=
  Line.ext_set (Set.Subset.antisymm h₁ h₂)

@[simp, obvious] theorem Line.mem_inter {L M : Line} {P : Point} :
    P ∈ L ∩ M ↔ P ∈ L ∧ P ∈ M := Set.mem_inter_iff P L.toSet M.toSet

@[simp, obvious] theorem Line.mem_union {L M : Line} {P : Point} :
    P ∈ L ∪ M ↔ P ∈ L ∨ P ∈ M := Set.mem_union P L.toSet M.toSet

@[simp, obvious] theorem Line.not_mem_empty {P : Point} : P ∉ (∅ : Line) := by
  simp [Line.mem_def]

syntax:50 (name := onNotation) term:51 " on " term:50 : term

macro_rules (kind := onNotation)
  | `($P on $L) => `($P ∈ $L)

-- Goal-state display: `Line` membership unfolds via the instance body
-- (`mem L P := P ∈ L.toSet`), which leaks `.toSet` into proof states like
-- `P ∈ (segment A B).toSet`. The unexpander below strips the projection
-- so `Line.toSet L` renders as just `L`, and the surrounding membership
-- collapses back to `P ∈ L` (further turned into `P on L` by the
-- `Membership.mem` delab below).
@[app_unexpander Geometry.Theory.Line.toSet]
def Line.toSet.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $L) => `($L)
  | _        => throw ()

-- Render `P ∈ L.toSet` (the unfolded form of Line membership — Lean
-- inlines the `instance Membership Point Line` body before delab sees
-- it, so the type arg is `Set Point`, not `Line`) as `P on L`. We
-- detect the Line layer via the *collection* shape (`Line.toSet X`).
open Lean PrettyPrinter.Delaborator SubExpr in
@[app_delab Membership.mem]
def delabMembershipOnLine : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``Membership.mem 5
  let collection := e.getArg! 3
  guard <| collection.isAppOfArity ``Geometry.Theory.Line.toSet 1
  let element ← withNaryArg 4 delab
  let lineStx ← withNaryArg 3 (withNaryArg 0 delab)
  `($element on $lineStx)

notation:80 P:81 " off " L:81 => P ∉ L
notation:80 L:81 " has " P:81 => P ∈ L
notation:80 L:81 " avoids " P:81 => P ∉ L

axiom Between : Point -> Point -> Point -> Prop

-- Ed: In the text, the author uses `*`, but Lean reserves that, so I've chosen `-`. `∗` is available, but I don't want
-- to type `\ast` every time.
syntax:65 (name := dashChain)
  term:66 " - " term:66 " - " term:66 (" - " term:66)* : term

macro_rules (kind := dashChain)
  | `($a:term - $b:term - $c:term) => `(Between $a $b $c)

open Lean PrettyPrinter.Delaborator SubExpr in
@[app_delab Geometry.Theory.Between]
def delabBetween : Delab := do
  guard <| (← getExpr).isAppOfArity ``Geometry.Theory.Between 3
  let a ← withNaryArg 0 delab
  let b ← withNaryArg 1 delab
  let c ← withNaryArg 2 delab
  `($a - $b - $c)

/- Examples -/

section Examples
variable (P : Point) (L : Line) (A B C : Point)

example : (P on L) ↔ (P ∈ L) := Iff.rfl
example : (P off L) ↔ (P ∉ L) := Iff.rfl
example : (L has P) ↔ (P ∈ L) := Iff.rfl
example : (L avoids P) ↔ (P ∉ L) := Iff.rfl
example : (A - B - C) ↔ Between A B C := Iff.rfl
end Examples

end Geometry.Theory
