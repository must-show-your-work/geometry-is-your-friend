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
