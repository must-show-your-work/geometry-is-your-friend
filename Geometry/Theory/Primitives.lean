import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs

/-!
# Primitives

Foundational opaque types and the universal relations / notations that the
rest of the theory layers over: `Point`, `Line` (as a set of points), the
`on` / `off` / `has` / `avoids` membership family, and the bare `Between`
relation with its `-` infix notation.

Everything here is type/relation *declaration* — no axioms about how these
behave. The axioms about incidence live in `Geometry/Theory/Axioms/Incidence.lean`;
the axioms about betweenness live in `Geometry/Theory/Axioms/Betweenness.lean`.
-/

namespace Geometry.Theory

/-- A point is the fundamental, opaque type we're working with. -/
axiom Point : Type

/-- Greenberg reasons classically throughout. Granting decidable equality on `Point`
    via `Classical.decEq` lets us use `Finset Point` and the associated decidable
    membership/cardinality machinery. -/
noncomputable instance : DecidableEq Point := Classical.decEq Point

/-- Ed: In the text, the author ends up using the 'Line is a Set of points' to define segments, rays, and implicitly
uses the intuitive idea ("A line is the set of collinear points that contain at least two known points"). However, Ch2
uses an opaque 'Line' type and reasons only about it's properties without definition. I try to replicate this in my
implementation of Ch2, but do define it as a set 'up front'.

`Line` is now an opaque-ish structure wrapping a `Set Point`. The `.toSet`
projection gives the underlying set view; instances below let `L ∩ M`,
`P ∈ L`, `L ⊆ M` etc. work the same way they did when `Line` was reducibly
`Set Point`. This shuns the implicit set-theoretic identity per Greenberg's
Tarski gesture, while preserving the surface syntax. -/
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

/-- `P ∈ L` (typed Line) unfolds to `P ∈ L.toSet` definitionally — Iff.rfl
    bridge for tactics. -/
@[simp, obvious] theorem Line.mem_def {L : Line} {P : Point} : P ∈ L ↔ P ∈ L.toSet := Iff.rfl

@[simp, obvious] theorem Line.subset_def {L M : Line} : L ⊆ M ↔ L.toSet ⊆ M.toSet := Iff.rfl

@[simp, obvious] theorem Line.inter_toSet (L M : Line) : (L ∩ M).toSet = L.toSet ∩ M.toSet := rfl

@[simp, obvious] theorem Line.union_toSet (L M : Line) : (L ∪ M).toSet = L.toSet ∪ M.toSet := rfl

@[simp, obvious] theorem Line.empty_toSet : (∅ : Line).toSet = ∅ := rfl

@[simp, obvious] theorem Line.singleton_toSet (P : Point) : ({P} : Line).toSet = {P} := rfl

/-- `Line` equality reduces to `.toSet` equality (the wrapper is a one-field
    structure, so two Lines are equal iff their carriers are). -/
@[ext] theorem Line.ext_set {L M : Line} (h : L.toSet = M.toSet) : L = M := by
  cases L; cases M; congr

theorem Line.eq_iff_toSet {L M : Line} : L = M ↔ L.toSet = M.toSet :=
  ⟨fun h => by rw [h], Line.ext_set⟩

/-- Singleton-line equality reduces to point equality. -/
@[simp, obvious] theorem Line.singleton_eq_singleton {P Q : Point} :
    ({P} : Line) = ({Q} : Line) ↔ P = Q := by
  rw [Line.eq_iff_toSet]; simp [Line.singleton_toSet, Set.singleton_eq_singleton_iff]

/-- Membership in a singleton Line. -/
@[simp, obvious] theorem Line.mem_singleton {P Q : Point} :
    P ∈ ({Q} : Line) ↔ P = Q := by
  simp [Line.mem_def]

/-- Intersection of Lines is commutative. -/
theorem Line.inter_comm (L M : Line) : L ∩ M = M ∩ L := by
  ext; simp [Set.mem_inter_iff, And.comm]

/-- Antisymmetry of `⊆` on `Line`. Standin for `Subset.antisymm` (which is
    Set-typed) at proof sites where the goal is `L = M` for Lines. -/
theorem Line.eq_of_subset {L M : Line} (h₁ : L ⊆ M) (h₂ : M ⊆ L) : L = M :=
  Line.ext_set (Set.Subset.antisymm h₁ h₂)

/-- Pointwise membership in a Line intersection / union. -/
@[simp, obvious] theorem Line.mem_inter {L M : Line} {P : Point} :
    P ∈ L ∩ M ↔ P ∈ L ∧ P ∈ M := Set.mem_inter_iff P L.toSet M.toSet

@[simp, obvious] theorem Line.mem_union {L M : Line} {P : Point} :
    P ∈ L ∪ M ↔ P ∈ L ∨ P ∈ M := Set.mem_union P L.toSet M.toSet

@[simp, obvious] theorem Line.not_mem_empty {P : Point} : P ∉ (∅ : Line) := by
  simp [Line.mem_def]

-- TODO: Review binding values for all this notation
syntax:50 (name := onNotation) term:51 " on " term:50 : term

-- Macro rules for "on" notation — start with the bare `P on L` case; the
-- segment/ray/extension/line cases are added in `Geometry/Theory/Constructors.lean`.
macro_rules (kind := onNotation)
  | `($P on $L) => `($P ∈ $L)

notation:80 P:81 " off " L:81 => P ∉ L
notation:80 L:81 " has " P:81 => P ∈ L
notation:80 L:81 " avoids " P:81 => P ∉ L

/-! ## Betweenness primitive -/

/-- Bare betweenness relation. Axioms about its behavior live in
    `Geometry/Theory/Axioms/Betweenness.lean`. -/
axiom Between : Point -> Point -> Point -> Prop
-- Ed: In the text, the author uses `*`, but Lean reserves that, so I've chosen `-`. `∗` is available, but I don't want
-- to type `\ast` every time.
notation:65 A:66 " - " B:66 " - " C:65 => Between A B C

syntax:65 (name := arrangementChain)
  term:66 " - " term:66 " - " term:66 " - " term:66 (" - " term:66)* : term

macro_rules
  | `($a:term - $b:term - $c:term - $d:term $[- $rest:term]*) =>
    `(Geometry.Theory.Arrangement [$a, $b, $c, $d, $rest,*])

/-! ## Examples -/

section Examples
variable (P : Point) (L : Line) (A B C : Point)

example : (P on L) ↔ (P ∈ L) := Iff.rfl
example : (P off L) ↔ (P ∉ L) := Iff.rfl
example : (L has P) ↔ (P ∈ L) := Iff.rfl
example : (L avoids P) ↔ (P ∉ L) := Iff.rfl
example : (A - B - C) ↔ Between A B C := Iff.rfl
end Examples

end Geometry.Theory
