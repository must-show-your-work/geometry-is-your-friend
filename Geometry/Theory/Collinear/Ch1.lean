
/- Lemmas relating to collinearity requiring only the content of Ch1 -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Data.List.Basic

import Geometry.Tactics
import Geometry.Theory.Axioms

-- There is no overlap here, so it's fine to import
import Geometry.Theory.Point.Ch1

namespace Geometry.Theory

open Set
open Geometry.Theory

namespace Collinear

/-- collinear points can be used in place of a line by using the induced line -/
noncomputable instance : Coe {l : List Point // Collinear l} Line where
  coe := fun ⟨_, h⟩ => h.line

noncomputable instance collinearCoe {points : List Point} (h : Collinear points) : CoeDep (Collinear points) h Line where
  coe := h.line

/-- a sublist of a list of collinear points is collinear -/
@[simp] lemma sublist {l l' : List Point} (h : Collinear l) (hs : List.Sublist l' l) : Collinear l' :=
  ⟨h.line, fun p hp => h.on_line p (hs.subset hp)⟩

/-- a permutation of a list of collinear points is collinear -/
@[simp] lemma perm {l l' : List Point} (c : Collinear l) (h : l.Perm l') : Collinear l' :=
  ⟨c.line, fun p hp => c.on_line p (h.mem_iff.mpr hp)⟩

/-- There is a line between any two points, so by definition any two points are collinear -/
@[simp] lemma any_two_points_are_collinear : A ≠ B -> collinear A B := by
  intro AneB
  have ⟨L, ⟨AonL, BonL⟩, _h⟩ := I1 A B AneB
  unfold Collinear
  use L
  intro P PinSub
  simp only [List.mem_cons, List.not_mem_nil, or_false] at PinSub
  rcases PinSub with eq | eq
  repeat rwa [eq]

/-- Collinearity is independent of list order -/
@[simp] lemma order_irrelevance {S T : List Point}
    (leftCol : Collinear S)
    (samePoints : (∀ p, p ∈ S ↔ p ∈ T) := by aesop) :
  Collinear T := by
  obtain ⟨L, hL⟩ := leftCol
  use L
  intro p hp
  exact hL p ((samePoints p).mpr hp)

@[simp] lemma redundancy_irrelevance_ABB (A B : Point) : collinear A B B ↔ collinear A B := by
  constructor
  · intro colABB
    unfold Collinear at colABB
    have ⟨L, cond⟩ := colABB
    use L; intro P PonAB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at PonAB
    have ⟨AonL, BonL⟩ : A on L ∧ B on L := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self, forall_eq_or_imp,
        forall_eq] at cond;
      exact cond
    rcases PonAB with eq | eq
    repeat rwa [eq]
  · intro colAB
    unfold Collinear
    have ⟨L, h⟩ := colAB
    use L
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, or_self]
    trivial

@[simp] lemma redundancy_irrelevance_BAB (A B : Point) : collinear B A B ↔ collinear A B := by
  constructor
  · intro colABB
    unfold Collinear at colABB
    have ⟨L, cond⟩ := colABB
    use L; intro P PonAB
    simp only [List.mem_cons, List.not_mem_nil, or_false] at PonAB
    have ⟨AonL, BonL⟩ : A on L ∧ B on L := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at cond;
      have ⟨_, AonL, BonL⟩ := cond
      exact ⟨AonL, BonL⟩
    rcases PonAB with eq | eq
    repeat rwa [eq]
  · intro colAB
    unfold Collinear
    have ⟨L, h⟩ := colAB
    use L
    simp_all only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    trivial

example (h : collinear A B C) : collinear C B A := order_irrelevance h

end Collinear

end Geometry.Theory
