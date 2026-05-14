
/- Lemmas relating to collinearity requiring only the content of Ch1, now over Finset. -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert

import Geometry.Tactics
import Geometry.Theory.Axioms

-- There is no overlap here, so it's fine to import
import Geometry.Theory.Point.Ch1

namespace Geometry.Theory

open Set
open Geometry.Theory

namespace Collinear

/-- collinear points can be used in place of a line by using the induced line -/
noncomputable instance : Coe {s : Finset Point // Collinear s} Line where
  coe := fun ⟨_, h⟩ => h.line

noncomputable instance collinearCoe {points : Finset Point} (h : Collinear points) : CoeDep (Collinear points) h Line where
  coe := h.line

/-- a subset of a collinear set of points is collinear -/
@[simp] lemma subset {s s' : Finset Point} (h : Collinear s) (hs : s' ⊆ s) : Collinear s' :=
  ⟨h.line, fun p hp => h.on_line p (hs hp)⟩

/-- Cast `Collinear` between propositionally-equal Finsets — Finsets are unordered,
    so two literals describing the same elements are equal even when they don't unify
    definitionally. Useful when stitching together facts produced under different
    insertion orders (e.g. `Betweenness.abc_imp_collinear (CAB : C - A - B)` yields
    `Collinear {C, A, B}` but a consumer wants `Collinear {A, B, C}`). -/
lemma of_eq {s t : Finset Point} (c : Collinear s) (h : s = t) : Collinear t := h ▸ c

/-- There is a line between any two points, so by definition any two points are collinear -/
@[simp] lemma any_two_points_are_collinear : A ≠ B -> collinear A B := by
  intro AneB
  have ⟨L, ⟨AonL, BonL⟩, _h⟩ := I1 A B AneB
  unfold Collinear
  use L
  intro P PinSub
  simp only [Finset.mem_insert, Finset.mem_singleton] at PinSub
  rcases PinSub with eq | eq
  repeat rwa [eq]

/-- Collinearity is independent of underlying set representation; Finsets with the
    same membership are equal, so this collapses to reflexivity through `Finset.ext`. -/
@[simp] lemma order_irrelevance {S T : Finset Point}
    (leftCol : Collinear S)
    (samePoints : ∀ p, p ∈ S ↔ p ∈ T := by aesop) :
  Collinear T := by
  obtain ⟨L, hL⟩ := leftCol
  use L
  intro p hp
  exact hL p ((samePoints p).mpr hp)

@[simp] lemma redundancy_irrelevance_ABB (A B : Point) : collinear A B B ↔ collinear A B := by
  constructor
  · intro h; exact order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton])
  · intro h; exact order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton])

@[simp] lemma redundancy_irrelevance_BAB (A B : Point) : collinear B A B ↔ collinear A B := by
  constructor
  · intro h; exact order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton]; try tauto)
  · intro h; exact order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton]; try tauto)

end Collinear

end Geometry.Theory
