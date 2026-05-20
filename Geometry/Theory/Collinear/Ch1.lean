
/- Lemmas relating to collinearity requiring only the content of Ch1, now over Finset. -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert

import Geometry.Tactics
import Geometry.Theory.Axioms
import Atlas

-- There is no overlap here, so it's fine to import
import Geometry.Theory.Point.Ch1

namespace Geometry.Theory

open Set
open Geometry.Theory
open Atlas

namespace Collinear

/-- collinear points can be used in place of a line by using the induced line -/
noncomputable instance : Coe {s : Finset Point // Collinear s} Line where
  coe := fun ⟨_, h⟩ => h.line

noncomputable instance collinearCoe {points : Finset Point} (h : Collinear points) : CoeDep (Collinear points) h Line where
  coe := h.line

-- Natural projections on Collinear values — not book content, not atlas'd.

/-- a subset of a collinear set of points is collinear -/
@[simp] lemma subset {s s' : Finset Point} (h : Collinear s) (hs : s' ⊆ s) : Collinear s' :=
  ⟨h.line, fun p hp => h.on_line p (hs hp)⟩

/-- Cast `Collinear` between propositionally-equal Finsets — Finsets are unordered,
    so two literals describing the same elements are equal even when they don't unify
    definitionally. Useful when stitching together facts produced under different
    insertion orders (e.g. `ref lemma 1.0.40 (CAB : C - A - B)` yields
    `Collinear {C, A, B}` but a consumer wants `Collinear {A, B, C}`). -/
lemma of_eq {s t : Finset Point} (c : Collinear s) (h : s = t) : Collinear t := h ▸ c

atlas commentary := by
  ref lemma 1.0.14
  name "Any two distinct points are collinear"
  preface "There is a line between any two points, so by definition any two points are collinear"

atlas lemma 1.0.14 "Any two distinct points are collinear"
  : A ≠ B -> collinear A B := by
  intro AneB
  have ⟨L, ⟨AonL, BonL⟩, _h⟩ := ref axiom I.1 A B AneB
  unfold Collinear
  use L
  intro P PinSub
  simp only [Finset.mem_insert, Finset.mem_singleton] at PinSub
  rcases PinSub with eq | eq
  repeat rwa [eq]

attribute [simp] «Any two distinct points are collinear»

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

atlas lemma 1.0.16 "Collinearity ignores trailing duplicate point (A B B ↔ A B)"
  (A B : Point) : collinear A B B ↔ collinear A B := by
  constructor
  · intro h; exact Collinear.order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton])
  · intro h; exact Collinear.order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton])

attribute [simp] «Collinearity ignores trailing duplicate point (A B B ↔ A B)»

atlas lemma 1.0.17 "Collinearity ignores interleaved duplicate point (B A B ↔ A B)"
  (A B : Point) : collinear B A B ↔ collinear A B := by
  constructor
  · intro h; exact Collinear.order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton]; try tauto)
  · intro h; exact Collinear.order_irrelevance h (by intro p; simp [Finset.mem_insert, Finset.mem_singleton]; try tauto)

attribute [simp] «Collinearity ignores interleaved duplicate point (B A B ↔ A B)»

end Collinear

end Geometry.Theory
