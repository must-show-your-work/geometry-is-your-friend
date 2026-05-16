
/- Lemmas relating to intersections using theory from Ch3 -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Theory.Intersection.Ch1
import Geometry.Theory.Intersection.Ch2
import Geometry.Theory.Line.Ch2
import Geometry.Tactics

namespace Geometry.Theory

open Set
open Geometry.Theory

namespace Intersection

/-- If `L intersects M` and `A` lies on both, then either the intersection happens
    at `A` specifically (`L intersects M at A`) or the two coincide.

    `intersects` is the weak ("nonempty intersection") form, so the proof needs
    `line_trichotomy` to pin down which of the three cases obtains; `A ∈ L ∩ M`
    rules out the empty branch, leaving either the unique-point branch (which
    must be `A`) or the coincident branch. -/
lemma specification {L M : Set Point} {A : Point} :
    L intersects M -> A on L ∧ A on M -> L intersects M at A ∨ L = M := by
  intro _LintM ⟨AonL, AonM⟩
  have AinInt : A ∈ L ∩ M := ⟨AonL, AonM⟩
  rcases Line.line_trichotomy L M with empty | unique | equal
  · exfalso; rw [empty] at AinInt; exact AinInt
  · left
    obtain ⟨X, hX, _⟩ := unique
    rw [hX] at AinInt
    have AeqX : A = X := AinInt
    change L ∩ M = {A}
    rw [hX, AeqX]
  · right; exact equal

/-- A line trivially intersects itself everywhere. -/
lemma coincident_lines_intersect_everywhere : L intersects L := by
  unfold IntersectsSome
  by_contra! hNeg
  rw [Set.inter_self] at hNeg
  obtain ⟨A, _, _, AonL, _⟩ := I2 L
  rw [hNeg] at AonL
  contradiction


end Intersection

end Geometry.Theory
