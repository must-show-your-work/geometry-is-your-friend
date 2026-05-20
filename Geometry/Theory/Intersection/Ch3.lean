
/- Lemmas relating to intersections using theory from Ch3 -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Theory.Intersection.Ch1
import Geometry.Theory.Intersection.Ch2
import Geometry.Theory.Line.Ch2
import Geometry.Tactics
import Atlas

namespace Geometry.Theory

open Set
open Geometry.Theory
open Atlas

namespace Intersection

atlas commentary := by
  ref lemma 3.0.1
  name "Bare intersection plus a shared point implies pointed intersection or coincidence"
  preface "If `L intersects M` and `A` lies on both, then either the intersection happens
at `A` specifically (`L intersects M at A`) or the two coincide."
  notes "`intersects` is the weak (\"nonempty intersection\") form, so the proof needs
`line_trichotomy` to pin down which of the three cases obtains; `A ∈ L ∩ M`
rules out the empty branch, leaving either the unique-point branch (which
must be `A`) or the coincident branch."

atlas lemma 3.0.1 "Bare intersection plus a shared point implies pointed intersection or coincidence"
  {L M : Set Point} {A : Point} :
    L intersects M -> A on L ∧ A on M -> L intersects M at A ∨ L = M := by
  intro _LintM ⟨AonL, AonM⟩
  have AinInt : A ∈ L ∩ M := ⟨AonL, AonM⟩
  rcases ref lemma 2.0.1 L M with empty | unique | equal
  · exfalso; rw [empty] at AinInt; exact AinInt
  · left
    obtain ⟨X, hX, _⟩ := unique
    rw [hX] at AinInt
    have AeqX : A = X := AinInt
    change L ∩ M = {A}
    rw [hX, AeqX]
  · right; exact equal


atlas commentary := by
  ref lemma 3.0.2
  name "A line intersects itself (bare intersection of L with L)"
  preface "A line trivially intersects itself everywhere."

atlas lemma 3.0.2 "A line intersects itself (bare intersection of L with L)"
  : L intersects L := by
  unfold IntersectsSome
  by_contra! hNeg
  rw [Set.inter_self] at hNeg
  obtain ⟨A, _, _, AonL, _⟩ := ref axiom I.2 L
  rw [hNeg] at AonL
  contradiction



end Intersection

end Geometry.Theory
