
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
  {L M : Line} {A : Point} :
    L intersects M -> A on L ∧ A on M -> L intersects M at A ∨ L = M := by
  intro _LintM ⟨AonL, AonM⟩
  have AinInt : A ∈ L ∩ M := Line.mem_inter.mpr ⟨AonL, AonM⟩
  rcases ref lemma 2.0.1 L M with empty | unique | equal
  · exfalso; rw [empty] at AinInt; exact (Line.not_mem_empty AinInt)
  · left
    obtain ⟨X, hX, _⟩ := unique
    rw [hX] at AinInt
    have AeqX : A = X := Line.mem_singleton.mp AinInt
    change L ∩ M = ({A} : Line)
    rw [hX, AeqX]
  · right; exact equal


atlas commentary := by
  ref lemma 3.0.2
  name "A line intersects itself (bare intersection of L with L)"
  preface "A line trivially intersects itself everywhere."

atlas lemma 3.0.2 "A line intersects itself (bare intersection of L with L)"
  : L intersects L := by
  obtain ⟨A, _, _, AonL, _⟩ := ref axiom I.2 L
  exact ⟨A, AonL, AonL⟩

atlas lemma 3.7.2 "If L intersects M, then there is a point at which it intersects M, WLOG X"
  {L M : Line} : L ≠ M -> L intersects M -> ∃ X : Point, L intersects M at X := by
  intro LneM LintM
  rcases ref lemma 2.0.1 L M with empty | unique | equal
  · exfalso
    obtain ⟨X, hX⟩ := LintM
    have hMem : X ∈ L ∩ M := Line.mem_inter.mpr hX
    rw [empty] at hMem; exact Line.not_mem_empty hMem
  · obtain ⟨X, hX, _⟩ := unique
    exact ⟨X, hX⟩
  · exact absurd equal LneM

atlas lemma 3.7.3 "If L splits A and B, then L intersects segment A B"
  {L : Line} {A B : Point} : (L splits A and B) -> (L intersects segment A B) := by
  intro LsplitsAB
  by_cases hA : A on L
  · exact ⟨A, hA, by obvious⟩
  by_cases hB : B on L
  · exact ⟨B, hB, by obvious⟩
  unfold Splits Guards at LsplitsAB
  push Not at LsplitsAB
  obtain ⟨_, P, PonSeg, PonL⟩ := LsplitsAB hA hB
  exact ⟨P, PonL, PonSeg⟩

atlas corollary 3.7.3 "If L guards A and B, then L does not intersect segment A B"
  {L : Line} {A B : Point} : (L guards A and B) -> ¬(L intersects segment A B) := by
  intro ⟨AoffL, BoffL, hCase⟩ ⟨X, XonL, XonSeg⟩
  rcases hCase with AeqB | hAvoids
  · subst AeqB
    rcases XonSeg with AXA | AeqX | AeqX
    · have : distinct A X A := (ref axiom B.1 AXA).distinct
      separate at this; contradiction
    · rw [<- AeqX] at XonL; exact AoffL XonL
    · rw [<- AeqX] at XonL; exact AoffL XonL
  · exact (hAvoids X XonSeg) XonL


end Intersection

end Geometry.Theory
