
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory
import Geometry.Tactics

import Geometry.Ch2.Prop
import Geometry.Ch3.Prop.P1
import Geometry.Ch3.Prop.B4iii
import Geometry.Theory.Betweenness.Ch1
import Geometry.Theory.Betweenness.Ch2
import Geometry.Theory.Line.Ch1
import Geometry.Theory.Line.Ch2
import Geometry.Theory.Collinear.Ch1
import Geometry.Theory.Collinear.Ch2
import Atlas

namespace Geometry.Ch3.Ex

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex

/-- p146. Given A-B-C and A-C-D:
  (a) Prove that A,B,C, and D are four distinct points (the proof requires an axiom)
-/
atlas exercise 3.1 "Exercise 1(a): four points from chained betweenness are distinct"
  : A - B - C ∧ A - C - D -> distinct A B C D := by
  intro ⟨ABC, ACD⟩
  have distinctABC := Betweenness.abc_imp_distinct ABC
  have distinctACD := Betweenness.abc_imp_distinct ACD
  separate at distinctABC
  separate at distinctACD
  have BneD : B ≠ D := by
    by_contra! BeqD
    rw [<- BeqD] at ACD
    exact Betweenness.absurdity_abc_acb ⟨ABC, ACD⟩
  refine ⟨?_⟩
  simp [Finset.card_insert_of_notMem, Finset.card_singleton,
        Finset.mem_insert, Finset.mem_singleton,
        AneB, AneC, AneD, BneC, BneD, CneD]

alias Ex1.a := «Exercise 1(a): four points from chained betweenness are distinct»

/-- (b) Prove that A,B,C, and D are collinear -/
atlas exercise 3.1 "Exercise 1(b): four points from chained betweenness are collinear"
  : A - B - C ∧ A - C - D -> collinear A B C D := by
  intro ⟨ABC, ACD⟩
  -- we only end up needing A ≠ C, but easy to get the whole thing.
  have distinctABCD := Ex1.a ⟨ABC, ACD⟩
  have AneC : A ≠ C := by distinguish
  have colABC := Betweenness.abc_imp_collinear ABC
  have colACD := Betweenness.abc_imp_collinear ACD
  have LeqM : colABC.line = colACD.line := Line.equiv AneC ⟨colABC.mem A, colACD.mem A, colABC.mem C, colACD.mem C⟩
  use colABC.line
  intro P PisABCD
  simp only [Finset.mem_insert, Finset.mem_singleton] at PisABCD
  rcases PisABCD with eq | eq | eq | eq
  · rw [eq]; exact colABC.mem A
  · rw [eq]; exact colABC.mem B
  · rw [eq]; exact colABC.mem C
  · have DonM := colACD.mem D
    rw [eq]
    rw [<- LeqM] at DonM
    exact DonM

alias Ex1.b := «Exercise 1(b): four points from chained betweenness are collinear»

/-- (c) Prove the corrolary to B4
Ed. Note that (c) is covered by the B4iii lemma in it's own file. -/
alias Ex1.c := «Corollary to B-4: splits + guards transitivity»

/-- Ed. These (Ex1 a' and b') are not in the exercise but are quite convenient elsewhere -/
atlas lemma "Distinct four points from shifted chained betweenness (A-B-C and B-C-D)"
  : (A - B - C) ∧ (B - C - D) → distinct A B C D := by
  intro ⟨ABC, BCD⟩
  have distinctABC := Betweenness.abc_imp_distinct ABC
  have distinctBCD := Betweenness.abc_imp_distinct BCD
  separate at distinctABC
  separate at distinctBCD
  have AneD : A ≠ D := by
    by_contra! AeqD
    rw [AeqD] at ABC
    exact Betweenness.absurdity_abc_cab ⟨BCD, ABC⟩
  refine ⟨?_⟩
  simp [Finset.card_insert_of_notMem, Finset.card_singleton,
        Finset.mem_insert, Finset.mem_singleton,
        AneB, AneC, AneD, BneC, BneD, CneD]

alias Ex1.a' := «Distinct four points from shifted chained betweenness (A-B-C and B-C-D)»

atlas lemma "Collinear four points from shifted chained betweenness (A-B-C and B-C-D)"
  : (A - B - C) ∧ (B - C - D) → collinear A B C D := by
  intro ⟨ABC, BCD⟩
  -- we only end up needing A ≠ C, but easy to get the whole thing.
  have distinctABCD := Ex1.a' ⟨ABC, BCD⟩
  have BneC : B ≠ C := by distinguish
  have colABC := Betweenness.abc_imp_collinear ABC
  have colBCD := Betweenness.abc_imp_collinear BCD
  have LeqM : colABC.line = colBCD.line := Line.equiv BneC ⟨colABC.mem B, colBCD.mem B, colABC.mem C, colBCD.mem C⟩
  use colABC.line
  intro P PisABCD
  simp only [Finset.mem_insert, Finset.mem_singleton] at PisABCD
  rcases PisABCD with eq | eq | eq | eq
  · rw [eq]; exact colABC.mem A
  · rw [eq]; exact colABC.mem B
  · rw [eq]; exact colABC.mem C
  · have DonM := colBCD.mem D
    rw [eq]
    rw [<- LeqM] at DonM
    exact DonM

alias Ex1.b' := «Collinear four points from shifted chained betweenness (A-B-C and B-C-D)»

end Geometry.Ch3.Ex
