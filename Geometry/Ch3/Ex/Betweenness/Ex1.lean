import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Distinct
import Geometry.Theory.Interpendices.B

import Geometry.Tactics

import Geometry.Construction.AtlasField
import Atlas

namespace Geometry.Ch3.Ex

open Set
open Geometry.Theory
open Geometry.Ch3.Ex
open Atlas

atlas commentary := by
  via exercise 3.Betweenness.1.a
  page 146
  name "Exercise 1(a): four points from chained betweenness are distinct"
  preface "Given A-B-C and A-C-D:
  (a) Prove that A,B,C, and D are four distinct points (the proof requires an axiom)"

  figure := by
    construction {
      exists A B C D : Point
      assert distinct A B C D
      assert between A B C
      assert between A C D
      construct segAD := segment A D
    }
    title "Exercise 3.Betweenness.1(a)"
    index 1
    caption "Chained betweenness A-B-C and A-C-D arranges four distinct collinear points."

atlas exercise 3.Betweenness.1.a "Exercise 1(a): four points from chained betweenness are distinct"
  : A - B - C ∧ A - C - D -> distinct A B C D := by
  intro ⟨ABC, ACD⟩
  have distinctABC := (via axiom B.1 ABC).distinct
  have distinctACD := (via axiom B.1 ACD).distinct
  separate at distinctABC
  separate at distinctACD
  have BneD : B ≠ D := by
    by_contra! BeqD
    rw [<- BeqD] at ACD
    exact via lemma 1.0.19 ⟨ABC, ACD⟩
  refine ⟨?_⟩
  simp [Finset.card_insert_of_notMem, Finset.card_singleton,
        Finset.mem_insert, Finset.mem_singleton,
        AneB, AneC, AneD, BneC, BneD, CneD]


atlas commentary := by
  via exercise 3.Betweenness.1.b
  page 146
  name "Exercise 1(b): four points from chained betweenness are collinear"
  preface "(b) Prove that A,B,C, and D are collinear"

  figure := by
    construction {
      exists A B C D : Point
      assert distinct A B C D
      assert between A B C
      assert between A C D
      construct segAD := segment A D
    }
    title "Exercise 3.Betweenness.1(b)"
    index 1
    caption "From A-B-C and A-C-D, the four points share a single line."

atlas exercise 3.Betweenness.1.b "Exercise 1(b): four points from chained betweenness are collinear"
  : A - B - C ∧ A - C - D -> collinear A B C D := by
  intro ⟨ABC, ACD⟩
  -- We only end up needing A ≠ C, but easy to get the whole thing.
  have distinctABCD : distinct A B C D := via exercise 3.Betweenness.1.a ⟨ABC, ACD⟩
  have AneC : A ≠ C := by distinguish
  have colABC := (via axiom B.1 ABC).collinear
  have colACD := (via axiom B.1 ACD).collinear
  have LeqM : colABC.line = colACD.line := via lemma 2.0.2 AneC ⟨colABC.mem A, colACD.mem A, colABC.mem C, colACD.mem C⟩
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


/- (c) Prove the corollary to B-4 — covered by the `B.4.iii` corollary in its own file. -/

atlas commentary := by
  via lemma 3.0.3
  name "Distinct four points from shifted chained betweenness (A-B-C and B-C-D)"
  notes "These (Ex1 a' and b') are not in the exercise but are quite convenient elsewhere"

  figure := by
    construction {
      exists A B C D : Point
      assert distinct A B C D
      assert between A B C
      assert between B C D
      construct segAD := segment A D
    }
    title "Lemma 3.0.3"
    index 1
    caption "Shifted chain A-B-C and B-C-D — four collinear distinct points in order A, B, C, D."

atlas lemma 3.0.3 "Distinct four points from shifted chained betweenness (A-B-C and B-C-D)"
  : (A - B - C) ∧ (B - C - D) → distinct A B C D := by
  intro ⟨ABC, BCD⟩
  have distinctABC := (via axiom B.1 ABC).distinct
  have distinctBCD := (via axiom B.1 BCD).distinct
  separate at distinctABC
  separate at distinctBCD
  have AneD : A ≠ D := by
    by_contra! AeqD
    rw [AeqD] at ABC
    exact via lemma 1.0.20 ⟨BCD, ABC⟩
  refine ⟨?_⟩
  simp [Finset.card_insert_of_notMem, Finset.card_singleton,
        Finset.mem_insert, Finset.mem_singleton,
        AneB, AneC, AneD, BneC, BneD, CneD]


atlas lemma 3.0.4 "Collinear four points from shifted chained betweenness (A-B-C and B-C-D)"
  : (A - B - C) ∧ (B - C - D) → collinear A B C D := by
  intro ⟨ABC, BCD⟩
  -- we only end up needing A ≠ C, but easy to get the whole thing.
  have distinctABCD := via lemma 3.0.3 ⟨ABC, BCD⟩
  have BneC : B ≠ C := by distinguish
  have colABC := (via axiom B.1 ABC).collinear
  have colBCD := (via axiom B.1 BCD).collinear
  have LeqM : colABC.line = colBCD.line := via lemma 2.0.2 BneC ⟨colABC.mem B, colBCD.mem B, colABC.mem C, colBCD.mem C⟩
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


end Geometry.Ch3.Ex
