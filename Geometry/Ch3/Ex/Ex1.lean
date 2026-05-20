
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
open Atlas

atlas commentary := by
  ref exercise 3.1.a
  page 146
  name "Exercise 1(a): four points from chained betweenness are distinct"
  preface "Given A-B-C and A-C-D:
  (a) Prove that A,B,C, and D are four distinct points (the proof requires an axiom)"

atlas exercise 3.1.a "Exercise 1(a): four points from chained betweenness are distinct"
  : A - B - C ∧ A - C - D -> distinct A B C D := by
  intro ⟨ABC, ACD⟩
  have distinctABC := ref lemma 1.0.39 ABC
  have distinctACD := ref lemma 1.0.39 ACD
  separate at distinctABC
  separate at distinctACD
  have BneD : B ≠ D := by
    by_contra! BeqD
    rw [<- BeqD] at ACD
    exact ref lemma 1.0.37 ⟨ABC, ACD⟩
  refine ⟨?_⟩
  simp [Finset.card_insert_of_notMem, Finset.card_singleton,
        Finset.mem_insert, Finset.mem_singleton,
        AneB, AneC, AneD, BneC, BneD, CneD]


atlas commentary := by
  ref exercise 3.1.b
  page 146
  name "Exercise 1(b): four points from chained betweenness are collinear"
  preface "(b) Prove that A,B,C, and D are collinear"

atlas exercise 3.1.b "Exercise 1(b): four points from chained betweenness are collinear"
  : A - B - C ∧ A - C - D -> collinear A B C D := by
  intro ⟨ABC, ACD⟩
  -- We only end up needing A ≠ C, but easy to get the whole thing.
  have distinctABCD : distinct A B C D := via exercise 3.1.a ⟨ABC, ACD⟩
  have AneC : A ≠ C := by distinguish
  have colABC := ref lemma 1.0.40 ABC
  have colACD := ref lemma 1.0.40 ACD
  have LeqM : colABC.line = colACD.line := ref lemma 2.0.2 AneC ⟨colABC.mem A, colACD.mem A, colABC.mem C, colACD.mem C⟩
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
  ref lemma 3.0.3
  name "Distinct four points from shifted chained betweenness (A-B-C and B-C-D)"
  notes "These (Ex1 a' and b') are not in the exercise but are quite convenient elsewhere"

atlas lemma 3.0.3 "Distinct four points from shifted chained betweenness (A-B-C and B-C-D)"
  : (A - B - C) ∧ (B - C - D) → distinct A B C D := by
  intro ⟨ABC, BCD⟩
  have distinctABC := ref lemma 1.0.39 ABC
  have distinctBCD := ref lemma 1.0.39 BCD
  separate at distinctABC
  separate at distinctBCD
  have AneD : A ≠ D := by
    by_contra! AeqD
    rw [AeqD] at ABC
    exact ref lemma 1.0.38 ⟨BCD, ABC⟩
  refine ⟨?_⟩
  simp [Finset.card_insert_of_notMem, Finset.card_singleton,
        Finset.mem_insert, Finset.mem_singleton,
        AneB, AneC, AneD, BneC, BneD, CneD]


atlas lemma 3.0.4 "Collinear four points from shifted chained betweenness (A-B-C and B-C-D)"
  : (A - B - C) ∧ (B - C - D) → collinear A B C D := by
  intro ⟨ABC, BCD⟩
  -- we only end up needing A ≠ C, but easy to get the whole thing.
  have distinctABCD := ref lemma 3.0.3 ⟨ABC, BCD⟩
  have BneC : B ≠ C := by distinguish
  have colABC := ref lemma 1.0.40 ABC
  have colBCD := ref lemma 1.0.40 BCD
  have LeqM : colABC.line = colBCD.line := ref lemma 2.0.2 BneC ⟨colABC.mem B, colBCD.mem B, colABC.mem C, colBCD.mem C⟩
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
