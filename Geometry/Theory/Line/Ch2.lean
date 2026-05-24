
/- General Theory about lines and line-parts using facts from Ch1 and Ch2 of the text -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Collinear.Ch1
import Geometry.Tactics
import Geometry.Ch2.Prop
import Atlas

namespace Geometry.Theory

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Atlas

set_option maxRecDepth 5000

namespace Line


atlas commentary := by
  ref lemma 2.0.1
  name "Line Trichotomy: Two lines either share no points share one point or are equal"
  preface "An intersection is either empty, a singleton, or the lines are equal."
  aliases [
    Geometry.Theory.Line.trichotomy
  ]

atlas lemma 2.0.1 "Two lines either share no points share one point or are equal"
  : ∀ L M : Line, (L ∩ M = ∅) ∨ (∃! X, L ∩ M = {X}) ∨ L = M := by
  intro L M
  by_cases suppose : (L ≠ M) ∧ (L ∦ M)
  · right; left
    exact proposition 2.1 suppose.left suppose.right
  · simp only [not_and_or, not_not] at suppose
    rcases suppose with LeqM | other
    · right; right; exact LeqM
    · left; push Not at *
      obtain ⟨_, LparM⟩ := other
      apply Line.eq_of_subset
      · intro e eInInt
        specialize LparM e
        rw [Line.inter_toSet, Set.mem_inter_iff] at eInInt
        obvious
      · obvious

atlas commentary := by
  ref lemma 2.0.2
  name "Two distinct points on two lines force the lines to coincide"
  preface "If two distinct points are found on two lines, those lines are equal."

atlas lemma 2.0.2 "Two distinct points on two lines force the lines to coincide"
  {L M : Line} {A B : Point} : A ≠ B -> ((A on L) ∧ (A on M) ∧ (B on L) ∧ (B on M) -> L = M) := by
  intro AneB ⟨AonL, AonM, BonL, BonM⟩
  have Aexists : A ∈ L ∩ M := by obvious
  have Bexists : B ∈ L ∩ M := by obvious
  comment "This is a _sweet_ use of trichotomy. This proof was much longer prior to this."
  rcases ref lemma 2.0.1 L M with LparM | LintMatX | LeqM
  · -- the intersection is nonempty by assumption
    exfalso
    rw [LparM] at Aexists
    contradiction
  · obtain ⟨X, Xinter, Xuniq⟩ := LintMatX
    exfalso
    -- A and B are both in the intersection by hypothesis
    rw [Xinter] at Aexists Bexists
    have AeqX : A = X := by obvious
    have BeqX : B = X := by obvious
    rw [AeqX, BeqX] at AneB
    contradiction
  · exact LeqM

attribute [simp] «Two distinct points on two lines force the lines to coincide»

atlas lemma 2.0.3 "Line Commutativity"
  {AneB : A ≠ B} : (line A B : Line) = line B A := by
  suffices subset : ∀ A B : Point, A ≠ B -> (line A B : Line) ⊆ line B A by
    exact Line.eq_of_subset
      (subset A B AneB)
      (subset B A AneB.symm)
  intro A B AneB P PinAB
  rcases PinAB with PeqA | PeqB | APB | ABP | PBA
  · rw [PeqA]; obvious
  · rw [PeqB]; obvious
  all_goals obvious


atlas commentary := by
  ref lemma 2.0.5
  name "Segment A B is a subset of line A B"
  preface "A segment is a subset of the line A B"

atlas lemma 2.0.5 "Segment A B is a subset of line A B"
  : (segment A B : Line) ⊆ (line A B : Line) := by
  have h₁ : (segment A B : Line) ⊆ (ray A B : Line) := obvious
  have h₂ : (ray A B : Line) ⊆ (line A B : Line) := ref lemma 1.0.18
  intro P PonSeg
  rcases PonSeg with APB | AorBeqP
  repeat obvious

atlas commentary := by
  ref lemma 2.0.6
  name "Line Points are Collinear"
  preface "All points on a line are collinear"

atlas lemma 2.0.6 "Line Points are Collinear"
  {AneB : A ≠ B} : P on line A B -> collinear A B P := by
  -- Direct Proof
  intro PonAB
  simp only [LineThrough.mem_def] at PonAB
  rcases PonAB with PeqA | PeqB | tween | tween | tween
  todo "These should be reducible to a single invocation, maybe a suffices?"
  · rw [<- PeqA];
    apply (ref lemma 1.0.17 B P).mpr
    by_cases suppose: B = P
    · rw [<- PeqA, suppose] at AneB; contradiction
    · exact ref lemma 1.0.14 suppose
  · rw [<- PeqB]
    apply (ref lemma 1.0.16 A P).mpr
    by_cases suppose: A = P
    · rw [<- PeqB, suppose] at AneB; contradiction
    · exact ref lemma 1.0.14 suppose
  repeat exact Collinear.order_irrelevance (ref axiom B.1 tween).collinear


/-
/- A extension excludes the points that define it -/
lemma extension_has_endpoints.left : A off extension A B := by sorry
/- A extension excludes the points that define it -/
lemma extension_excludes_endpoints.right : B off extension A B := by sorry
-/

atlas commentary := by
  ref lemma 2.0.7
  name "Every point on extension A B is collinear with A and B"
  preface "All points on a extension are collinear"

atlas lemma 2.0.7 "Every point on extension A B is collinear with A and B"
  {A B : Point} : P on extension A B -> collinear A B P := by
  intro PonExtAB
  exact (ref axiom B.1 PonExtAB.left).collinear


atlas commentary := by
  ref lemma 2.0.8
  name "Every point on segment A B is collinear with A and B"
  preface "All points on a segment are collinear"

atlas lemma 2.0.8 "Every point on segment A B is collinear with A and B"
  {AneB : A ≠ B} : P on segment A B -> collinear A B P := by
  intro PonSegAB
  apply ref lemma 2.0.5 at PonSegAB
  -- `@«Title»` form needed here: positional implicits, and `@ref ...`
  -- doesn't compose cleanly with Lean's built-in `@` term modifier.
  exact @«Line Points are Collinear» A B P AneB PonSegAB


atlas commentary := by
  ref lemma 2.0.9
  name "Ray Points are Collinear"
  preface "All points on a ray are collinear"

atlas lemma 2.0.9 "Ray Points are Collinear"
  {AneB : A ≠ B} : P on ray A B -> collinear A B P := by
  intro PonAB
  apply ref lemma 1.0.18 at PonAB
  -- `@«Title»` form needed here: positional implicits, and `@ref ...`
  -- doesn't compose cleanly with Lean's built-in `@` term modifier.
  exact @«Line Points are Collinear» A B P AneB PonAB



atlas lemma 2.0.10 "Segment A B and extension A B are disjoint"
  : (segment A B : Line) ∩ extension A B = ∅ := by
  apply Line.ext_set
  rw [Line.inter_toSet, Line.empty_toSet]
  apply Subset.antisymm
  · intro P ⟨PonSeg, PonExt⟩
    have ⟨ABP, AneP, BneP⟩ := PonExt
    rcases PonSeg with APB | AeqP | BeqP
    · exfalso; exact ref lemma 1.0.37 ⟨ABP, APB⟩
    · contradiction
    · contradiction
  · intro _ absurdity; exfalso; contradiction



atlas commentary := by
  ref lemma 2.0.12
  name "A ray A B is never equal to any line L"
  preface "A line is 'bigger' than a ray in the same way that a line is bigger than a segment"

atlas lemma 2.0.12 "A ray A B is never equal to any line L"
  { L : Line } {A B : Point}  (AneB : A ≠ B := by assumption) : ray A B ≠ L := by
  by_contra ABeqL
  idea "construct a point X - A - B, X is on L, by definition, but off AB, also by def. but under the hypothesis L = AB, -><-"
  have ⟨X, colXAB, distinctXAB, XAB⟩ := ref lemma 1.0.5 A B AneB
  separate at distinctXAB;
  have XonL : X on L := by
    idea "L = AB, and L = colXAB.line by the ref lemma 2.0.2"
    have LeqXAB : L = colXAB.line := by
      have ABeqXAB := ref lemma 2.0.2 AneB
        ⟨(by obvious : A on ray A B), colXAB.mem A,
         (by obvious : B on ray A B), colXAB.mem B⟩
      rw [<- ABeqXAB]; exact ABeqL.symm
    rw [LeqXAB]; exact colXAB.mem X
  rw [<- ABeqL] at XonL
  rcases XonL with XonSeg | XonExt
  · rcases XonSeg with AXB | AeqX | BeqX
    · exact ref lemma 1.0.36 ⟨XAB, AXB⟩
    · exact absurd AeqX XneA.symm
    · exact absurd BeqX XneB.symm
  · have ⟨ABX, _, _⟩ := XonExt
    exact ref lemma 1.0.38 ⟨ABX, XAB⟩


atlas commentary := by
  ref lemma 2.0.13
  name "Segment Commutativity"
  preface "It helps to be able to commute these around, when we get to congruence this will make part of it trivial"

atlas lemma 2.0.13 "Segment Commutativity"
  : (segment A B : Line) = segment B A := by
  suffices subset : ∀ A B : Point, (segment A B : Line) ⊆ segment B A by
    exact Line.eq_of_subset (subset A B) (subset B A)
  intro A B P hPinSegAB
  rcases hPinSegAB with APB | AeqP | BeqP
  all_goals obvious

attribute [obvious] «Segment Commutativity»


atlas commentary := by
  ref lemma 2.0.14
  name "A segment A B is never equal to any line L"
  preface "A line is 'bigger' than a segment, in the same way that a line is bigger than a ray (2.0.12)"

atlas lemma 2.0.14 "A segment A B is never equal to any line L"
  { L : Line } {A B : Point}  (AneB : A ≠ B := by assumption) : segment A B ≠ L := by
  intro ABeqL
  have AonL : A on L := by rw [<- ABeqL]; obvious
  have BonL : B on L := by rw [<- ABeqL]; obvious
  have ⟨X, colXAB, distinctXAB, XAB⟩ := ref lemma 1.0.5 A B AneB
  separate at distinctXAB
  have XonL : X on L := by
    have LeqXAB : L = colXAB.line :=
      ref lemma 2.0.2 AneB ⟨AonL, colXAB.mem A, BonL, colXAB.mem B⟩
    rw [LeqXAB]; exact colXAB.mem X
  rw [<- ABeqL] at XonL
  rcases XonL with AXB | AeqX | BeqX
  · exact ref lemma 1.0.36 ⟨XAB, AXB⟩
  · exact absurd AeqX XneA.symm
  · exact absurd BeqX XneB.symm

attribute [obvious] «A segment A B is never equal to any line L»
                    «A ray A B is never equal to any line L»


end Line

end Geometry.Theory
