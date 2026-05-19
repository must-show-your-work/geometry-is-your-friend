
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

set_option maxRecDepth 5000

namespace Line


/-- An intersection is either empty, a singleton, or the lines are equal. -/
atlas lemma 2.0.1 "Two lines either share no points share one point or are equal"
  : ∀ L M : Set Point, (L ∩ M = ∅) ∨ (∃! X, L ∩ M = {X}) ∨ L = M := by
  intro L M
  by_cases suppose : (L ≠ M) ∧ (L ∦ M)
  · right; left
    exact proposition 2.1 suppose.left suppose.right
  · simp only [not_and_or, not_not] at suppose
    rcases suppose with LeqM | other
    · right; right; exact LeqM
    · left; push_neg at *
      obtain ⟨_, LparM⟩ := other
      apply Subset.antisymm
      · intro e eInInt
        specialize LparM e
        obtain ⟨eInL, eInM⟩ := by
          rw [Set.mem_inter_iff] at eInInt
          exact eInInt
        tauto
      · tauto


/-- If two distinct points are found on two lines, those lines are equal. -/
atlas lemma 2.0.2 "Two distinct points on two lines force the lines to coincide"
  {L M : Line} {A B : Point} : A ≠ B -> ((A on L) ∧ (A on M) ∧ (B on L) ∧ (B on M) -> L = M) := by
  intro AneB ⟨AonL, AonM, BonL, BonM⟩
  have Aexists : A ∈ L ∩ M := by tauto
  have Bexists : B ∈ L ∩ M := by tauto
  -- Ed. This is a _sweet_ use of trichotomy. This proof was much longer prior to this.
  rcases ref lemma 2.0.1 L M with LparM | LintMatX | LeqM
  · -- the intersection is nonempty by assumption
    exfalso
    rw [LparM] at Aexists
    contradiction
  · obtain ⟨X, Xinter, Xuniq⟩ := LintMatX
    exfalso
    -- A and B are both in the intersection by hypothesis
    rw [Xinter] at Aexists Bexists
    have AeqX : A = X := by tauto
    have BeqX : B = X := by tauto
    rw [AeqX, BeqX] at AneB
    contradiction
  · exact LeqM

attribute [simp] «Two distinct points on two lines force the lines to coincide»

atlas lemma 2.0.3 "Line Commutativity"
  {AneB : A ≠ B} : line A B = line B A := by
  suffices subset : ∀ A B : Point, A ≠ B -> line A B ⊆ line B A by
    exact Subset.antisymm
      (subset A B AneB)
      (subset B A AneB.symm)
  intro A B AneB P PinAB
  rcases PinAB with PeqA | PeqB | APB | ABP | PBA
  · rw [PeqA]; exact ref lemma 1.0.24
  · rw [PeqB]; exact ref lemma 1.0.23
  all_goals obvious


/-- pXX "By the definition of segment and ray, `the segment A B ⊆ the ray A B`" -/
-- FIXME: this is a quote but I didn't write the page #
-- FIXME: if it's obvious here, it's obvious at the callsite, so inline it
atlas lemma 2.0.4 "Segment A B is a subset of ray A B"
  : segment A B ⊆ ray A B := obvious


/-- A segment is a subset of the line A B -/
atlas lemma 2.0.5 "Segment A B is a subset of line A B"
  : segment A B ⊆ line A B := by
  have h₁ : segment A B ⊆ ray A B := ref lemma 2.0.4
  have h₂ : ray A B ⊆ line A B := ref lemma 1.0.18
  intro P PonSeg
  rcases PonSeg with APB | AorBeqP
  repeat tauto

/-- All points on a line are collinear -/
atlas lemma 2.0.6 "Line Points are Collinear"
  {AneB : A ≠ B} : P on line A B -> collinear A B P := by
  -- Direct Proof
  intro PonAB
  simp only [mem_setOf_eq] at PonAB
  rcases PonAB with PeqA | PeqB | tween | tween | tween
  -- TODO: These should be reducible to a single invocation, maybe a suffices?
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
  repeat exact Collinear.order_irrelevance (ref lemma 1.0.40 tween)


/-
/- A extension excludes the points that define it -/
lemma extension_has_endpoints.left : A off extension A B := by sorry
/- A extension excludes the points that define it -/
lemma extension_excludes_endpoints.right : B off extension A B := by sorry
-/

/-- All points on a extension are collinear -/
atlas lemma 2.0.7 "Every point on extension A B is collinear with A and B"
  {A B : Point} : P on extension A B -> collinear A B P := by
  intro PonExtAB
  exact ref lemma 1.0.40 PonExtAB.left


/-- All points on a segment are collinear -/
atlas lemma 2.0.8 "Every point on segment A B is collinear with A and B"
  {AneB : A ≠ B} : P on segment A B -> collinear A B P := by
  intro PonSegAB
  apply ref lemma 2.0.5 at PonSegAB
  -- `@«Title»` form needed here: positional implicits, and `@ref ...`
  -- doesn't compose cleanly with Lean's built-in `@` term modifier.
  exact @«Line Points are Collinear» A B P AneB PonSegAB


/-- All points on a ray are collinear -/
atlas lemma 2.0.9 "Ray Points are Collinear"
  {AneB : A ≠ B} : P on ray A B -> collinear A B P := by
  intro PonAB
  apply ref lemma 1.0.18 at PonAB
  -- `@«Title»` form needed here: positional implicits, and `@ref ...`
  -- doesn't compose cleanly with Lean's built-in `@` term modifier.
  exact @«Line Points are Collinear» A B P AneB PonAB



atlas lemma 2.0.10 "Segment A B and extension A B are disjoint"
  : segment A B ∩ extension A B = ∅ := by
  apply Subset.antisymm
  · intro P ⟨PonSeg, PonExt⟩
    have ⟨ABP, AneP, BneP⟩ := PonExt
    rcases PonSeg with APB | AeqP | BeqP
    · exfalso; exact ref lemma 1.0.37 ⟨ABP, APB⟩
    · contradiction
    · contradiction
  · intro _ absurdity; exfalso; contradiction


/-- A line is the set of all points on it -/
atlas lemma 2.0.11 "A line equals the set of all points lying on it"
  : ∀ L : Line, L = {P : Point | P on L} := by
  intro L
  apply Subset.antisymm
  repeat tauto


/-- A line is 'bigger' than a ray in the same way that a line is bigger than a segment -/
atlas lemma 2.0.12 "A ray A B is never equal to any line L"
  : ∀ L : Line, ∀ A B : Point, A ≠ B -> ray A B ≠ L := by
  intro L A B AneB
  by_contra ABeqL
  -- idea: construct a point X - A - B, X is on L, by definition, but off AB, also by def. but under the hypothesis L = AB, -><-
  have ⟨X, colXAB, distinctXAB, XAB⟩ := ref lemma 1.0.5 A B AneB
  separate at distinctXAB;
  have XonL : X on L := by
    -- idea, L = AB, and L = colXAB.line by the ref lemma 2.0.2
    have LeqXAB : L = colXAB.line := by
      have ABeqXAB := ref lemma 2.0.2 AneB ⟨ref lemma 1.0.21, colXAB.mem A, ref lemma 1.0.22, colXAB.mem B⟩
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


/- It helps to be able to commute these around, when we get to congruence this will make part of it trivial -/
atlas lemma 2.0.13 "Segment Commutativity"
  : segment A B = segment B A := by
  suffices subset : ∀ A B : Point, segment A B ⊆ segment B A by
    exact Subset.antisymm (subset A B) (subset B A)
  intro A B P hPinSegAB
  rcases hPinSegAB with APB | AeqP | BeqP
  all_goals obvious

attribute [obvious_simp] «Segment Commutativity»


/-- The endpoint B is in common here. -/
atlas lemma 2.0.14 "Segment A B is a subset of ray B A (the swapped-endpoint ray)"
  : segment A B ⊆ ray B A := by
  intro P hPinSegAB
  obvious


/- lemma ABP_imp_P_on_line_AB (PneAB : P ≠ A ∧ P ≠ B) : -/
/-   A - B - P -> P on the line A B := by -/
/-     intro ABP; -/
/-     have distinctABP := ref lemma 1.0.39 ABP -/
/-     have AneB := by distinguish distinctABP A B -/
/-     have colABP := ref lemma 1.0.40 ABP -/
/-     unfold LineThrough -/

/- lemma APB_imp_P_on_line_AB (PneAB : P ≠ A ∧ P ≠ B) : -/
/-   A - P - B -> P on the line A B := by -/
/-     intro hABP; -/
/-     have hPonSegAB : P on segment A B := APB_imp_P_on_segment_AB PneAB hABP -/
/-     unfold LineThrough; simp only [mem_setOf_eq] -/
/-     exact ref lemma 2.0.8 hPonSegAB -/

end Line

end Geometry.Theory
