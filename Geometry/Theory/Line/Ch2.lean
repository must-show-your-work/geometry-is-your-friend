
/- General Theory about lines and line-parts using facts from Ch1 and Ch2 of the text -/

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Collinear.Ch1
import Geometry.Tactics
import Geometry.Ch2.Prop

namespace Geometry.Theory

open Set
open Geometry.Theory
open Geometry.Ch2.Prop

set_option maxRecDepth 5000

namespace Line


/-- An intersection is either empty, a singleton, or the lines are equal. -/
lemma line_trichotomy : ∀ L M : Set Point, (L ∩ M = ∅) ∨ (∃! X, L ∩ M = {X}) ∨ L = M := by
  intro L M
  by_cases suppose : (L ≠ M) ∧ (L ∦ M)
  · right; left
    exact Ch2.Prop.P1 suppose.left suppose.right
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
@[simp] lemma equiv {L M : Line} {A B : Point} : A ≠ B -> ((A on L) ∧ (A on M) ∧ (B on L) ∧ (B on M) -> L = M) := by
  intro AneB ⟨AonL, AonM, BonL, BonM⟩
  have Aexists : A ∈ L ∩ M := by tauto
  have Bexists : B ∈ L ∩ M := by tauto
  -- Ed. This is a _sweet_ use of trichotomy. This proof was much longer prior to this.
  rcases line_trichotomy L M with LparM | LintMatX | LeqM
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

lemma commutes {AneB : A ≠ B} : line A B = line B A := by
  suffices subset : ∀ A B : Point, A ≠ B -> line A B ⊆ line B A by
    exact Subset.antisymm
      (subset A B AneB)
      (subset B A AneB.symm)
  intro A B AneB P PinAB
  rcases PinAB with PeqA | PeqB | APB | ABP | PBA
  · rw [PeqA]; exact line_has_definition_points.right
  · rw [PeqB]; exact line_has_definition_points.left
  · rw [B1b] at APB; tauto
  · rw [B1b] at ABP; tauto
  · rw [B1b] at PBA; tauto

/-- pXX "By the definition of segment and ray, `the segment A B ⊆ the ray A B`" -/
-- FIXME: this is a quote but I didn't write the page #
lemma seg_sub_ray : segment A B ⊆ ray A B := by simp_all only [subset_union_left]

/-- A segment is a subset of the line A B -/
lemma seg_sub_line : segment A B ⊆ line A B := by
  have h₁ : segment A B ⊆ ray A B := seg_sub_ray
  have h₂ : ray A B ⊆ line A B := ray_sub_line
  simp only [setOf_subset_setOf, B1b]
  intro P PonSeg
  tauto

/-- All points on a line are collinear -/
lemma all_points_on_a_line_are_collinear {AneB : A ≠ B} : P on line A B -> collinear A B P := by
  -- Direct Proof
  intro PonAB
  simp only [mem_setOf_eq] at PonAB
  rcases PonAB with PeqA | PeqB | tween | tween | tween
  -- TODO: These should be reducible to a single invocation, maybe a suffices?
  · rw [<- PeqA];
    apply (Collinear.redundancy_irrelevance_BAB B P).mpr
    by_cases suppose: B = P
    · rw [<- PeqA, suppose] at AneB; contradiction
    · exact Collinear.any_two_points_are_collinear suppose
  · rw [<- PeqB]
    apply (Collinear.redundancy_irrelevance_ABB A P).mpr
    by_cases suppose: A = P
    · rw [<- PeqB, suppose] at AneB; contradiction
    · exact Collinear.any_two_points_are_collinear suppose
  repeat exact Collinear.order_irrelevance (Betweenness.abc_imp_collinear tween)

/-
/- A extension excludes the points that define it -/
lemma extension_has_endpoints.left : A off extension A B := by sorry
/- A extension excludes the points that define it -/
lemma extension_excludes_endpoints.right : B off extension A B := by sorry
-/

/-- All points on a extension are collinear -/
lemma all_points_on_an_extension_are_collinear {A B : Point} : P on extension A B -> collinear A B P := by
  intro PonExtAB
  exact Betweenness.abc_imp_collinear PonExtAB.left

/-- All points on a segment are collinear -/
lemma all_points_on_a_segment_are_collinear {AneB : A ≠ B} : P on segment A B -> collinear A B P := by
  intro PonSegAB
  apply seg_sub_line at PonSegAB
  exact @all_points_on_a_line_are_collinear A B P AneB PonSegAB

/-- All points on a ray are collinear -/
lemma all_points_on_a_ray_are_collinear {AneB : A ≠ B} : P on ray A B -> collinear A B P := by
  intro PonAB
  apply ray_sub_line at PonAB
  exact @all_points_on_a_line_are_collinear A B P AneB PonAB


lemma segment_int_extension_is_empty : segment A B ∩ extension A B = ∅ := by
  apply Subset.antisymm
  · intro P ⟨PonSeg, PonExt⟩
    have ⟨ABP, AneP, BneP⟩ := PonExt
    rcases PonSeg with APB | AeqP | BeqP
    · exfalso; exact Betweenness.absurdity_abc_acb ⟨ABP, APB⟩
    · contradiction
    · contradiction
  · intro _ absurdity; exfalso; contradiction

/-- A line is the set of all points on it -/
lemma line_by_definition : ∀ L : Line, L = {P : Point | P on L} := by
  intro L
  apply Subset.antisymm
  repeat tauto

/-- A line is 'bigger' than a ray in the same way that a line is bigger than a segment -/
lemma line_is_bigger_than_ray : ∀ L : Line, ∀ A B : Point, A ≠ B -> ray A B ≠ L := by
  intro L A B AneB
  by_contra ABeqL
  -- idea: construct a point X - A - B, X is on L, by definition, but off AB, also by def. but under the hypothesis L = AB, -><-
  have ⟨X, colXAB, distinctXAB, XAB⟩ := B2.left A B AneB
  separate at distinctXAB;
  have XonL : X on L := by
    -- idea, L = AB, and L = colXAB.line by the Line.equiv
    have LeqXAB : L = colXAB.line := by
      have ABeqXAB := Line.equiv AneB ⟨Line.ray_has_endpoints.left, colXAB.mem A, Line.ray_has_endpoints.right, colXAB.mem B⟩
      rw [<- ABeqXAB]; exact ABeqL.symm
    rw [LeqXAB]; exact colXAB.mem X
  rw [<- ABeqL] at XonL
  rcases XonL with XonSeg | XonExt
  · rcases XonSeg with AXB | AeqX | BeqX
    · exact Betweenness.absurdity_abc_bac ⟨XAB, AXB⟩
    · exact absurd AeqX XneA.symm
    · exact absurd BeqX XneB.symm
  · have ⟨ABX, _, _⟩ := XonExt
    exact Betweenness.absurdity_abc_cab ⟨ABX, XAB⟩

/- It helps to be able to commute these around, when we get to congruence this will make part of it trivial -/
lemma segment_AB_eq_segment_BA : segment A B = segment B A := by
  unfold Segment
  ext P
  rw [@mem_setOf]; simp_all only [mem_setOf_eq]
  constructor
  intro h; rcases h with h0 | h1 | h2; rw [B1b];
  repeat tauto
  intro h; rcases h with h0 | h1 | h2; rw [B1b]
  repeat tauto

/-- The endpoint B is in common here. -/
lemma segment_AB_sub_ray_BA : segment A B ⊆ ray B A := by
  intro P hPinSegAB
  simp_all only [mem_setOf_eq, mem_union, segment_AB_eq_segment_BA, true_or]

lemma APB_imp_P_on_segment_AB (PneAB : P ≠ A ∧ P ≠ B) :
  A - P - B -> P on the segment A B := by intro _; obvious

lemma APB_imp_P_on_ray_AB (PneAB : P ≠ A ∧ P ≠ B) :
  A - P - B -> P on the ray A B := by intro _; obvious

lemma ABP_imp_P_on_ext_AB (PneAB : P ≠ A ∧ P ≠ B) :
  A - B - P -> P on the extension A B := by intro _; obvious

/- lemma ABP_imp_P_on_line_AB (PneAB : P ≠ A ∧ P ≠ B) : -/
/-   A - B - P -> P on the line A B := by -/
/-     intro ABP; -/
/-     have distinctABP := Betweenness.abc_imp_distinct ABP -/
/-     have AneB := by distinguish distinctABP A B -/
/-     have colABP := Betweenness.abc_imp_collinear ABP -/
/-     unfold LineThrough -/

/- lemma APB_imp_P_on_line_AB (PneAB : P ≠ A ∧ P ≠ B) : -/
/-   A - P - B -> P on the line A B := by -/
/-     intro hABP; -/
/-     have hPonSegAB : P on segment A B := APB_imp_P_on_segment_AB PneAB hABP -/
/-     unfold LineThrough; simp only [mem_setOf_eq] -/
/-     exact Line.all_points_on_a_segment_are_collinear hPonSegAB -/

end Line

end Geometry.Theory
