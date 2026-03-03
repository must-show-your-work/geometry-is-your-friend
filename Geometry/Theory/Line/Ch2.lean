
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
lemma equiv {L M : Line} {A B : Point} : A ≠ B -> ((A on L) ∧ (A on M) ∧ (B on L) ∧ (B on M) -> L = M) := by
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
  -- FIXME: This is an aesop special, it's probably much simpler than this.
  simp_all only [ne_eq]
  ext x : 1
  simp_all only [mem_setOf_eq, B1b]
  apply Iff.intro
  · intro a
    cases a with
    | inl h =>
      subst h
      simp_all only [B1b, or_self_left, true_or, or_true]
    | inr h_1 =>
      cases h_1 with
      | inl h =>
        subst h
        simp_all only [true_or]
      | inr h_2 =>
        cases h_2 with
        | inl h => simp_all only [true_or, or_true]
        | inr h_1 =>
          cases h_1 with
          | inl h => simp_all only [or_true]
          | inr h_2 => simp_all only [true_or, or_true]
  · intro a
    cases a with
    | inl h =>
      subst h
      simp_all only [or_self_left, true_or, or_true]
    | inr h_1 =>
      cases h_1 with
      | inl h =>
        subst h
        simp_all only [B1b, false_or, true_or]
      | inr h_2 =>
        cases h_2 with
        | inl h => simp_all only [true_or, or_true]
        | inr h_1 =>
          cases h_1 with
          | inl h => simp_all only [or_true]
          | inr h_2 => simp_all only [true_or, or_true]



/-- A segment contains the points that define it -/
lemma seg_has_endpoints.left : A on segment A B := by tauto
/-- A segment contains the points that define it -/
lemma seg_has_endpoints.right : B on segment A B := by tauto

/-- A ray contains the points that define it -/
lemma ray_has_endpoints.left : A on ray A B := by
  simp only [mem_union, mem_setOf_eq, true_or, or_true, ne_eq, not_true_eq_false, false_and, and_false, or_false]
/-- A ray contains the points that define it -/
lemma ray_has_endpoints.right : B on ray A B := by
  simp only [mem_union, mem_setOf_eq, or_true, ne_eq, not_true_eq_false, and_false, or_false]

/-- A ray A B is a subset of the line A B -/
lemma ray_sub_line : ray A B ⊆ line A B := by
  intro P PonRay
  simp only [B1b, mem_setOf_eq]
  rcases PonRay with (APB | AeqP | BeqP) | h
  · right; right; left; assumption
  · left; exact AeqP.symm
  · right; left; exact BeqP.symm
  · have ⟨ABP,_⟩ := h
    right; right; right; left; assumption

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

/-- A line contains the points that define it -/
lemma line_has_definition_points.left : A on line A B := ray_sub_line ray_has_endpoints.left

/-- A line contains the points that define it -/
lemma line_has_definition_points.right : B on line A B := ray_sub_line ray_has_endpoints.right

/-- A line contains the points that define it -/
lemma line_has_definition_points : A on line A B ∧ B on line A B := ⟨line_has_definition_points.left, line_has_definition_points.right⟩

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

/-- Every `line A B` is a whole line `L` -/
lemma linethrough_lift_line : ∀ L : Line, ∃ A B : Point, A ≠ B ∧ L = line A B := by
  sorry

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
  -- there are three cases:
  -- 1. L ∥ ray A B, in which case they are not equal because A and B aren't on L.
  -- 2. L intersects ray A B, in which case at least one of A or B aren't on L
  -- 3. L is line A B, which is not equal to ray A B because it contains points on extension B A
  have AonRayAB : A on ray A B := Line.ray_has_endpoints.left
  have BonRayAB : B on ray A B := Line.ray_has_endpoints.right
  have ⟨C, D, _, lineCD⟩ := (linethrough_lift_line L)
  rcases line_trichotomy L (ray A B) with LparRay | LintRay | LextendsRay
  · by_contra! hNeg
    rw [<- hNeg] at LparRay
    simp only [inter_self] at LparRay
    rw [LparRay] at AonRayAB
    contradiction
  · obtain ⟨X, LintABatX, Xuniq⟩ := LintRay
    have AorBoffL : (A off L) ∨ (B off L) := by
      by_contra! ⟨AonL, BonL⟩
      have AinInt : A ∈ L ∩ ray A B := by tauto
      have BinInt : B ∈ L ∩ ray A B := by tauto
      rw [LintABatX] at *
      have AeqB : A = B := by
        have AeqX : A = X := by tauto
        have BeqX : B = X := by tauto
        rw [<- BeqX] at AeqX
        exact AeqX
      contradiction
    by_contra! hNeg
    rw [<- hNeg] at AorBoffL
    tauto
  · exfalso
    have LisPsonL : L = { P | P on L } := line_by_definition L
    rw [<- LextendsRay] at AonRayAB BonRayAB
    have LeqLineAB : L = line A B := Line.equiv AneB
      ⟨AonRayAB, line_has_definition_points.left, BonRayAB, line_has_definition_points.right⟩
    have lABeqlCD : line A B = line C D := by
      rwa [LeqLineAB] at lineCD
    rw [LeqLineAB] at LextendsRay
    have ⟨X, colXAB, distinctXAB, XAB⟩ := B2.left A B AneB
    have ⟨XneA, XneB⟩ : X ≠ A ∧ X ≠ B := by sorry -- distinguish -- fails here due to simp recursion issues? or maybe index OOB
    have L'eqL : colXAB.line = line A B := Line.equiv AneB
      ⟨colXAB.mem A, line_has_definition_points.left, colXAB.mem B, line_has_definition_points.right⟩
    have XonL : X on L := by rw [LeqLineAB, <- L'eqL]; exact colXAB.mem X
    -- by construction, X is off the ray
    have XoffRayAB : X off ray A B := by
      unfold Ray;
      -- TODO: This could be done under the rcases below, probably cleaner
      have XoffSegmentAB : X off segment A B := by
        unfold Segment
        simp only [mem_setOf_eq]
        by_contra! hNeg
        rcases hNeg with AXB | AeqX | BeqX
        · exact Betweenness.absurdity_abc_bac ⟨AXB, XAB⟩
        · tauto
        · tauto
      have XoffExtensionAB : X off extension A B := by
        unfold Extension
        simp only [mem_setOf_eq]
        push_neg
        intro ABX
        exfalso;
        exact Betweenness.absurdity_abc_cab ⟨ABX, XAB⟩
      by_contra! hNeg
      rcases hNeg with XinSeg | XinExt
      repeat contradiction
    -- so X is off the ray but on the line, which can't be if the two things are equal.
    rw [<- LextendsRay] at XoffRayAB
    have XonL' := colXAB.mem X
    rw [L'eqL] at XonL'
    contradiction

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
  A - P - B -> P on the segment A B := by intro h; unfold Segment; simp; tauto;

lemma APB_imp_P_on_ray_AB (PneAB : P ≠ A ∧ P ≠ B) :
  A - P - B -> P on the ray A B := by intro h; unfold Ray; simp; tauto;

lemma ABP_imp_P_on_ext_AB (PneAB : P ≠ A ∧ P ≠ B) :
  A - B - P -> P on the extension A B := by
  intro h; unfold Extension; simp only [ne_eq, mem_setOf_eq, B1b];
  rw [B1b] at h
  tauto

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
