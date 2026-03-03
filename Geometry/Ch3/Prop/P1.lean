import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Ch2
import Geometry.Theory.Line.Ch2

import Geometry.Tactics

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory

-- Ed. I'm inserting this `A ≠ B` condition because the author never clearly
-- states, but definitely implies, that `the ray A A` is degenerate because `A
-- - A - B` and the like are degenerate
/-- p.109, "For any two points A and B: (i) Ray A B ∩ Ray B A = Segment A B ..." -/
theorem P1.i : A ≠ B -> (segment A B) = (ray A B) ∩ (ray B A) := by
  intro AneB
  apply Subset.antisymm
  · /- "Proof of (i):
       (1) By the definition of segment and ray, the segment A B ⊆ the ray A B [and ⊆ ray B A],
       so by definition of intersection, the segment AB ⊆ (ray A B ∩ ray B A)." -/
    exact subset_inter Line.seg_sub_ray Line.segment_AB_sub_ray_BA
  · /- (2) Conversely, let the point C belong to the intersection, `(ray A B ∩ ray B A)`; we wish
        to show that C belongs to the segment A B. -/
    intro C CinInt
    /- (3) If C = A or C = B, C is an endpoint of the segment A B ..." -/
    by_cases suppose : C = A ∨ C = B
    · tauto
    · /- "... Otherwise, A B and C are three collinear points (by the definition of ray and Axiom B-1)..." -/
      have distinctABC : distinct A B C := by separate; tauto
      have colABC : collinear A B C := by
        use ray A B
        intro P PinABC
        simp only [List.mem_cons, List.not_mem_nil, or_false] at PinABC
        rcases PinABC with eq | eq | eq
        · rw [eq]; exact Line.ray_has_endpoints.left
        · rw [eq]; exact Line.ray_has_endpoints.right
        · rw [eq]; exact CinInt.left
      /- "so exactly one of A - C - B, A - B - C, or C - A - B holds (Axiom B-3). ..." -/
      have ⟨ConAB, ConBA⟩ : C on ray A B ∧ C on ray B A := by tauto
      rcases B3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, _, _⟩ | ⟨_, CAB, _⟩ | ⟨_, _ACB⟩
      · /- "... (4) If A - B - C holds, then C is not on the ray B A; ..." -/
        exfalso;
        have CoffBA : C off ray B A := by
          simp only [mem_union, mem_setOf_eq, B1b, ne_eq, not_or, not_and, not_not]
          tauto
        contradiction
      · /- "... if C - A - B holds, then C is not on the ray A B. ..." -/
        exfalso;
        have CoffAB : C off ray A B := by
          simp only [mem_union, mem_setOf_eq, ne_eq, not_or, not_and, not_not]
          tauto
        contradiction
      · /- "... In either case, C does not belong to both rays.
          (5) Hence, the relation A - C - B must hold, so C belongs to the segment A B (definition of the segment A B, proof by
          cases)." -/
        tauto

/-- p.109 "... (ii) Ray A B ∪ Ray B A = LineThrough A B" -/
theorem P1.ii : A ≠ B -> -- Ed. Same as above.
  (ray A B) ∪ (ray B A) = (line A B) := by
  intro AneB
  apply Subset.antisymm
  · intro P PinUnion
    rcases PinUnion with PinAB | PinBA
    · exact Line.ray_sub_line PinAB
    · apply Line.ray_sub_line at PinBA
      rwa [(@Line.commutes A B AneB)]
  · intro P PinLine
    -- Need to handle the equality cases first, we'll refer to these later in the proof
    by_cases AneP : A = P
    · rw [<- AneP]; exact mem_union_left (ray B A) Line.ray_has_endpoints.left
    by_cases BneP : B = P
    · rw [<- BneP]; exact mem_union_left (ray B A) Line.ray_has_endpoints.right
    -- the main proof
    rcases PinLine with eq | eq | tween | tween | tween
    -- the equality cases are handled separately above
    · exfalso; exact absurd eq.symm AneP
    · exfalso; exact absurd eq.symm BneP
    -- the case where P is on the segment
    · have PonSegAB : P on segment A B := by
        simp only [mem_setOf_eq]
        left; exact tween
      exact mem_union_left (ray B A) (Line.seg_sub_ray PonSegAB)
    -- this is where we need the PneA and PneB conditions
    · have PonExtAB : P on extension A B := by
        simp only [mem_setOf_eq]
        exact ⟨tween, AneP, BneP⟩
      left; right; exact PonExtAB
    -- here too, P is on the other extension
    · have PonExtBA : P on extension B A := by
        simp only [mem_setOf_eq]
        exact ⟨B1b.mp tween, BneP, AneP⟩
      right; right; exact PonExtBA

/- -- TODO: This is ugly. --

  intro AneB
  ext P
  constructor
  -- Forward Case: Idea, unfold all the set stuff and apply some commutativity rules
  -- to build everything
  intro hPonRayUnion
  rcases hPonRayUnion with hPonRayAB | hPonRayBA
  · exact Line.all_points_on_a_ray_are_collinear hPonRayAB
  · simp only [mem_setOf_eq]; unfold Ray at hPonRayBA;
    rcases hPonRayBA with hPonSegmentBA | hPonExtensionBA
    · rw [Line.segment_AB_eq_segment_BA] at hPonSegmentBA; exact Line.all_points_on_a_segment_are_collinear hPonSegmentBA
    · rw [Collinear.commutes.left]; exact Line.all_points_on_an_extension_are_collinear hPonExtensionBA
      -- Backward Case: Just check all the cases.
      intro hPonLine
      unfold LineThrough at *;
      have ⟨L, ⟨AonL, BonL, PonL⟩⟩ := hPonLine
      by_cases suppose: P = A ∨ P = B
      -- Easy case first, this is degenerate
      -- now if P = A, and P = B, then A = B, which is false.
      rcases suppose with PeqA | PeqB
      rw [PeqA]; simp only [mem_union, mem_setOf_eq, true_or, or_true, ne_eq, not_true_eq_false, false_and, and_false, or_false, Line.segment_AB_eq_segment_BA, or_self]
      rw [PeqB]; simp only [mem_union, mem_setOf_eq, or_true, ne_eq, not_true_eq_false, and_false, or_false, Line.segment_AB_eq_segment_BA, false_and, or_self]
      -- Now we have that A B and P are distinct
      have hABPdistinct := by push_neg at suppose; exact suppose
      -- Assuming P distinct, B3 + Collinearity means only one betweenness is possible:
      obtain (⟨bABP, nBAP, nAPB⟩ | ⟨nABP, bBAP, nAPB⟩ | ⟨nABP, nBAP, bAPB⟩) := B3 A B P ⟨AneB, hABPdistinct.right.symm, hABPdistinct.left.symm, hPonLine⟩
      -- the first assumption here is that P is on the extension
      obtain hPonExtAB : P on the extension A B := Line.ABP_imp_P_on_ext_AB hABPdistinct bABP
      -- so it's easy to fulfill the definition and do the set algebra
      unfold Ray; rw [<- Line.segment_AB_eq_segment_BA]; rw [@union_union_union_comm, union_self, union_comm];
      -- then we just have to dig a little.
      constructor; left; exact hPonExtAB
      --
      -- B - A - P is the same argument in the other direction.
      obtain hPonExtBA : P on the extension B A := Line.ABP_imp_P_on_ext_AB (id (And.symm hABPdistinct)) bBAP
      unfold Ray; rw [<- Line.segment_AB_eq_segment_BA]; rw [@union_union_union_comm, union_self, union_comm];
      constructor; right; exact hPonExtBA
      --
      -- APB means we're on the segment, not the extension, otherwise a similar argument
      obtain hPonsegAB : P on the segment A B := Line.APB_imp_P_on_segment_AB hABPdistinct bAPB
      unfold Ray; tauto
-/

end Geometry.Ch3.Prop
