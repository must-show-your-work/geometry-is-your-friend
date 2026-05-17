import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Ch2
import Geometry.Theory.Line.Ch2

import Geometry.Tactics
import Atlas

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory

-- Ed. I'm inserting this `A ≠ B` condition because the author never clearly
-- states, but definitely implies, that `the ray A A` is degenerate because `A
-- - A - B` and the like are degenerate
/-- p.109, "For any two points A and B: (i) Ray A B ∩ Ray B A = Segment A B ..." -/
atlas proposition 3.1 "Two rays from common endpoints intersect in their segment"
  : A ≠ B -> (segment A B) = (ray A B) ∩ (ray B A) := by
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
      have distinctABC : distinct A B C := by
        push_neg at suppose
        obtain ⟨CneA, CneB⟩ := suppose
        refine ⟨?_⟩
        simp only [Finset.card_insert_eq_ite, Finset.card_singleton,
                   Finset.mem_insert, Finset.mem_singleton,
                   AneB, CneA.symm, CneB.symm, if_false, or_false]
      have colABC : collinear A B C := by
        use ray A B
        intro P PinABC
        simp only [Finset.mem_insert, Finset.mem_singleton] at PinABC
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

alias P1.i := «Two rays from common endpoints intersect in their segment»

/-- p.109 "... (ii) Ray A B ∪ Ray B A = LineThrough A B" -/
atlas proposition 3.1 "Two rays from common endpoints union to their line"
  : A ≠ B -> -- Ed. Same as above.
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
    · have PonSegAB : P on segment A B := obvious
      exact mem_union_left (ray B A) (Line.seg_sub_ray PonSegAB)
    -- this is where we need the PneA and PneB conditions
    · have PonExtAB : P on extension A B := obvious
      left; right; exact PonExtAB
    -- here too, P is on the other extension
    · have PonExtBA : P on extension B A := obvious
      right; right; exact PonExtBA

alias P1.ii := «Two rays from common endpoints union to their line»

end Geometry.Ch3.Prop
