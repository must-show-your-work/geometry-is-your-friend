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
open Atlas

atlas commentary := by
  ref proposition 3.1.i
  page 109
  name "Two rays from common endpoints intersect in their segment"
  preface "For any two points A and B: (i) Ray A B ∩ Ray B A = Segment A B ..."
  notes "I'm inserting this `A ≠ B` condition because the author never clearly states, but definitely implies, that `the ray A A` is degenerate because `A - A - B` and the like are degenerate"

atlas proposition 3.1.i "Two rays from common endpoints intersect in their segment"
  : A ≠ B -> (segment A B : Line) = (ray A B : Line) ∩ (ray B A : Line) := by
  intro AneB
  apply Line.eq_of_subset
  · quoting (1) "By the definition of segment and ray, the segment A B ⊆ the ray A B [and ⊆ ray B A], so by definition of intersection, the segment AB ⊆ (ray A B ∩ ray B A)."
    obvious
  · quoting (2) "Conversely, let the point C belong to the intersection, (ray A B ∩ ray B A); we wish to show that C belongs to the segment A B."
    intro C CinInt
    quoting (3) "If C = A or C = B, C is an endpoint of the segment A B" ...
    by_cases suppose : C = A ∨ C = B
    · obvious
    · quoting ... "Otherwise, A B and C are three collinear points (by the definition of ray and Axiom B-1)" ...
      have distinctABC : distinct A B C := by separate; obvious
      have colABC : collinear A B C := by
        use ray A B
        intro P PinABC
        by_exhaustion PinABC
        · rw [PeqA]; obvious
        · rw [PeqB]; obvious
        · rw [PeqC]; exact CinInt.left
      quoting ... "so exactly one of A - C - B, A - B - C, or C - A - B holds (Axiom B-3)." ...
      have ⟨ConAB, ConBA⟩ : C on ray A B ∧ C on ray B A := obvious
      rcases ref axiom B.3 A B C ⟨distinctABC, colABC⟩ with ⟨ABC, _, _⟩ | ⟨_, CAB, _⟩ | ⟨_, _ACB⟩
      · quoting (4) "If A - B - C holds, then C is not on the ray B A" ...
        have CoffBA : C off ray B A := by obvious
        contradiction
      · quoting ... "if C - A - B holds, then C is not on the ray A B." ...
        have CoffAB : C off ray A B := by obvious
        contradiction
      · quoting ... "In either case, C does not belong to both rays."
        quoting (5) "Hence, the relation A - C - B must hold, so C belongs to the segment A B (definition of the segment A B, proof by cases)."
        obvious


atlas commentary := by
  ref proposition 3.1.ii
  page 109
  name "Two rays from common endpoints union to their line"
  preface "... (ii) Ray A B ∪ Ray B A = LineThrough A B"
  notes "similar to the above, an implied A ≠ B condition was added"

atlas proposition 3.1.ii "Two rays from common endpoints union to their line"
  : A ≠ B -> (ray A B : Line) ∪ (ray B A : Line) = (line A B : Line) := by
  intro AneB
  apply Line.eq_of_subset
  · intro P PinUnion
    rcases PinUnion with PinAB | PinBA
    · exact ref lemma 1.0.18 PinAB
    · apply ref lemma 1.0.18 at PinBA
      rwa [(@Line.«Line Commutativity» A B AneB)]
  · intro P PinLine
    -- Need to handle the equality cases first, we'll refer to these later in the proof
    by_cases AneP : A = P
    · rw [<- AneP]; exact mem_union_left (ray B A) (by obvious : A on ray A B)
    by_cases BneP : B = P
    · rw [<- BneP]; exact mem_union_left (ray B A) (by obvious : B on ray A B)
    -- the main proof
    rcases PinLine with eq | eq | tween | tween | tween
    -- the equality cases are handled separately above
    · exfalso; exact absurd eq.symm AneP
    · exfalso; exact absurd eq.symm BneP
    -- the case where P is on the segment
    · have PonSegAB : P on segment A B := obvious
      have PonRayAB : P ∈ (ray A B : Line) := by obvious
      exact mem_union_left _ PonRayAB
    -- this is where we need the PneA and PneB conditions
    · have PonExtAB : P on extension A B := obvious
      left; right; exact PonExtAB
    -- here too, P is on the other extension
    · have PonExtBA : P on extension B A := obvious
      right; right; exact PonExtBA

end Geometry.Ch3.Prop
