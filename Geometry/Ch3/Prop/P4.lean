import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory
import Geometry.Theory.Axioms
import Geometry.Tactics

import Geometry.Ch2.Prop
import Geometry.Ch3.Prop.P1
import Geometry.Ch3.Prop.B4iii
import Geometry.Ch3.Ex.Ex1
import Geometry.Theory.Distinct
import Geometry.Theory.Collinear.Ch1
import Geometry.Theory.Collinear.Ch2
import Geometry.Theory.Betweenness.Ch1
import Geometry.Theory.Betweenness.Ch2
import Geometry.Theory.Line.Ch1
import Geometry.Theory.Line.Ch2
import Geometry.Theory.Forgetting

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex


/-- p. 113 If C - A - B and l is the line through A, B, and C (Betweenness Axiom 1), then for every point P lying on l,
P lies either on ray A B or on the opposite ray A C. -/
theorem P4 {A B C P : Point} (CAB : C - A - B) (PonL : P on (line A B)) : P on ray A B ∨ P on ray A C := by 
  /- Ed. Some mise en place -/
  have distinctABCP : distinct A B C P := by sorry
  have colABCP : collinear A B C P := by sorry

  by_cases! suppose: P on ray A B
  /-       (1) Either P lies on ray A B or it does not (Law of the Excluded Middle) -/
  · /-     (2) If P does lie on ray A B, we are done... -/
    left; trivial
  · right
    /-         ... so assume it doesn't; then P - A - B (Betweenness Axiom 3) -/
    have PAB : P - A - B := by 
      -- have h := B3 P A B (distinctABCP forgetting C) (colABCP forgetting C)
      sorry
      
  
    /-     (3) If P = C, then P lies on ray A C (by definition) -/
    by_cases PneC : P ≠ C
    · /-       so assume P ≠ C; then exactly one of the relations C-A-P, C-P-A, or P-C-A holds (Betweeness Axiom 3
               again). -/
      /-   (4) Suppose the relation C-A-P holds (RAA Hypothesis -/
      by_cases CAP : C - A - P
      · /-   (5) We know (by Betweenness Axiom 3) that exactly one of the relations P-C-B, C-P-B, or C-B-P holds. -/
        /-   (6) If P-B-C, then combining this with P-A-B (step 2) gives A-B-C (Proposition 3.3), contradiction the
             hypothesis. -/
        /-   (7) If C-P-B, then combining this with C-A-P (step 4) gives A-P-B (Proposition 3.3), contradiction step 2. -/
        /-   (8) If B-C-P, then combining this with B-A-C (hypothesis and Betweenness Axiom 1) gives A-C-P (Proposition 3.3),
             contradicting step 4. -/
        /-   (9) Since we obtain a contradiction in all three cases, C-A-P does not hold (RAA conclusion). -/
        /-   (10) Therefore, C-P-A or P-C-A (step 3), which means that P lies on the opposite ray A C. ∎ -/
        sorry
      · sorry
    · push_neg at PneC; rw [PneC]; exact Line.ray_has_endpoints.right

end Geometry.Ch3.Prop


namespace Line

alias separation := Geometry.Ch3.Prop.P4

end Line
