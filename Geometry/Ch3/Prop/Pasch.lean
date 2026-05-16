import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory
import Geometry.Theory.Axioms
import Geometry.Tactics

import Geometry.Ch2.Prop
import Geometry.Ch3.Prop.P1
import Geometry.Ch3.Prop.B4iii
import Geometry.Ch3.Prop.P2
import Geometry.Ch3.Prop.P3
import Geometry.Ch3.Prop.P4
import Geometry.Ch3.Ex.Ex1
import Geometry.Theory.Distinct
import Geometry.Theory.Collinear.Ch1
import Geometry.Theory.Collinear.Ch2
import Geometry.Theory.Betweenness.Ch1
import Geometry.Theory.Betweenness.Ch2
import Geometry.Theory.Line.Ch1
import Geometry.Theory.Line.Ch2
import Geometry.Theory.Forgetting
import Geometry.Theory.Intersection.Ch3

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex

/-- p.114 If A,B,C are distinct noncollinear points and L is any line intersecting AB in a point between A and B, then L
also intersect AC or BC (see figure 3.10). If C does not lie on L, then L does not intersect both AC and BC.

  Intuititively, this theorem says that if a line "goes into" a triangle through one side, it must "come out" through
another side.-/
theorem pasch {A B C : Point} {L : Line}
  (triABC : ¬(collinear A B C)) (LintSegAB : L intersects segment A B) :
  ((L intersects segment A C) ∨ (L intersects segment B C)) ∧
  (C off L -> ¬((L intersects segment A C) ∧ (L intersects segment B C))) := by
    /- Ed: mise en place -/
    clearly segment A B ≠ segment B C := by
      -- idea: if AB = BC, then ABC are collinear, which is a contradiction
      have colABC : collinear A B C := by
        use segment A B
        intro P PisABorC
        by_exhaustion PisABorC
        repeat obvious
      contradiction
    clearly L ≠ segment A C := by
      constructor
      · rw [LeqSegAC]; left; exact Intersection.coincident_lines_intersect_everywhere
      · intro CoffL; rw [LeqSegAC] at CoffL
        exact absurd Line.seg_has_endpoints.right CoffL
    clearly L ≠ segment B C := by
      constructor
      · rw [LeqSegBC]; right; exact Intersection.coincident_lines_intersect_everywhere
      · intro CoffL; rw [LeqSegBC] at CoffL
        exact absurd Line.seg_has_endpoints.right CoffL
    /- (1) Either C lies on L or it does not; if it does, the theorem holds (law the excluded middle) -/
    clearly C off L := by
      have ConAC : C on segment A C := Line.seg_has_endpoints.right
      have CinInt : C ∈ L ∩ segment A C := by tauto
      have LintersectsAC : L intersects segment A C := by use C
      constructor
      · left; trivial
      · contrapose!; intro _; exact ConL
    /- (2) A and B do not lie on L, ... -/
    -- Ed: Author asserts without proof, but it is obvious that these result in true instances for Pasch.
    clearly A off L := by
      -- if A on L, then L intersects segment A C at A, and L does not intersect B C at all, since A is off BC
      have AonAC : A on segment A C := obvious
      have AoffBC : A off segment B C := by
        -- triABC is the play here; have collinear B C (via segment B C), so since ¬ collinear {A,B,C}, contra
        sorry
      have LavoidsBC : L ∩ segment B C = ∅ := by sorry
      constructor
      · have AinInt : A ∈ L ∩ segment A C := obvious
        obvious
      · intros; push_neg; intro LintAC; by_contra! LintBC
        have colABC : collinear A B C := by
          sorry
        contradiction
    clearly B off L := by
      -- similar arg to above
      sorry
    /- ... and the segment A B does intersect L (hypothesis and Axiom B-1) -/
    -- Ed: We already have the intersection hypothesis, so this is just mise en place, I suppose this _is_
    -- the author's justification that A and B are off L.
    /- (3) Hence, A and B lie on opposite sides of L (by definition) -/
    have LsplitsAB : L splits A and B := by
      sorry
    /- (4) From step 1 we may assume that C does not lie on L, in which case C is either on the same side of L as A or
           on the same side of L as B (separation axiom) -/
    have LguardsACorBC : (L guards A and C) ∨ (L guards B and C) := by sorry
    rcases LguardsACorBC with LguardsAC | LguardsBC
    · /- (5) If C is on the same side of L as A, then C is on the opposite side from B, which means that L intersects BC
           and does not intersect AC ... -/
      sorry
    · /- ... similarly, if C is on the same side of L as B, then L intersects AC and does not intersect BC (separation axiom). -/
      sorry
    /- (6) The conclusion of Pasch's theorem holds (Logic Rule 11 -- proof by cases). ∎ -/


end Geometry.Ch3.Prop

namespace Geometry.Theory

/- Ed: this is a 'standard' geometric theorem that is necessary for results regardless of underlying axiomatization, so 
I'm aliasing it to the top level 'Theory' namespace so it can be referenced as such, similar to P4's aliasing into the
Line namespace. There is no other natural namespace for Pasch so I put it here. -/
alias pasch := Geometry.Ch3.Prop.pasch

end Geometry.Theory

