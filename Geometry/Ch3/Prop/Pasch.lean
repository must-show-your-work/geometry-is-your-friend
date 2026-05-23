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
import Atlas

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas


atlas commentary := by
  ref proposition 3.7
  page 114
  aliases [
    Geometry.Theory.pasch
  ]
  name "Pasch's Postulate"
  preface "If A,B,C are distinct noncollinear points and L is any line intersecting AB in a point between A and B, then L
also intersects AC or BC (see figure 3.10). If C does not lie on L, then L does not intersect both AC and BC.
  
  Intuititively, this theorem says that if a line \"goes into\" a triangle through one side, it must \"come out\" through
another side."

atlas proposition 3.7 "Pasch's Postulate"
  {A B C : Point} {L : Line}
  (triABC : ¬(collinear A B C)) (LintSegAB : L intersects segment A B) :
  ((L intersects segment A C) ∨ (L intersects segment B C)) ∧
  (C off L -> ¬((L intersects segment A C) ∧ (L intersects segment B C))) := by
    comment "mise en place"
    clearly segment A B ≠ segment B C := by
      idea "if AB = BC, then ABC are collinear, which is a contradiction"
      have colABC : collinear A B C := by
        use segment A B
        intro P PisABorC
        by_exhaustion PisABorC
        repeat obvious
      contradiction
    clearly L ≠ segment A C := by
      constructor
      · rw [LeqSegAC]; left; exact ref lemma 3.0.2
      · intro CoffL; rw [LeqSegAC] at CoffL
        exact absurd obvious CoffL
    clearly L ≠ segment B C := by
      constructor
      · rw [LeqSegBC]; right; exact ref lemma 3.0.2
      · intro CoffL; rw [LeqSegBC] at CoffL
        exact absurd obvious CoffL
    quoting (1) "Either C lies on L or it does not; if it does, the theorem holds (law the excluded middle)"
    clearly C off L := by
      have ConAC : C on segment A C := obvious
      have CinInt : C ∈ L ∩ segment A C := by tauto
      have LintersectsAC : L intersects segment A C := by use C
      constructor
      · left; trivial
      · contrapose!; intro _; exact ConL
    quoting (2) "A and B do not lie on L," ...
    fixme "Do I need to dispatch both at once? is that easier than one or the other? This argument is kinda messy"
    comment "Author asserts without proof, but it is obvious that these result in true instances for Pasch."
    clearly A off L := by
      idea "if A on L, clearly L intersects AC, since A is on L and AC."
      constructor
      · have AonAC : A on segment A C := obvious
        left; obvious
      · intro _; push Not; intro LintAC;
        by_contra! LintBC
        intuition "If L intersects all three, then there is a sort of 'collinear-transititvity' that happens." 
        todo "Make the lookup coerce between types here, segment ⊆ ray ⊆ linethrough, etc"
        have colABC := ref corollary 3.7.1 ⟨LintSegAB, LintBC, LintAC⟩
        contradiction
    clearly B off L := by
      idea "similar to the above"
      constructor
      · have BonBC : B on segment B C := obvious
        right; obvious
      · intro _; push Not; intro LintAC;
        by_contra! LintBC
        have colABC := ref corollary 3.7.1 ⟨LintSegAB, LintBC, LintAC⟩
        contradiction
    quoting ... "and the segment A B does intersect L (hypothesis and Axiom B-1)"
    comment "
    We already have the intersection hypothesis, so this is just mise en place, I suppose this _is_
    the author's justification that A and B are off L.
    "
    quoting (3) "Hence, A and B lie on opposite sides of L (by definition)"
    have LsplitsAB : L splits A and B := via corollary 2.0.25 (via lemma 3.7.2 LintSegAB).choose_spec
    quoting (4) "From step 1 we may assume that C does not lie on L, in which case C is either on the same side of L as A or
           on the same side of L as B (separation axiom)"
    have LguardsACorBC : (L guards A and C) ∨ (L guards B and C) := by
      by_contra! ⟨LsplitsAC, LsplitsBC⟩
      exact absurd (ref axiom ["B.4.ii"] ⟨LsplitsAB, LsplitsBC⟩) LsplitsAC
    rcases LguardsACorBC with LguardsAC | LguardsBC
    · quoting (5) "If C is on the same side of L as A, then C is on the opposite side from B, which means that L intersects BC
           and does not intersect AC" ...
      have LsplitsBC : L splits B and C := ref corollary ["B.4.iii"] ⟨LsplitsAB.symm, LguardsAC⟩
      have LintBC : L intersects segment B C := via lemma 3.7.3 LsplitsBC
      have LguardsAC := ref axiom ["B.4.ii"] ⟨LsplitsAB, LsplitsBC⟩
      constructor
      · right; exact LintBC
      · intro; push Not; contrapose!; intro;
        exact ref corollary 3.7.3 LguardsAC
    · quoting ... "similarly, if C is on the same side of L as B, then L intersects AC and does not intersect BC (separation axiom)."
      have LsplitsAC := ref corollary ["B.4.iii"] ⟨LsplitsAB, LguardsBC⟩
      have LintAC := via lemma 3.7.3 LsplitsAC
      constructor
      · left; exact LintAC
      · intro; push Not; intro;
        exact ref corollary 3.7.3 LguardsBC
    quoting (6) "The conclusion of Pasch's theorem holds (Logic Rule 11 -- proof by cases). ∎"


end Geometry.Ch3.Prop

