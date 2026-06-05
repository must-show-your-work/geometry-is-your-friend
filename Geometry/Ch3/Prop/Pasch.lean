import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Distinct
import Geometry.Theory.Interpendices.B

import Geometry.Tactics

import Geometry.Ch3.Prop.B4iii

import Geometry.Construction.AtlasField
import Geometry.Construction.AtlasTactic
import Atlas

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Atlas


atlas commentary := by
  via theorem 3.0
  page 114
  aliases [
    Geometry.Theory.pasch,
    «Pasch's Postulate»,
    «Pasch's Proposition»
  ]
  name "Pasch's Theorem"
  preface "If A,B,C are distinct noncollinear points and L is any line intersecting AB in a point between A and B, then L
also intersects AC or BC (see figure 3.10). If C does not lie on L, then L does not intersect both AC and BC.
  
  Intuititively, this theorem says that if a line \"goes into\" a triangle through one side, it must \"come out\" through
another side."
  notes "The author doesn't give Pasch's a number, but also calls it a 'theorem', eschewing the possible alliteration.
  While this dodge is sad, it is the case, and theorems are fortunately numbered separately from propositions, solving our
  possible off-by-one situation. Perhaps our disappointment was worth it after all."

  figure := by
    construction {
      exists A B C : Point
      exists X : Point
      exists L : Line
      assert distinct A B C
      assert ¬ collinear A B C
      assert between A X B
      assert incident X L
      construct segAB := segment A B
      construct segBC := segment B C
      construct segAC := segment A C
    }
    title "Pasch's Theorem"
    index 1
    caption "Line L meets the interior of segment AB at X. The conclusion of Pasch is that L also meets exactly one of the other two segments — AC or BC — provided C is off L."

atlas theorem 3.0 "Pasch's Theorem"
  {A B C : Point} {L : Line} {distinctABC : distinct A B C} {AXB : A - X - B}
  (triABC : ¬(collinear A B C)) (LintSegAB : L intersects segment A B at X) :
  ((L intersects segment A C) ∨ (L intersects segment B C)) ∧
  (C off L -> ¬((L intersects segment A C) ∧ (L intersects segment B C))) := by
    comment "mise en place"
    separate at distinctABC
    clearly (segment A B : Line) ≠ (segment B C : Line) := by
      idea "if AB = BC, then ABC are collinear, which is a contradiction"
      have colABC : collinear A B C := by
        use (segment A B : Line)
        intro P PisABorC
        by_exhaustion PisABorC
        · obvious
        · obvious
        · rw [PeqC, SegABeqSegBC]; obvious
      auxillary { assert collinear A B C }
      contradiction
    clearly L ≠ segment A B := by exact absurd LeqSegAB.symm (via lemma 2.0.12)
    clearly L ≠ segment A C := by exact absurd LeqSegAC.symm (via lemma 2.0.12)
    clearly L ≠ segment B C := by exact absurd LeqSegBC.symm (via lemma 2.0.12)
    quoting (1) "Either C lies on L or it does not; if it does, the theorem holds (law the excluded middle)"
    clearly C off L := by
      auxillary { assert incident C L }
      have ConAC : C on segment A C := obvious
      have CinInt : C ∈ L ∩ segment A C := obvious
      have LintersectsAC : L intersects segment A C := ⟨C, ConL, ConAC⟩
      constructor
      · left; trivial
      · contrapose!; intro _; exact ConL
    quoting (2) "A and B do not lie on L," ...
    comment "Author asserts without proof, but it is obvious that these result in true instances for Pasch."
    clearly A off L := by
      auxillary { assert incident A L }
      constructor
      · left ; have AonAB : A on segment A C := obvious
        exact ⟨A, AonL, AonAB⟩
      · intros
        intuition "if A is on L, then since A is on AB and X is where L intersects AB, A = X, but A X B are distinct by
        assumption"
        have : A ∈ L ∩ segment A B := ⟨AonL, by obvious⟩
        rw [LintSegAB] at this
        have AeqX : A = X := this
        have dAXB := (via axiom B.1 AXB).distinct
        separate at dAXB
        contradiction
    clearly B off L := by
      auxillary { assert incident B L }
      idea "same as above"
      constructor
      · right ; have BonBC : B on segment B C := obvious
        exact ⟨B, BonL, BonBC⟩
      · intros
        have : B ∈ L ∩ segment A B := ⟨BonL, by obvious⟩
        rw [LintSegAB] at this
        have BeqX : X = B := this.symm
        have dAXB := (via axiom B.1 AXB).distinct
        separate at dAXB
        contradiction
    quoting ... "and the segment A B does intersect L (hypothesis and Axiom B-1)"
    comment "
    We already have the intersection hypothesis, so this is just mise en place, I suppose this _is_
    the author's justification that A and B are off L.
    "
    quoting (3) "Hence, A and B lie on opposite sides of L (by definition)"
    have LsplitsAB : L splits A and B := via corollary 2.0.22 (via lemma 3.7.2 LneSegAB LintSegAB.bare).choose_spec
    quoting (4) "From step 1 we may assume that C does not lie on L, in which case C is either on the same side of L as A or
           on the same side of L as B (separation axiom)"
    have LguardsACorBC : (L guards A and C) ∨ (L guards B and C) := by
      by_contra! ⟨LsplitsAC, LsplitsBC⟩
      exact absurd (via axiom B.4.ii ⟨LsplitsAB, LsplitsBC⟩) LsplitsAC
    rcases LguardsACorBC with LguardsAC | LguardsBC
    · quoting (5) "If C is on the same side of L as A, then C is on the opposite side from B, which means that L intersects BC
           and does not intersect AC" ...
      have LsplitsBC : L splits B and C := via corollary B.4.iii ⟨LsplitsAB.symm, LguardsAC⟩
      have LintBC : L intersects segment B C := via lemma 3.7.3 LsplitsBC
      have LguardsAC := via axiom B.4.ii ⟨LsplitsAB, LsplitsBC⟩
      constructor
      · right; exact LintBC
      · intro; push Not; contrapose!; intro;
        exact via corollary 3.7.3 LguardsAC
    · quoting ... "similarly, if C is on the same side of L as B, then L intersects AC and does not intersect BC (separation axiom)."
      have LsplitsAC := via corollary B.4.iii ⟨LsplitsAB, LguardsBC⟩
      have LintAC := via lemma 3.7.3 LsplitsAC
      constructor
      · left; exact LintAC
      · intro; push Not; intro;
        exact via corollary 3.7.3 LguardsBC
    quoting (6) "The conclusion of Pasch's theorem holds (Logic Rule 11 -- proof by cases). ∎"


end Geometry.Ch3.Prop


