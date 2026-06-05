import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Distinct
import Geometry.Theory.Interpendices.B

import Geometry.Tactics

import Geometry.Construction.AtlasField
import Atlas

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Atlas

atlas commentary := by
  via proposition 3.2
  page 112
  name "Every line bounds exactly two disjoint half-planes"
  preface "Every line bounds exactly two half-planes, and these half-planes have no point in common."
  notes "B4 is the plane-separation axiom, 3.2 here is on the path toward proving the more useful line-separation property later in 3.4.
I've chosen to notate the halfplanes in the theorem as 'Hl' and 'Hr' for 'left' and 'right' half-plane, respectively."

  -- Figure flagged for revision (2026-06-03). The current draft doesn't
  -- convey "two disjoint half-planes bounded by L"; revisit when the
  -- solver can draw region fills or when we have a chosen layout for
  -- showing P / Q on opposite sides without ambiguity.
  -- figure := by
  --   construction {
  --     exists A B P Q : Point
  --     exists L : Line
  --     assert distinct A B
  --     assert ¬ collinear A P Q
  --     assert incident A L
  --     assert incident B L
  --   }
  --   title "Proposition 3.2"
  --   index 1
  --   caption "Line L (through A and B) bounds two disjoint half-planes; P and Q sit on opposite sides."

atlas proposition 3.2 "Every line bounds exactly two disjoint half-planes"
  : ∀ L : Line, L = line A B -> A ≠ B -> ∃ Hl Hr : Set Point,
  (∀ P : Point, (P on L) -> (P ∉ Hl) ∧ (P ∉ Hr)) ∧ (Hl ∩ Hr = ∅)
:= by
  quoting (1) "There is a point A not lying on l, (Proposition 2.3 [proposition 2.3])."
  intro L LeqLineAB AneB
  obtain ⟨A, AoffL⟩ := proposition 2.3 L
  quoting (2) "There is a point O lying on l (Incidence Axiom 2 [via axiom I.2])."
  obtain ⟨O, _, _, OonL, _⟩ := via axiom I.2 L
  quoting (3) "There is a point B such that B * O * A (Betweenness Axiom 2 [via axiom B.2])"
  have AneO : A ≠ O := by -- author omits this step
    by_contra!; rw [this] at AoffL; obvious
  have ⟨B, _, _, colBOA, distinctBOA, bBOA, _, _⟩ := via axiom B.2 O A AneO.symm
  have AneB : A ≠ B := by distinguish
  have LneAO : L ≠ segment A O := by
    by_contra! hNeg;
    rw [hNeg] at AoffL;
    have AonAO : A on segment A O := by obvious
    contradiction
  have LnoparAO : L ∦ segment A O := by
    by_contra! hNeg
    unfold Parallel at hNeg
    have ⟨LneAO, parCondition⟩ := hNeg
    push Not at parCondition
    have OonAO : O on segment A O := obvious
    specialize parCondition O OonL
    contradiction
  have BoffL : B off L := by
    idea "since A is off L, and O is on, the AO intersects L at O, extend AO, since AOB, then B is on this extension."
    have ⟨distinctBOA, colBOA, _⟩ := via axiom B.1 bBOA
    separate at distinctBOA
    have LintAOatO : L intersects segment A O at O := by
      unfold Intersects
      have OonAO : O on segment A O := by obvious
      have OonInt : O on L ∩ segment A O := by obvious
      exact (via lemma 2.0.17 O L (segment A O) ⟨LneAO, LnoparAO⟩).mp OonInt
    have h := via lemma 2.0.18 AneO LintAOatO
    unfold Ray at h
    have BonExtAO : B on extension A O := ⟨bBOA.symm, AneB, BneO.symm⟩
    have BonRayAO : B on ray A O := by obvious
    unfold Intersects at h
    by_contra! BonL
    have BonInt : B ∈ (L ∩ ray A O) := by obvious
    rw [h] at BonInt
    have BeqO : B = O := by obvious
    contradiction
  quoting (4) "Then A and B are on opposite sides of l (by definition)," ...
  have LsplitsAB : L splits A and B := by
    unfold Splits Guards
    push Not
    intro AoffL BoffL
    refine ⟨AneB, O, ?_, OonL⟩
    obvious
  quoting ... "so L has at least two sides."
  quoting (5) "Let C be any point distinct from A and B not lying on l" ...
  comment "Construct point C off L and distinct from A and B as follows.

  1. Take AB and find it's intersection by L, call it O (since that's where it is)
  2. Examine segment A O with via axiom B.2, we want C with A - C - O
  3. Use C."
  comment "Here are the sets we require"
  let Hl : Set Point := {P | L guards A and P}
  let Hr : Set Point := {P | L guards B and P}
  let PsoffL : Set Point := {P | P off L}
  comment "Use our sets"
  use Hl
  use Hr
  quoting ... "So the set of points not on L is the union of side Hₐ of A and the side Hₐ of B."
  comment "Note, to formalize this, we need to state the claim first."
  have claim : PsoffL = Hl ∪ Hr := by
    apply Subset.antisymm
    · intro C CinPsoffL
      have CoffL : C off L := by tauto
      simp only [mem_union]
      quoting ... "If C and B are not on the same side of L,"
      have AseparatefromB : (L splits B and C) -> (L guards A and C) := by
        intro LsplitsBC
        quoting ... "then C and A are on the same side of L (by the law of the excluded middle and Betweenness Axiom 4(ii))."
        by_contra LsplitsAC
        have LguardsAB := via axiom B.4.ii ⟨LsplitsAC, LsplitsBC.symm⟩
        contradiction
      by_cases suppose: L splits B and C
      · specialize AseparatefromB suppose
        have CinHl : C ∈ Hl := by tauto
        obvious
      · push Not at suppose
        have CinHr : C ∈ Hr := by tauto
        obvious
    · intro C CinUnion
      rcases CinUnion with CinHl | CinHr
      rw [Set.mem_setOf_eq] at *;
      · obtain ⟨_, CoffL, hOpts⟩ := CinHl
        rcases hOpts with AeqC | hCond
        · exact CoffL
        · by_contra! hNeg
          contradiction
      · obtain ⟨BoffL, CoffL, hOpts⟩ := CinHr
        tauto
  quoting (6) "If C were on both sides (RAA Hypothesis), then A and B would be on the
  same side (Axiom 4(i) [via axiom B.4.i]), contradicting step 4; hence the two sides are
  disjoint."
  have HlintHrempty : Hl ∩ Hr = ∅ := by
    apply Subset.antisymm
    · intro P PinInt
      obtain ⟨PinHl, PinHr⟩ := PinInt
      have LguardsAandP : L guards A and P := PinHl
      have LguardsBandP : L guards B and P := PinHr
      have LguardsPandB : L guards P and B := LguardsBandP.symm
      have PoffL : P off L := by tauto
      have LguardsAandB : L guards A and B := via axiom B.4.i ⟨LguardsAandP, LguardsPandB⟩
      contradiction
    · intro P PinEmpty
      contradiction
  refine ⟨?g, HlintHrempty⟩
  comment "this last section is perhaps not _quite_ what the author had, but it works
  and I've been working on formalizing this for a while now, so call it good enough."
  intro C ConL
  by_cases CinHl : C ∈ Hl
  · exfalso;
    have LguardsAandC : L guards A and C := CinHl
    have CoffL : C off L := by tauto
    contradiction
  by_cases CinHr : C ∈ Hr
  · exfalso;
    have LguardsBandC : L guards B and C := CinHr
    have CoffL : C off L := by tauto
    contradiction
  obvious


/- I was frequently left to my own devices with respect to school. We did a correspondence video thing.
I'd sit in the same room, for a while it was the couch in the living room, later it was a hard dining chair in our
'dining room' (that we didn't really use very much as a dining room). I'd watch hours of video taped lectures, most
already over ten years old in most cases. I remember one course was recorded well before I was born, and the teacher
talked excitedly about how, one day, you might even get to own a computer.

I remember jumping online and looking up what kind of personal computers were available in 1982 or whatever year it was.
I remember thinking that the videos probably weren't going to be where I'd learn most of what I'd learn. I remember
thinking the internet was a much better place to look for truth. -/

end Geometry.Ch3.Prop
