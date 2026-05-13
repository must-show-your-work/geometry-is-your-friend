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


/-- p112. Given A - B - C and A - C - D, then B - C - D and A - B - D (see Figure 3.9) -/
theorem P3.left : (A - B - C) ∧ (A - C - D) -> B - C - D := by
  /- (1) A, B, C, and D are distinct, collinear points (see Exercise 1). -/
  intro ⟨ABC, ACD⟩
  have distinctABCD := Ex1.a ⟨ABC, ACD⟩
  separate at distinctABCD
  have cL := Ex1.b ⟨ABC, ACD⟩
  /- (2) There exists a point E not on the line through A,B,C,D (Proposition 2.3) -/
  have LeqAB : cL = line A B := Line.equiv AneB
    ⟨cL.mem A, Line.line_has_definition_points.left, cL.mem B, Line.line_has_definition_points.right⟩
  have ⟨E, EoffcL⟩ := Ch2.Prop.P3 cL
  /- (3) Consider line EC. Since (by hypothesis) AD meets this line in point C,... -/
  let EC := line E C
  -- {Ed} Missing these simple conditions
  -- NOTE: have to be specific here to avoid coercion issues.
  have BonAB : B on cL.line := cL.mem B
  have DonAB : D on cL.line := cL.mem D
  -- TODO: I need better tools for proving lines different from each other
  have LneEC : cL ≠ EC := by
    have EonEC : E on EC := Line.line_has_definition_points.left
    by_contra! hNeg; rw [hNeg] at EoffcL; contradiction
  have ConEC : C on EC := Line.line_has_definition_points.right
  have ConLintEC : C on cL ∩ EC := ⟨cL.mem C, ConEC⟩
  have LnparEC : cL ∦ EC := by
    by_contra! hNeg
    have emptyInter := Intersection.parallel_intersection_is_empty cL EC LneEC hNeg
    rw [emptyInter] at ConLintEC
    contradiction
  have LintECatC : cL intersects EC at C := (Intersection.single_point_of_intersection C cL EC ⟨LneEC, LnparEC⟩).mp ConLintEC
  have AoffEC : A off EC := (Intersection.miss_means_off AneC LintECatC).resolve_left (not_not.mpr (cL.mem A))
  have BoffEC : B off EC := (Intersection.miss_means_off BneC LintECatC).resolve_left (not_not.mpr (cL.mem B))
  have DoffEC : D off EC := (Intersection.miss_means_off CneD.symm LintECatC).resolve_left (not_not.mpr (cL.mem D))
  -- {/Ed}
  /- ... points A and D are on opposite sides of EC -/
  have ECsplitsAandD : EC splits A and D := Intersection.splits_points ACD (Intersection.symm.mpr LintECatC)
  /- (4) We claim A and B are on the same side of EC. Assume on the contrary that A and B are on opposite sides of EC
     (RAA Hypothesis)

     {Ed} This section is proved without the use of Intersection.between_splits, which matches the book closely, but the core
     argument is not extracted, just left to intuition. This is fine for humans, but it means a very long and inscrutable
     proof in Lean, replicated ~4 times over, which sucks. So this matches the book, the other branches of this will use the
     lemma. {/Ed}
  -/
  by_cases raa : EC splits A and B
  · /- p113. (5) Then EC meets AB in a point between A and B (definition of "opposite sides" [ed. "splits" in our parlance]). -/
    have ⟨X, LintECatX, Xuniq⟩ : ∃! X : Point, (cL intersects EC at X) := by
      rcases Line.line_trichotomy cL EC with LparEC | LintECatX | LeqEC
      · exfalso; rwa [LparEC] at ConLintEC
      · exact LintECatX
      · exfalso; rw [<- LeqEC] at AoffEC; contradiction
    -- {Ed} need this for a step below
    have ⟨XonL, XonEC⟩ := Intersection.inter_touch LintECatX
    -- {/Ed}
    have AXB : A - X - B := by
      have colAXB : collinear A X B := by
        use cL
        intro P PinAXB
        simp only [List.mem_cons, List.not_mem_nil, or_false] at PinAXB
        rcases PinAXB with PeqA | PeqX | PeqB
        · rw [PeqA, LeqAB]; exact Line.line_has_definition_points.left
        · rwa [PeqX]
        · rw [PeqB, LeqAB]; exact Line.line_has_definition_points.right
      have AneX : A ≠ X := by by_contra! hNeg; rw [hNeg] at AoffEC; contradiction
      have BneX : B ≠ X := by by_contra! hNeg; rw [hNeg] at BoffEC; contradiction
      have distinctAXB : distinct A X B := by separate; tauto
      rcases B3 A X B ⟨distinctAXB, colAXB⟩ with ⟨AXB, _⟩ | reject
      · exact AXB
      · have ECguardsAB : EC guards A and B := by
          refine ⟨AoffEC, BoffEC, Or.inr ?_⟩
          by_contra! hNeg
          have ⟨P, PonAB, PonEC⟩ := hNeg
          have PinIntLine : P ∈ EC ∩ (line A B) := Set.inter_subset_inter_right EC Line.seg_sub_line ⟨PonEC, PonAB⟩
          have APB : A - P - B := by
            rcases PonAB with APB | AeqP | BeqP
            · exact APB
            · exfalso; rw [<- AeqP] at PonEC; contradiction
            · exfalso; rw [<- BeqP] at PonEC; contradiction
          have PeqX : P = X := Intersection.intersection_is_unique cL EC LneEC LnparEC ⟨LeqAB.symm ▸ PinIntLine.symm, ⟨XonL, XonEC⟩⟩
          rcases reject with ⟨_, XAB, _⟩ | ⟨_, _, ABX⟩
          · exact Betweenness.absurdity_abc_bac ⟨PeqX.symm ▸ XAB, APB⟩
          · exact Betweenness.absurdity_abc_acb ⟨APB, PeqX.symm ▸ ABX⟩
        contradiction
    /- (6) That point must be C (Proposition 2.1) -/
    have CeqX : C = X := Intersection.uniq ⟨LintECatC, LintECatX⟩
    /- (7) Thus A - B - C and A - C - B, which contradicts Betweenness Axiom 3. -/
    have ACB : A - C - B := CeqX.symm ▸ AXB
    exfalso; exact Betweenness.absurdity_abc_acb ⟨ABC, ACB⟩
  · /- (8) Hence, A and B are on the same side of EC (RAA conclusion) -/
    push_neg at raa
    /- (9) B and D are on opposite sides of EC (steps 3 and 8 and the corrolary to Betweenness Axiom 4). -/
    have ECsplitsBandD : EC splits B and D := by
      by_contra! ECguardsBandD
      have h := B4i ⟨AoffEC, BoffEC, DoffEC⟩ ⟨raa, ECguardsBandD⟩
      contradiction
    /- (10) Hence, the point C of intersection of lines EC and BD lies between B and D (definition of "opposite sides";
       Proposition 2.1, i.e., that the point of intersection is unique). -/
    unfold SameSide at ECsplitsBandD
    push_neg at ECsplitsBandD
    specialize ECsplitsBandD BoffEC DoffEC
    have ⟨BneD, P, ⟨PonSegBD, PonEC⟩⟩ := ECsplitsBandD
    have PinBDintEC : P ∈ line B D ∩ EC := ⟨(Line.seg_sub_line PonSegBD), PonEC⟩
    have LeqBD : cL = line B D := LeqAB ▸ Line.equiv BneD
      ⟨LeqAB ▸ BonAB, Line.line_has_definition_points.left, LeqAB ▸ DonAB, Line.line_has_definition_points.right⟩
    rw [LeqBD] at LintECatC
    rw [LintECatC] at PinBDintEC
    have PeqC : P = C := by tauto
    rw [<- PeqC]
    rcases PonSegBD with BPD | BeqP | DeqP
    · exact BPD
    · rw [BeqP, <- PeqC] at BneC; contradiction
    · rw [DeqP, <- PeqC] at CneD; contradiction

/- Ed: I've taken a more 'proof programmer' approach below, extracting out a much terser argument and relying on 
lemmas elsewhere to reduce duplication. The following are _not_ the argument that the author makes directly, but
a version of it optimized for tersity in the context of Lean. I think it reads alright, but it atomizes the
intuitive argument that the author makes into a bunch of type theoretic dust, which isn't my favorite thing in the
world. -/

/-- p.113 A similar argument involving EB proves that A - B - D (Ex 2(b)) -/
theorem P3.right : (A - B - C) ∧ (A - C - D) -> A - B - D := by
  intro ⟨ABC, ACD⟩
  have distinctABCD := Ex1.a ⟨ABC, ACD⟩
  separate at distinctABCD
  have cL := Ex1.b ⟨ABC, ACD⟩
  have ⟨E, EoffcL⟩ := Ch2.Prop.P3 cL
  let EB := line E B
  have ⟨LneEB, LnparEB, LintEBatB⟩ := Intersection.auxillary_line_through (cL.mem B) EoffcL
  have AoffEB := (Intersection.miss_means_off AneB LintEBatB).resolve_left (not_not.mpr (cL.mem A))
  have CoffEB := (Intersection.miss_means_off BneC.symm LintEBatB).resolve_left (not_not.mpr (cL.mem C))
  have DoffEB := (Intersection.miss_means_off BneD.symm LintEBatB).resolve_left (not_not.mpr (cL.mem D))
  have EBsplitsAC := Intersection.splits_points ABC (Intersection.symm.mpr LintEBatB)
  have BCD := P3.left ⟨ABC, ACD⟩
  have notCBD : ¬(C - B - D) := fun CBD => Betweenness.absurdity_abc_bac ⟨BCD, CBD⟩
  have EBguardsCD := Intersection.guards_when_not_between BneC.symm BneD.symm LintEBatB ⟨cL.mem C, cL.mem D⟩ notCBD
  have EBsplitsAD := B4iii ⟨AoffEB, CoffEB, DoffEB⟩ ⟨EBsplitsAC, EBguardsCD⟩
  exact Intersection.between_splits AneB BneD.symm LintEBatB ⟨cL.mem A, cL.mem D⟩ EBsplitsAD

/-- p.113, Corollary, Given A-B-C and B-C-D, then A-B-D... -/
lemma P3.corollary.left : (A - B - C) ∧ (B - C - D) -> A - B - D := by
  intro ⟨ABC, BCD⟩
  have distinctABCD := Ex1.a' ⟨ABC, BCD⟩
  separate at distinctABCD
  have cL := Ex1.b' ⟨ABC, BCD⟩
  have ⟨E, EoffcL⟩ := Ch2.Prop.P3 cL
  let EB := line E B
  have ⟨LneEB, LnparEB, LintEBatB⟩ := Intersection.auxillary_line_through (cL.mem B) EoffcL
  have AoffEB := (Intersection.miss_means_off AneB LintEBatB).resolve_left (not_not.mpr (cL.mem A))
  have CoffEB := (Intersection.miss_means_off BneC.symm LintEBatB).resolve_left (not_not.mpr (cL.mem C))
  have DoffEB := (Intersection.miss_means_off BneD.symm LintEBatB).resolve_left (not_not.mpr (cL.mem D))
  have EBsplitsAC := Intersection.splits_points ABC (Intersection.symm.mpr LintEBatB)
  have notCBD : ¬(C - B - D) := fun CBD => Betweenness.absurdity_abc_bac ⟨BCD, CBD⟩
  have EBguardsCD := Intersection.guards_when_not_between BneC.symm BneD.symm LintEBatB ⟨cL.mem C, cL.mem D⟩ notCBD
  have EBsplitsAD := B4iii ⟨AoffEB, CoffEB, DoffEB⟩ ⟨EBsplitsAC, EBguardsCD⟩
  exact Intersection.between_splits AneB BneD.symm LintEBatB ⟨cL.mem A, cL.mem D⟩ EBsplitsAD

/-- p.113 and A-C-D -/
lemma P3.corollary.right : (A - B - C) ∧ (B - C - D) -> A - C - D := by
  intro ⟨ABC, BCD⟩
  have ABD := P3.corollary.left ⟨ABC, BCD⟩
  exact B1b.mp (P3.right ⟨B1b.mp BCD, B1b.mp ABD⟩)


/-

Let me take you through what school was like in more detail.

For the first few years, from third up through seventh grade (I 'skipped' sixth, because it was cheaper
to have some hand-me-down school materials from the Pastor's family, as I recall), I did school alone in
what would eventually be my sister's downstairs bedroom. I would sit and stare at a wall for a few hours,
write some answers on a sheet that I knew wouldn't be checked by anyone, and 'finish' around four or five.

For the first few weeks, Mom sat at a big desk we got from an office auction or something, playing teacher,
but never really doing any teaching. I remember asking her a question about my math homework once, she told
me the answer was probably in my book and I should read it. So I did.

Later, when I started seventh grade, is we transitioned to the 'Video Learning Academy' -- I actually don't
remember the _official_ name, but I think that's what it was. In any case, this was a system where you'd be
sent these pre-recorded videos with lectures, the 'teachers' -- and some of them legitmately did do some teaching
-- would occasionally pause and 'ask the students at home' for an answer before returning to the classroom
for the same.

This is when the supervision really became a formality. For a while it was 'check in every day', then it was
'check in occasionally, when the thought occurred to Mom' to 'you are responsible for your own education' and
'we expect you to do this' -- coupled with the classic "Honor thy father and mother" canard that a certain
class of evangelicals like to break out whenever they do something shitty and want to make it the kid's fault.

-/

end Geometry.Ch3.Prop
