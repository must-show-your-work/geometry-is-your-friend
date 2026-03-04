
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
import Geometry.Theory.Collinear.Ch1
import Geometry.Theory.Collinear.Ch2
import Geometry.Theory.Betweenness.Ch1
import Geometry.Theory.Betweenness.Ch2
import Geometry.Theory.Line.Ch1
import Geometry.Theory.Line.Ch2

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex

lemma Intersection.miss_means_off {L M : Line} {A X : Point} : A ≠ X -> (L intersects M at X) -> (A off L) ∨ (A off M) := by
  intro AneX LintMatX
  by_contra! AonLandM
  have AinInt : A ∈ L ∩ M := AonLandM
  rw [LintMatX] at AinInt
  tauto

/-- If A - X - B, and L intersects a segment A B at X, then L splits A and B -/
lemma Intersection.splits_points {L : Line} {A X B : Point} (AXB : A - X - B) :
  (L intersects M at X) -> (L splits A and B) := by
  intro LintAXBatX
  unfold SameSide
  push_neg
  intro AoffL BoffL
  have distinctAXB := Betweenness.abc_imp_distinct AXB
  distinguish
  use X
  constructor
  · unfold Segment; simp only [mem_setOf_eq]; left; exact AXB
  · exact Intersection.inter_touch_left LintAXBatX


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
     (RAA Hypothesis) -/
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
  /- A similar argument involving EB proves that A - B - D -/
  

  /- TODO: Ed: time to break out `suffices` or some other clever thing... -/


theorem P3.right : (A - B - C) ∧ (A - C - D) -> A - B - D := by
  /- (1) A, B, C, and D are distinct, collinear points (see Exercise 1). -/
  intro ⟨ABC, ACD⟩
  have distinctABCD := Ex1.a ⟨ABC, ACD⟩
  separate at distinctABCD
  have cL := Ex1.b ⟨ABC, ACD⟩
  /- (2) There exists a point E not on the line through A,B,C,D (Proposition 2.3) -/
  have LeqAB : cL = line A B := Line.equiv AneB
    ⟨cL.mem A, Line.line_has_definition_points.left, cL.mem B, Line.line_has_definition_points.right⟩
  have ⟨E, EoffcL⟩ := Ch2.Prop.P3 cL
  /- (3) Consider line EB. Since (by hypothesis) AD meets this line in point B,... -/
  let EB := line E B
  -- {Ed} Missing these simple conditions
  -- NOTE: have to be specific here to avoid coercion issues.
  have BonAB : B on cL.line := cL.mem B
  have DonAB : D on cL.line := cL.mem D
  -- TODO: I need better tools for proving lines different from each other
  have LneEB : cL ≠ EB := by
    have EonEB : E on EB := Line.line_has_definition_points.left
    by_contra! hNeg; rw [hNeg] at EoffcL; contradiction
  have BonEB : B on EB := Line.line_has_definition_points.right
  have BonLintEB : B on cL ∩ EB := ⟨cL.mem B, BonEB⟩
  have LnparEB : cL ∦ EB := by
    by_contra! hNeg
    have emptyInter := Intersection.parallel_intersection_is_empty cL EB LneEB hNeg
    rw [emptyInter] at BonLintEB
    contradiction
  have LintEBatB : cL intersects EB at B := (Intersection.single_point_of_intersection B cL EB ⟨LneEB, LnparEB⟩).mp BonLintEB
  have AoffEB : A off EB := (Intersection.miss_means_off AneB LintEBatB).resolve_left (not_not.mpr (cL.mem A))
  have CoffEB : C off EB := (Intersection.miss_means_off BneC.symm LintEBatB).resolve_left (not_not.mpr (cL.mem C))
  have DoffEB : D off EB := (Intersection.miss_means_off BneD.symm LintEBatB).resolve_left (not_not.mpr (cL.mem D))
  -- {/Ed}
  /- ... points A and D are on opposite sides of EB -/
  have EBsplitsAandC : EB splits A and C := Intersection.splits_points ABC (Intersection.symm.mpr LintEBatB)
  /- (4) We claim A and B are on the same side of EB. Assume on the contrary that A and B are on opposite sides of EB
     (RAA Hypothesis) -/
  by_cases raa : EB splits A and B
  · /- p113. (5) Then EB meets AB in a point between A and B (definition of "opposite sides" [ed. "splits" in our parlance]). -/
    have ⟨X, LintEBatX, Xuniq⟩ : ∃! X : Point, (cL intersects EB at X) := by
      rcases Line.line_trichotomy cL EB with LparEB | LintEBatX | LeqEB
      · exfalso; rwa [LparEB] at BonLintEB
      · exact LintEBatX
      · exfalso; rw [<- LeqEB] at AoffEB; contradiction
    -- {Ed} need this for a step below
    have ⟨XonL, XonEB⟩ := Intersection.inter_touch LintEBatX
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
      have AneX : A ≠ X := by by_contra! hNeg; rw [hNeg] at AoffEB; contradiction
      have BneX : C ≠ X := by by_contra! hNeg; rw [hNeg] at CoffEB; contradiction
      have distinctAXB : distinct A X B := by separate; sorry
      rcases B3 A X B ⟨distinctAXB, colAXB⟩ with ⟨AXB, _⟩ | reject
      · exact AXB
      · have EBguardsCD : EB guards C and D := by
          sorry
        sorry
    -- FIXME:  proof gets a little lost here.
    sorry
  · push_neg at raa
    sorry -- FIXME: same as above
  

end Geometry.Ch3.Prop
