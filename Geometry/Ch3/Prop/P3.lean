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
import Atlas

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas


atlas commentary := by
  ref proposition 3.3.i
  page 112
  name "Betweenness from shared outer pair: B-C-D from A-B-C and A-C-D"
  preface "Given A - B - C and A - C - D, then B - C - D and A - B - D (see Figure 3.9)"

atlas proposition 3.3.i "Betweenness from shared outer pair: B-C-D from A-B-C and A-C-D"
  : (A - B - C) ∧ (A - C - D) -> B - C - D := by
  quoting (1) "A, B, C, and D are distinct, collinear points (see Exercise 1)."
  intro ⟨ABC, ACD⟩
  have distinctABCD : distinct A B C D := via exercise 3.1.a ⟨ABC, ACD⟩
  separate at distinctABCD
  have cL : collinear A B C D := via exercise 3.1.b ⟨ABC, ACD⟩
  quoting (2) "There exists a point E not on the line through A,B,C,D (Proposition 2.3)"
  have LeqAB : cL = line A B := ref lemma 2.0.2 AneB
    ⟨cL.mem A, ref lemma 1.0.23, cL.mem B, ref lemma 1.0.24⟩
  have ⟨E, EoffcL⟩ := proposition 2.3 cL
  quoting (3) "Consider line EC. Since (by hypothesis) AD meets this line in point C," ...
  let EC := line E C
  comment "Missing these simple conditions"
  detail "have to be specific here to avoid coercion issues."
  have BonAB : B on cL.line := cL.mem B
  have DonAB : D on cL.line := cL.mem D
  todo "I need better tools for proving lines different from each other"
  have LneEC : cL ≠ EC := by
    have EonEC : E on EC := ref lemma 1.0.23
    by_contra! hNeg; rw [hNeg] at EoffcL; contradiction
  have ConEC : C on EC := ref lemma 1.0.24
  have ConLintEC : C on cL ∩ EC := ⟨cL.mem C, ConEC⟩
  have LnparEC : cL ∦ EC := by
    by_contra! hNeg
    have emptyInter := ref lemma 2.0.19 cL EC LneEC hNeg
    rw [emptyInter] at ConLintEC
    contradiction
  have LintECatC : cL intersects EC at C := (ref lemma 2.0.20 C cL EC ⟨LneEC, LnparEC⟩).mp ConLintEC
  have AoffEC : A off EC := (ref lemma 2.0.26 AneC LintECatC).resolve_left (not_not.mpr (cL.mem A))
  have BoffEC : B off EC := (ref lemma 2.0.26 BneC LintECatC).resolve_left (not_not.mpr (cL.mem B))
  have DoffEC : D off EC := (ref lemma 2.0.26 CneD.symm LintECatC).resolve_left (not_not.mpr (cL.mem D))
  quoting ... "points A and D are on opposite sides of EC"
  todo "[refactor] nested ref-in-ref (\"Demeter violation for proofs\") — `ref lemma
  2.0.25 _ ((ref lemma 1.0.31).mpr _)` chains two atlas refs through a `.mpr`. Lift
  the inner symm-application out into a `have`, or introduce a small adapter lemma."
  have ECsplitsAandD : EC splits A and D := via lemma 2.0.25 ACD ((ref lemma 1.0.31).mpr LintECatC)
  quoting (4) "We claim A and B are on the same side of EC. Assume on the contrary that A and B are on opposite sides of EC
     (RAA Hypothesis)"
  comment "This section is proved without the use of ref lemma 2.0.27, which matches the book closely, but the core
     argument is not extracted, just left to intuition. This is fine for humans, but it means a very long and inscrutable
     proof in Lean, replicated ~4 times over, which sucks. So this matches the book, the other branches of this will use the
     lemma."
  by_cases raa : EC splits A and B
  · page break
    quoting (5) "Then EC meets AB in a point between A and B (definition of \"opposite sides\" [ed. \"splits\" in our parlance])."
    have ⟨X, LintECatX, Xuniq⟩ : ∃! X : Point, (cL intersects EC at X) := by
      rcases ref lemma 2.0.1 cL EC with LparEC | LintECatX | LeqEC
      · exfalso; rwa [LparEC] at ConLintEC
      · exact LintECatX
      · exfalso; rw [<- LeqEC] at AoffEC; contradiction
    comment "need this for a step below"
    have ⟨XonL, XonEC⟩ := ref lemma 1.0.34 LintECatX
    have AXB : A - X - B := by
      have colAXB : collinear A X B := by
        use cL
        intro P PinAXB
        simp only [Finset.mem_insert, Finset.mem_singleton] at PinAXB
        rcases PinAXB with PeqA | PeqX | PeqB
        · rw [PeqA, LeqAB]; exact ref lemma 1.0.23
        · rwa [PeqX]
        · rw [PeqB, LeqAB]; exact ref lemma 1.0.24
      have AneX : A ≠ X := by by_contra! hNeg; rw [hNeg] at AoffEC; contradiction
      have BneX : B ≠ X := by by_contra! hNeg; rw [hNeg] at BoffEC; contradiction
      have distinctAXB : distinct A X B := by
        refine ⟨?_⟩
        rw [Finset.card_insert_of_notMem (by simp [AneX, AneB])]
        rw [Finset.card_insert_of_notMem (by simp [BneX.symm])]
        rfl
      rcases ref axiom B.3 A X B ⟨distinctAXB, colAXB⟩ with ⟨AXB, _⟩ | reject
      · exact AXB
      · have ECguardsAB : EC guards A and B := by
          refine ⟨AoffEC, BoffEC, Or.inr ?_⟩
          by_contra! hNeg
          have ⟨P, PonAB, PonEC⟩ := hNeg
          have PinIntLine : P ∈ EC ∩ (line A B) := Set.inter_subset_inter_right EC ref lemma 2.0.5 ⟨PonEC, PonAB⟩
          have APB : A - P - B := by
            rcases PonAB with APB | AeqP | BeqP
            · exact APB
            · exfalso; rw [<- AeqP] at PonEC; contradiction
            · exfalso; rw [<- BeqP] at PonEC; contradiction
          have PeqX : P = X := ref lemma 2.0.18 cL EC LneEC LnparEC ⟨LeqAB.symm ▸ PinIntLine.symm, ⟨XonL, XonEC⟩⟩
          rcases reject with ⟨_, XAB, _⟩ | ⟨_, _, ABX⟩
          · exact ref lemma 1.0.36 ⟨PeqX.symm ▸ XAB, APB⟩
          · exact ref lemma 1.0.37 ⟨APB, PeqX.symm ▸ ABX⟩
        contradiction
    quoting (6) "That point must be C (Proposition 2.1)"
    have CeqX : C = X := ref lemma 1.0.30 ⟨LintECatC, LintECatX⟩
    quoting (7) "Thus A - B - C and A - C - B, which contradicts Betweenness Axiom 3."
    have ACB : A - C - B := CeqX.symm ▸ AXB
    exfalso; exact ref lemma 1.0.37 ⟨ABC, ACB⟩
  · quoting (8) "Hence, A and B are on the same side of EC (RAA conclusion)"
    push Not at raa
    quoting (9) "B and D are on opposite sides of EC (steps 3 and 8 and the corrolary to Betweenness Axiom 4)."
    have ECsplitsBandD : EC splits B and D := by
      by_contra! ECguardsBandD
      have h := ref axiom ["B.4.i"] ⟨raa, ECguardsBandD⟩
      contradiction
    quoting (10) "Hence, the point C of intersection of lines EC and BD lies between B and D (definition of \"opposite sides\";
       Proposition 2.1, i.e., that the point of intersection is unique)."
    unfold SameSide at ECsplitsBandD
    push Not at ECsplitsBandD
    specialize ECsplitsBandD BoffEC DoffEC
    have ⟨BneD, P, ⟨PonSegBD, PonEC⟩⟩ := ECsplitsBandD
    have PinBDintEC : P ∈ line B D ∩ EC := ⟨(ref lemma 2.0.5 PonSegBD), PonEC⟩
    have LeqBD : cL = line B D := LeqAB ▸ ref lemma 2.0.2 BneD
      ⟨LeqAB ▸ BonAB, ref lemma 1.0.23, LeqAB ▸ DonAB, ref lemma 1.0.24⟩
    rw [LeqBD] at LintECatC
    rw [LintECatC] at PinBDintEC
    have PeqC : P = C := by tauto
    rw [<- PeqC]
    rcases PonSegBD with BPD | BeqP | DeqP
    · exact BPD
    · rw [BeqP, <- PeqC] at BneC; contradiction
    · rw [DeqP, <- PeqC] at CneD; contradiction

atlas commentary := by
  ref proposition 3.3.ii
  page 113
  name "Betweenness from shared outer pair: A-B-D from A-B-C and A-C-D"
  preface "A similar argument involving EB proves that A - B - D (Ex 2(b))"
  notes "I've taken a more 'proof programmer' approach below, extracting out a much terser argument and relying on
lemmas elsewhere to reduce duplication. The following are _not_ the argument that the author makes directly, but
a version of it optimized for tersity in the context of Lean. I think it reads alright, but it atomizes the
intuitive argument that the author makes into a bunch of type theoretic dust, which isn't my favorite thing in the
world."

atlas proposition 3.3.ii "Betweenness from shared outer pair: A-B-D from A-B-C and A-C-D"
  : (A - B - C) ∧ (A - C - D) -> A - B - D := by
  intro ⟨ABC, ACD⟩
  have distinctABCD : distinct A B C D := via exercise 3.1.a ⟨ABC, ACD⟩
  separate at distinctABCD
  have cL : collinear A B C D := via exercise 3.1.b ⟨ABC, ACD⟩
  have ⟨E, EoffcL⟩ := proposition 2.3 cL
  let EB := line E B
  have ⟨LneEB, LnparEB, LintEBatB⟩ := ref lemma 2.0.28 (cL.mem B) EoffcL
  have AoffEB := (ref lemma 2.0.26 AneB LintEBatB).resolve_left (not_not.mpr (cL.mem A))
  have CoffEB := (ref lemma 2.0.26 BneC.symm LintEBatB).resolve_left (not_not.mpr (cL.mem C))
  have DoffEB := (ref lemma 2.0.26 BneD.symm LintEBatB).resolve_left (not_not.mpr (cL.mem D))
  todo "[refactor] same ref-in-ref pattern as `ECsplitsAandD` above."
  have EBsplitsAC := via lemma 2.0.25 ABC ((ref lemma 1.0.31).mpr LintEBatB)
  have BCD : B - C - D := via proposition 3.3.i ⟨ABC, ACD⟩
  have notCBD : ¬(C - B - D) := fun CBD => ref lemma 1.0.36 ⟨BCD, CBD⟩
  have EBguardsCD := ref lemma 2.0.29 BneC.symm BneD.symm LintEBatB ⟨cL.mem C, cL.mem D⟩ notCBD
  have EBsplitsAD := corollary ["B.4.iii"] ⟨EBsplitsAC, EBguardsCD⟩
  exact ref lemma 2.0.27 AneB BneD.symm LintEBatB ⟨cL.mem A, cL.mem D⟩ EBsplitsAD


atlas commentary := by
  ref corollary 3.3.i
  page 113
  name "Corollary: A-B-D from chained betweenness A-B-C and B-C-D"
  preface "Corollary, Given A-B-C and B-C-D, then A-B-D..."

atlas corollary 3.3.i "Corollary: A-B-D from chained betweenness A-B-C and B-C-D"
  : (A - B - C) ∧ (B - C - D) -> A - B - D := by
  intro ⟨ABC, BCD⟩
  have distinctABCD := ref lemma 3.0.3 ⟨ABC, BCD⟩
  separate at distinctABCD
  have cL := ref lemma 3.0.4 ⟨ABC, BCD⟩
  have ⟨E, EoffcL⟩ := proposition 2.3 cL
  let EB := line E B
  have ⟨LneEB, LnparEB, LintEBatB⟩ := ref lemma 2.0.28 (cL.mem B) EoffcL
  have AoffEB := (ref lemma 2.0.26 AneB LintEBatB).resolve_left (not_not.mpr (cL.mem A))
  have CoffEB := (ref lemma 2.0.26 BneC.symm LintEBatB).resolve_left (not_not.mpr (cL.mem C))
  have DoffEB := (ref lemma 2.0.26 BneD.symm LintEBatB).resolve_left (not_not.mpr (cL.mem D))
  todo "[refactor] same ref-in-ref pattern as `ECsplitsAandD` above."
  have EBsplitsAC := via lemma 2.0.25 ABC ((ref lemma 1.0.31).mpr LintEBatB)
  have notCBD : ¬(C - B - D) := fun CBD => ref lemma 1.0.36 ⟨BCD, CBD⟩
  have EBguardsCD := ref lemma 2.0.29 BneC.symm BneD.symm LintEBatB ⟨cL.mem C, cL.mem D⟩ notCBD
  have EBsplitsAD := corollary ["B.4.iii"] ⟨EBsplitsAC, EBguardsCD⟩
  exact ref lemma 2.0.27 AneB BneD.symm LintEBatB ⟨cL.mem A, cL.mem D⟩ EBsplitsAD


atlas commentary := by
  ref corollary 3.3.ii
  page 113
  name "Corollary: A-C-D from chained betweenness A-B-C and B-C-D"
  preface "and A-C-D"

atlas corollary 3.3.ii "Corollary: A-C-D from chained betweenness A-B-C and B-C-D"
  : (A - B - C) ∧ (B - C - D) -> A - C - D := by
  intro ⟨ABC, BCD⟩
  have ABD : A - B - D := via corollary 3.3.i ⟨ABC, BCD⟩
  exact ((via proposition 3.3.ii ⟨BCD.symm, ABD.symm⟩ : D - C - A)).symm



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
