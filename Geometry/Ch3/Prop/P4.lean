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
import Geometry.Ch3.Ex.Ex1
import Geometry.Theory.Distinct
import Geometry.Theory.Collinear.Ch1
import Geometry.Theory.Collinear.Ch2
import Geometry.Theory.Betweenness.Ch1
import Geometry.Theory.Betweenness.Ch2
import Geometry.Theory.Line.Ch1
import Geometry.Theory.Line.Ch2
import Geometry.Theory.Forgetting
import Geometry.Theory.Arranged

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
  have distinctABCP : distinct A B C P := by
    have dABC : distinct A B C := ((Betweenness.abc_imp_distinct CAB) arranged A B C)
    separate; distinguish
    
     
    sorry
  have AneB : A ≠ B := by distinguish
  have colABCP : collinear A B C P := by
    have cABC : collinear A B C := (Betweenness.abc_imp_collinear CAB) arranged A B C
    have ABisSameLine : line A B = cABC.line := Line.equiv AneB
      ⟨Line.line_has_definition_points.left, cABC.mem A, Line.line_has_definition_points.right, cABC.mem B⟩
    rw [ABisSameLine] at PonL
    have cABCP : collinear A B C P := by extending
    exact cABCP
    sorry
  /- (1) Either P lies on ray A B or it does not (Law of the Excluded Middle) -/
  rcases Classical.em (P on ray A B) with PonRayAB | PoffRayAB
  · /- (2) If P does lie on ray A B, we are done... -/
    left; trivial
  · /- ... so assume it doesn't; then P - A - B (Betweenness Axiom 3) -/
    have PAB : P - A - B := by
      have h := B3 P A B ⟨distinctABCP forgetting C arranged P A B, colABCP forgetting C arranged P A B⟩
      rcases h with ⟨PAB,_,_⟩ | ⟨_,APB,_⟩ | ⟨_, _, ABP⟩
      · exact PAB
      · have PonSegAB : P on segment A B := obvious
        apply Line.seg_sub_ray at PonSegAB
        contradiction
      · have PonRayAB : P on ray A B := obvious
        contradiction
    /- (3) If P = C ... -/
    rcases Classical.em (P = C) with PeqC | PneC
    · /- ... then P lies on ray A C (by definition) -/
      obvious
    · /- so assume P ≠ C; then exactly one of the relations C-A-P, C-P-A, or P-C-A holds (Betweeness Axiom 3 again). -/
      have hCAP := B3 C A P ⟨distinctABCP forgetting B arranged C A P, colABCP forgetting B arranged C A P⟩
      /- (4) Suppose the relation C-A-P holds (RAA Hypothesis) -/
      rcases Classical.em (C - A - P) with CAP | nCAP
      · /- (5) We know (by Betweenness Axiom 3) that exactly one of the relations P-C-B, C-P-B, or C-B-P holds. -/
        have hPBC := B3 P B C ⟨distinctABCP forgetting A arranged P B C, colABCP forgetting A arranged P B C⟩
        rcases hPBC with ⟨PBC,_,_⟩ | ⟨_,BPC,_⟩ | ⟨_, _, PCB⟩
        · /- (6) If P-B-C, then combining this with P-A-B (step 2) gives A-B-C (Proposition 3.3), contradiction the
              hypothesis. -/
          exfalso
          exact Betweenness.absurdity_abc_cab ⟨P3.left ⟨PAB, PBC⟩, CAB⟩
        · /- (7) If C-P-B, then combining this with C-A-P (step 4) gives A-P-B (Proposition 3.3), contradiction step 2. -/
          exfalso
          exact Betweenness.absurdity_abc_bac ⟨P3.left ⟨CAP, (B1b.mp BPC)⟩, PAB⟩
        · /- (8) If B-C-P, then combining this with B-A-C (hypothesis and Betweenness Axiom 1) gives A-C-P (Proposition 3.3),
             contradicting step 4. -/
          exfalso
          exact Betweenness.absurdity_abc_bac ⟨P3.left ⟨PCB, CAB⟩, CAP⟩
      · /- (9) Since we obtain a contradiction in all three cases, C-A-P does not hold (RAA conclusion). -/
        -- Ed. this is covered by the above .em elimination
        /- (10) Therefore, C-P-A or P-C-A (step 3), which means that P lies on the opposite ray A C. ∎ -/
        rcases hCAP with ⟨CAP,_,_⟩ | ⟨_,ACP,_⟩ | ⟨_,_,CPA⟩
        · contradiction -- covered above
        · have PonRayAC : P on ray A C := by
            obvious
            exact eq_or_ne C P
          right; trivial
        · have PonSegAB : P on segment A C := by obvious
          apply Line.seg_sub_ray at PonSegAB
          right; trivial

end Geometry.Ch3.Prop


namespace Line

/-- P3.4 has a specific name, the line separation property, and so we alias it into the Line namespace for
 clarity later -/
alias separation := Geometry.Ch3.Prop.P4

end Line

/-

When you are left to your own devices, and you're clever and interested in creative abuse of the rules, you rapidly find
all sorts of creative ways to avoid the boring stuff and just do what you want. In my case, plopping a bored kid with
some sort of undiagnosed neuroatypicality was a great way to find new ways to not do schoolwork and instead watch
M*A*S*H or stand up comedy or whatever else sated my curiosity. Ultimately Cable TV from the late '90s and early '00s
provided more of my education than did the VLA. I still reflexivly quote the Franscisco Pablo special where he does an
impression of an Arnold Schwarzenegger movie trailer.

... in a world...

Anyway.

The whole process worked fine, I did my homework (since it was easy anyway), I made sure the videos needed to be
rewound, I made sure the forms filled in, I made sure it _looked_ like I was being educated by the propagandists
on the old CRT; but the majority of teaching came from Alan Alda and whoever was on Comedy Central. I read subtitles
more than textbooks, lips more than subtitles, and spent most of middle school shirking homework in favor of whichever
rerun of Star Trek was on at 11AM on any given tuesday.

-/
