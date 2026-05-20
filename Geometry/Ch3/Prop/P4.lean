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
import Atlas

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas  -- enables `atlas commentary := by …` field keywords (scoped)

atlas commentary := by
  ref proposition 3.4
  page 113
  name "Line Separation Property"
  aliases [
    Geometry.Theory.Line.separation
  ]
  preface "If C - A - B and l is the line through A, B, and C (Betweenness Axiom 1), then for every point P lying on l, P lies either on ray A B or on the opposite ray A C."

atlas proposition 3.4 "Line separation by an interior point: points on the line lie on one of two opposite rays"
  {A B C P : Point} (CAB : C - A - B) (PonL : P on (line A B)) : P on ray A B ∨ P on ray A C := by
  comment "Some mise en place"
  clearly A ≠ P; clearly B ≠ P; clearly C ≠ P
  have distinctABCP : distinct A B C P := by
    have dABC : distinct A B C := (ref lemma 1.0.39 CAB).of_eq obvious
    separate
    distinguish
    repeat assumption
  have AneB : A ≠ B := by distinguish
  have colABCP : collinear A B C P := by
    have cABC : collinear A B C := (ref lemma 1.0.40 CAB).of_eq obvious
    have ABisSameLine : line A B = cABC.line := ref lemma 2.0.2 AneB
      ⟨ref lemma 1.0.23, cABC.mem A, ref lemma 1.0.24, cABC.mem B⟩
    rw [ABisSameLine] at PonL
    exact (Collinear.insert cABC PonL).of_eq obvious
  comment "Expose the pairwise inequalities for the `forgetting` casts below."
  separate at distinctABCP
  quoting (1) "Either P lies on ray A B or it does not (Law of the Excluded Middle)"
  rcases Classical.em (P on ray A B) with PonRayAB | PoffRayAB
  · quoting (2) "If P does lie on ray A B, we are done" ...
    left; trivial
  · quoting ... "so assume it doesn't; then P - A - B (Betweenness Axiom 3)"
    have PAB : P - A - B := by
      have h := ref axiom B.3 P A B ⟨distinctABCP forgetting C, colABCP forgetting C⟩
      rcases h with ⟨PAB,_,_⟩ | ⟨_,APB,_⟩ | ⟨_, _, ABP⟩
      · exact PAB
      · have PonSegAB : P on segment A B := obvious
        apply ref lemma 2.0.4 at PonSegAB
        contradiction
      · have PonRayAB : P on ray A B := obvious
        contradiction
    quoting (3) "If P = C" ...
    rcases Classical.em (P = C) with PeqC | PneC
    · quoting ... "then P lies on ray A C (by definition)" ...
      obvious
    · quoting ... "so assume P ≠ C; then exactly one of the relations C-A-P, C-P-A, or P-C-A holds (Betweeness Axiom 3 again)."
      have hCAP := ref axiom B.3 C A P ⟨distinctABCP forgetting B, colABCP forgetting B⟩
      quoting (4) "Suppose the relation C-A-P holds (RAA Hypothesis)"
      rcases Classical.em (C - A - P) with CAP | nCAP
      · quoting (5) "We know (by Betweenness Axiom 3) that exactly one of the relations P-C-B, C-P-B, or C-B-P holds."
        have hPBC := ref axiom B.3 P B C ⟨distinctABCP forgetting A, colABCP forgetting A⟩
        rcases hPBC with ⟨PBC,_,_⟩ | ⟨_,BPC,_⟩ | ⟨_, _, PCB⟩
        · quoting (6) "If P-B-C, then combining this with P-A-B (step 2) gives A-B-C (Proposition 3.3), contradiction the
              hypothesis."
          exfalso
          exact ref lemma 1.0.38 ⟨via proposition 3.3.i ⟨PAB, PBC⟩, CAB⟩
        · quoting (7) "If C-P-B, then combining this with C-A-P (step 4) gives A-P-B (Proposition 3.3), contradiction step 2."
          exfalso
          exact ref lemma 1.0.36 ⟨via proposition 3.3.i ⟨CAP, (BPC.symm)⟩, PAB⟩
        · quoting (8) "If B-C-P, then combining this with B-A-C (hypothesis and Betweenness Axiom 1) gives A-C-P (Proposition 3.3),
             contradicting step 4."
          exfalso
          exact ref lemma 1.0.36 ⟨via proposition 3.3.i ⟨CAB.symm, PCB.symm⟩, CAP⟩
      · quoting (9) "Since we obtain a contradiction in all three cases, C-A-P does not hold (RAA conclusion)."
        comment "this is covered by the above .em elimination"
        quoting (10) "Therefore, C-P-A or P-C-A (step 3), which means that P lies on the opposite ray A C. ∎"
        rcases hCAP with ⟨CAP,_,_⟩ | ⟨_,ACP,_⟩ | ⟨_,_,CPA⟩
        · comment "covered above"
          contradiction
        · have PonRayAC : P on ray A C := by obvious
          right; trivial
        · have PonSegAB : P on segment A C := by obvious
          apply ref lemma 2.0.4 at PonSegAB
          right; trivial


/-
-- IDK if we can structure this like a bunch of tactic invocations that just build a bunch of data on a structe that
-- gets associated with the next theorem, but if we have to like, duplicate some names around that's fine with me. I
-- just include the kind/number here, but ostentibly we could have any number of names here pretty comfortably, and then
-- the main atlas macro drops the frenchquoted name (which lives here instead?)
atlas commentary := by
  ref proposition 3.4
  page 131
  name "Line separation property"
  -- These would expand into aliases of the main result, solving our third-name problem. Maybe nice if this supported
  -- `ref` aliasing too, so we could have `ref property 3.4` here as well. Not critical
  aliases [
    Line.separation
    -- ...
  ]
  -- alternative, `pages 109..113`
  preface """
  If C - A - B and l is the line through A, B, and C (Betweenness Axiom 1), then for every point P lying on l,
  P lies either on ray A B or on the opposite ray A C.

  arbitrary multiline text, eventually we might even highlight this w/ treesitter or something.
  """
  notes """

  prefacing editorial notes

  arbitrary multiline text, eventually we might even highlight this w/ treesitter or something.
  """
  tags ["some", "arbitrary", "tags"]


-- I'd still want the statement separated like this, but moving the french quot
atlas proposition 3.4
  {A B C P : Point} (CAB : C - A - B) (PonL : P on (line A B)) : P on ray A B ∨ P on ray A C := by
  comment "Some mise en place"
  clearly A ≠ P; clearly B ≠ P; clearly C ≠ P
  have distinctABCP : distinct A B C P := by
    have dABC : distinct A B C := (ref lemma 1.0.39 CAB).of_eq obvious
    separate
    distinguish
    repeat assumption
  have AneB : A ≠ B := by distinguish
  have colABCP : collinear A B C P := by
    have cABC : collinear A B C := (ref lemma 1.0.40 CAB).of_eq obvious
    have ABisSameLine : line A B = cABC.line := ref lemma 2.0.2 AneB
      ⟨ref lemma 1.0.23, cABC.mem A, ref lemma 1.0.24, cABC.mem B⟩
    rw [ABisSameLine] at PonL
    exact (Collinear.insert cABC PonL).of_eq obvious
  comment "Expose the pairwise inequalities for the `forgetting` casts below."
  separate at distinctABCP
  quoting (1) "Either P lies on ray A B or it does not (Law of the Excluded Middle)"
  rcases Classical.em (P on ray A B) with PonRayAB | PoffRayAB
  · quoting (2) "If P does lie on ray A B, we are done" ...
    left; trivial
  · quoting ... "so assume it doesn't; then P - A - B (Betweenness Axiom 3)"
    have PAB : P - A - B := by
      have h := ref axiom B.3 P A B ⟨distinctABCP forgetting C, colABCP forgetting C⟩
      rcases h with ⟨PAB,_,_⟩ | ⟨_,APB,_⟩ | ⟨_, _, ABP⟩
      · exact PAB
      · have PonSegAB : P on segment A B := obvious
        apply ref lemma 2.0.4 at PonSegAB
        contradiction
      · have PonRayAB : P on ray A B := obvious
        contradiction
    quoting (3) "If P = C" ...
    rcases Classical.em (P = C) with PeqC | PneC
    · quoting ... "then P lies on ray A C (by definition)" ...
      obvious
    · quoting ... """
      so assume P ≠ C; then exactly one of the relations C-A-P, C-P-A, or P-C-A holds (Betweeness Axiom 3 again).
      """
      have hCAP := ref axiom B.3 C A P ⟨distinctABCP forgetting B, colABCP forgetting B⟩
      quoting (4) "Suppose the relation C-A-P holds (RAA Hypothesis)"
      rcases Classical.em (C - A - P) with CAP | nCAP
      · quoting (5) "We know (by Betweenness Axiom 3) that exactly one of the relations P-C-B, C-P-B, or C-B-P holds."
        have hPBC := ref axiom B.3 P B C ⟨distinctABCP forgetting A, colABCP forgetting A⟩
        rcases hPBC with ⟨PBC,_,_⟩ | ⟨_,BPC,_⟩ | ⟨_, _, PCB⟩
        · quoting (6) """
          If P-B-C, then combining this with P-A-B (step 2) gives A-B-C (Proposition 3.3), contradiction the hypothesis.
          """
          exfalso
          exact ref lemma 1.0.38 ⟨via proposition 3.3.i ⟨PAB, PBC⟩, CAB⟩
        · quoting (7) """
          If C-P-B, then combining this with C-A-P (step 4) gives A-P-B (Proposition 3.3), contradiction step 2.
          """
          exfalso
          exact ref lemma 1.0.36 ⟨via proposition 3.3.i ⟨CAP, (BPC.symm)⟩, PAB⟩
        · quoting (8) """
          If B-C-P, then combining this with B-A-C (hypothesis and Betweenness Axiom 1) gives A-C-P (Proposition 3.3),
          contradicting step 4.
          """
          exfalso
          exact ref lemma 1.0.36 ⟨via proposition 3.3.i ⟨CAB.symm, PCB.symm⟩, CAP⟩
      · quoting (9) "Since we obtain a contradiction in all three cases, C-A-P does not hold (RAA conclusion)."
        comment Ed. this is covered by the above .em elimination
        quoting (10) "Therefore, C-P-A or P-C-A (step 3), which means that P lies on the opposite ray A C." ...
        rcases hCAP with ⟨CAP,_,_⟩ | ⟨_,ACP,_⟩ | ⟨_,_,CPA⟩
        · contradiction; comment "covered above"
        · have PonRayAC : P on ray A C := by obvious
          right; trivial
        · have PonSegAB : P on segment A C := by obvious
          apply ref lemma 2.0.4 at PonSegAB
          right; trivial
        quoting ... "∎"
-/

end Geometry.Ch3.Prop


namespace Line

-- P3.4 ("line separation property") was previously aliased into the Line
-- namespace; reference it as `proposition 3.4` (or via the title) instead.

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
