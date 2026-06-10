import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Interpendices.B
import Geometry.Theory.Arrangement
import Geometry.Theory.Forgetting

import Geometry.Tactics

import Geometry.Construction.AtlasField
import Atlas

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch3.Prop
open Atlas


atlas commentary := by
  via proposition 3.6
  page 115
  name "Line cuts"
  preface "Given A - B - C. Then B is the only point common to rays BA and BC, and ray AB = ray AC"

  -- FIXME: betweenness renders wrong.
  /- figure := by -/
    /- construction { -/
    /-   exists A B C : Point -/
    /-   assert distinct A B C -/
    /-   assert collinear A B C -/
    /-   assert between A B C -/
    /-   construct rayBA := ray B A -/
    /-   construct rayBC := rab B C -/
    /-   focus B -/
    /- } -/
    /- title "Proposition 3.6" -/
    /- index 1 -/
    /- caption "" -/


atlas proposition 3.6 "If A - B - C, then B cuts line AC into two parts"
  { A B C : Point } (ABC : A - B - C := by assumption) :
  ((ray B A) intersects (ray B C) at B) ∧ ((ray A B : Set Point) = (ray A C)) := by
  have dABC : distinct A B C := obvious
  constructor
  · apply Line.eq_of_subset
    · intro P ⟨PinBA, PinBC⟩
      fixme "This is _misery_, some kind of table-based approach is what's needed, 'here are all the cases in a matrix,
fill them in' kind of thing"
      todo "Additionally, we need something like a 'find all possible valid arrangments under the current assumption for
all collinear points'"
      rcases PinBA with PinSegBA | PinExtBA
      · rcases PinBC with PinSegBC | PinExtBC
        · rcases PinSegBA with BPA | rfl | rfl
          · exfalso
            rcases PinSegBC with BPC | rfl | rfl
            · idea "this essentially argues that the points are arranged A - P - B - P - C; which is absurd"
              fixme "I keep hitting a 'cycle in constraints' which is true, except that's the point, the fact that it
              found the cycle tells me that I can derive false. In particular it's noting precisly the idea above, P < B < P is
              absurd. I think the topoSort needs to detect and return the 'I found a cycle you have archisplosion
              happening' maybe something like an `absurd arrangement` tactic?"
              have : A - B - P - C := by organize ABC BPC
              have : A - B - P := by arrangement this
              exact via lemma 1.0.19 ⟨BPA.symm, this⟩
            · exact via lemma 1.0.18 ⟨BPA, BPA⟩
            · exact via lemma 1.0.20 ⟨BPA, ABC⟩
          · obvious
          · exfalso
            rcases PinSegBC with BPC | rfl | rfl
            · exact via lemma 1.0.20 ⟨ABC, BPC.symm⟩
            all_goals separate at dABC; contradiction
        obtain ⟨BCP, PneB, PneC⟩ := PinExtBC
        · rcases PinSegBA with BPA | rfl | rfl
          · exfalso
            have : A - P - B - C := by organize BPA.symm ABC
            have : P - B - C := by arrangement this
            exact via lemma 1.0.19 ⟨this, BCP.symm⟩
          · obvious
          · exfalso
            exact via lemma 1.0.19 ⟨ABC, BCP.symm⟩
      · obtain ⟨BAP, PneB, PneA⟩ := PinExtBA
        rcases PinBC with PinSegBC | PinExtBC
        · rcases PinSegBC with BPC | rfl | rfl
          · exfalso
            have : P - A - B - C := by organize ABC BAP.symm
            have : P - B - C := by arrangement this
            exact via lemma 1.0.20 ⟨this, BPC.symm⟩
          · obvious
          · exfalso
            exact via lemma 1.0.18 ⟨BAP, ABC⟩
        · exfalso
          obtain ⟨BCP, PneB, PneC⟩ := PinExtBC
          have : P - A - B - C := by organize BAP.symm ABC
          have : P - B - C := by arrangement this
          exact via lemma 1.0.19 ⟨this, BCP.symm⟩
    · intro P PisB
      obvious
  · apply Subset.antisymm
    · intro P PinAB
      rcases PinAB with (APB | rfl | rfl) | ⟨ABP, AneP, BneP⟩
      · comment "I regard applications of 3.3 and its friends as obvious; so does the author after this theorem, more or less"
        have : A - P - B - C := obvious
        have : A - P - C := by arrangement this
        have : P on ray A C := obvious
        exact this
      · obvious
      · obvious
      · have : A - B - C - P ∨ A - B - P - C := by sorry
        rcases this with ABCP | ABPC
        · have : A - C - P := by arrangement ABCP
          obvious
        · have : A - P - C := by arrangement ABPC
          obvious
    · intro P PinAC
      rcases PinAC with PinSegAC | PinExtAC
      · rcases PinSegAC with APC | rfl | rfl
        · have : A - P - B - C ∨  A - B - P - C := by sorry
          rcases this with APBC | ABPC
          · have : A - P - B := by arrangement APBC
            obvious
          · have : A - B - P := by arrangement ABPC
            obvious
        all_goals obvious
      · obtain ⟨ACP, PneA, PneC⟩ := PinExtAC
        have : A - B - C - P := obvious
        have : A - B - P := by arrangement this
        obvious

end Geometry.Ch3.Prop
