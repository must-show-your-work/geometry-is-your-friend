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
      rcases PinBA with PinSegBA | PinExtBA
      · rcases PinBC with PinSegBC | PinExtBC
        · rcases PinSegBA with BPA | rfl | rfl
          · exfalso
            rcases PinSegBC with BPC | rfl | rfl
            · idea "this essentially argues that the points are arranged A - P - B - P - C; which is absurd"
              have a1 : A - B - P - C := by sorry -- should be obvious
              have a2 : A - P - B - C := by sorry -- should be obvious
              have ABP : A - B - P := by arrangement a1
              exact via lemma 1.0.19 ⟨BPA.symm, ABP⟩
            · exact via lemma 1.0.18 ⟨BPA, BPA⟩
            · exact via lemma 1.0.20 ⟨BPA, ABC⟩
          · obvious
          · exfalso
            rcases PinSegBC with BPC | rfl | rfl
            · exact via lemma 1.0.20 ⟨ABC, BPC.symm⟩
            all_goals separate at dABC; contradiction
        · sorry
      · rcases PinBC with PinSegBC | PinExtBC
        · sorry
        · sorry
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
      · by_contra! hNeg
        sorry
    · intro P PinAC
      sorry


end Geometry.Ch3.Prop
