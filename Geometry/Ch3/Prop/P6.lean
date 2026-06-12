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

  figure := by
    title "Proposition 3.6"
    construction {
      infer
    }

atlas proposition 3.6 "If A - B - C, then B cuts line AC into two parts"
  { A B C : Point } (ABC : A - B - C := by assumption) :
  ((ray B A) intersects (ray B C) at B) ∧ ((ray A B : Set Point) = (ray A C)) := by
  have dABC : distinct A B C := obvious
  constructor
  · apply Line.eq_of_subset
    · intro P ⟨PinBA, PinBC⟩
      fixme "This is _misery_, some kind of table-based approach is what's needed, 'here are all the cases in a matrix,
fill them in' kind of thing"
      rcases PinBA with PinSegBA | PinExtBA
      · rcases PinBC with PinSegBC | PinExtBC
        · rcases PinSegBA with BPA | rfl | rfl
          · exfalso
            rcases PinSegBC with BPC | rfl | rfl
            · idea "this essentially argues that the points are arranged A - P - B - P - C; which is absurd"
              exact via lemma 1.0.19 ⟨BPA.symm, by organize! ABC BPC⟩
            · exact via lemma 1.0.18 ⟨BPA, BPA⟩
            · exact via lemma 1.0.20 ⟨BPA, ABC⟩
          · obvious
          · exfalso
            rcases PinSegBC with BPC | rfl | rfl
            · exact via lemma 1.0.20 ⟨ABC, BPC.symm⟩
            all_goals separate at dABC; contradiction
        obtain ⟨BCP, PneB, PneC⟩ := PinExtBC
        · rcases PinSegBA with BPA | rfl | rfl
          · exfalso; exact via lemma 1.0.19 ⟨by organize! BPA.symm ABC, BCP.symm⟩
          · obvious
          · exfalso; exact via lemma 1.0.19 ⟨ABC, BCP.symm⟩
      · obtain ⟨BAP, PneB, PneA⟩ := PinExtBA
        rcases PinBC with PinSegBC | PinExtBC
        · rcases PinSegBC with BPC | rfl | rfl
          · exfalso; exact via lemma 1.0.20 ⟨by organize! ABC BAP.symm, BPC.symm⟩
          · obvious
          · exfalso; exact via lemma 1.0.18 ⟨BAP, ABC⟩
        · exfalso
          obtain ⟨BCP, PneB, PneC⟩ := PinExtBC
          exact via lemma 1.0.19 ⟨by organize! BAP.symm ABC, BCP.symm⟩
    · intro P PisB
      obvious
  · apply Subset.antisymm
    · intro P PinAB
      rcases PinAB with (APB | rfl | rfl) | ⟨ABP, AneP, BneP⟩
      · comment "I regard applications of 3.3 and its friends as obvious via this `organize!` tactic; so does the author after this theorem, more or less"
        have : P on ray A C := by
          organize! APB ABC
          have : A - P - C := obvious; obvious
        exact this
      · obvious
      · obvious
      · clearly P ≠ C
        rcases (by organize! ABP ABC PneC) with ABPC | ABCP
        · have : A - P - C := by arrangement ABPC
          obvious
        · have : A - C - P := by arrangement ABCP
          obvious
    · intro P PinAC
      rcases PinAC with PinSegAC | PinExtAC
      · rcases PinSegAC with APC | rfl | rfl
        · clearly P ≠ B
          rcases (by organize! APC ABC PneB) with ABPC | APBC
          · have : A - B - P := by arrangement ABPC
            obvious
          · have : A - P - B := by arrangement APBC
            obvious
        all_goals obvious
      · obtain ⟨ACP, PneA, PneC⟩ := PinExtAC
        have : A - B - C - P := obvious
        have : A - B - P := by arrangement this
        obvious

end Geometry.Ch3.Prop
