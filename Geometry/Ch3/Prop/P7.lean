import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Interpendices.A
import Geometry.Theory.Interpendices.B
import Geometry.Theory.Arrangement
import Geometry.Theory.Forgetting
import Geometry.Theory.Distinct
import Geometry.Theory.Collinear
import Geometry.Theory.Angle

import Geometry.Tactics

import Geometry.Construction.AtlasField

import Geometry.Ch3.Prop.P6

import Atlas

namespace Geometry.Ch3.Prop


open Set
open Geometry.Theory
open Geometry.Ch3.Prop
open Atlas

-- p115, 'Given an angle ∠ CAB, define a point D to be in the interior of ∠CAB if D is on the same side of AC as B and
-- if D is also on the same side of AB as C. (Thus, the interior of an angle is the intersection of two half-planes.)
-- See Figure 3.11.'
def InteriorOf (B A C D : Point) :=
  ∠ B A C ∧ (ray A C guards B and D) ∧ (ray A B guards C and D)

syntax (name := isInteriorToAngleNotation)
  ident "is" "interior" "to" "∠" ident ident ident : term

macro_rules (kind := isInteriorToAngleNotation)
  | `($D:ident is interior to ∠ $X:ident $V:ident $Z:ident) =>
      `(InteriorOf $X $V $Z $D)

atlas commentary := by
  via proposition 3.7
  page 115
  name "Given an angle ∠CAB and point D lying on line BC. Then D is in the interior of ∠CAB if and only if B-D-C (see
  figure 3.12"
  preface ""

  figure := by
    construction { infer }
    title "Proposition 3.7"

atlas proposition 3.7 "D on line BC is interior to ∠CAB iff B-D-C"
  { A B C D : Point } (DonBC : D on line B C) (aCAB : ∠ C A B := by assumption) (DonBC : D on line B C := by assumption) :
    D is interior to ∠ B A C ↔ B-D-C := by
    have cBCD : collinear B C D := by
      use line B C
      intro P PisBCD; by_exhaustion PisBCD
      all_goals obvious
    obtain ⟨rABnerAC, _⟩ := aCAB
    constructor
    · intro DintCAB
      obtain ⟨aBAC, ACguardsBD, ABguardsCD⟩ := DintCAB
      obtain ⟨BoffAC, DoffAC, guardConditionBD⟩ := ACguardsBD
      obtain ⟨CoffAB, DoffAB, guardConditionCD⟩ := ABguardsCD
      rcases guardConditionBD with rfl | h
      · obvious
      · rcases guardConditionCD with rfl | j
        · exfalso; exact absurd DoffAC obvious
        · clearly B ≠ D
          clearly C ≠ D
          have : distinct B C D := by
            separate; obvious
          rcases (via axiom B.3 B C D ⟨this, cBCD⟩) with ⟨BCD, _, _⟩ | ⟨_,CBD,_⟩ | ⟨_, _, BDC⟩
          · exfalso
            idea "violates the guard condition"
            sorry
          · exfalso
            idea "ibid"
            sorry
          · exact BDC
    · intro BDC
      idea "construct rays DB and DC and use 3.6"
      have ⟨h, j⟩ := via proposition 3.6 BDC
      constructor
      · constructor
        · exact rABnerAC.symm
        · by_contra!; obtain ⟨_, BAeqBC⟩ := this
          -- rw [<- BAeqBC] at DonBC -- why doesn't this work?
          sorry
      · suffices key : ∀ {B C : Point}, B - D - C → (ray A C guards B and D) by
          exact ⟨key BDC, key BDC.symm⟩
        intro B C BDC
        sorry


end Geometry.Ch3.Prop
