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

-- p115, 'Given an angle ∠ CAB, define a point D to be in the interior of ∠CAB if D is on the same side of line AC as B and
-- if D is also on the same side of line AB as C. (Thus, the interior of an angle is the intersection of two half-planes.)
-- See Figure 3.11.'
def InteriorOf (B A C D : Point) :=
  ∠ B A C ∧ (line A C guards B and D) ∧ (line A B guards C and D)

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

  /- figure := by -/
  /-   construction { -/
  /-     infer -/
  /-     focus A -/
  /-   } -/
  /-   title "Proposition 3.7" -/

atlas proposition 3.7 "D on line BC is interior to ∠CAB iff B-D-C"
  { A B C D : Point } (DonBC : D on line B C) (aCAB : ∠ C A B := by assumption) (DonBC : D on line B C := by assumption) :
    D is interior to ∠ B A C ↔ B-D-C := by
    have cBCD : collinear B C D := by
      use line B C
      intro P PisBCD; by_exhaustion PisBCD
      all_goals obvious
    obtain ⟨dABC, rABnerAC, rABnopprAC⟩ := aCAB
    constructor
    · intro DintCAB
      obtain ⟨aBAC, ACguardsBD, ABguardsCD⟩ := DintCAB
      have ⟨BoffAC, DoffAC, guardConditionBD⟩ := ACguardsBD
      have ⟨CoffAB, DoffAB, guardConditionCD⟩ := ABguardsCD
      clearly A ≠ D := by rw [AeqD] at DoffAB; obvious
      clearly B ≠ D := by rw [BeqD] at DoffAB; obvious
      clearly C ≠ D := by rw [CeqD] at DoffAC; obvious
      have dABCD : distinct A B C D := by
        separate; distinguish; obvious
      rcases guardConditionBD with rfl | h
      · obvious
      · rcases guardConditionCD with rfl | j
        · exfalso; exact absurd DoffAC obvious
        · rcases (via axiom B.3 B C D ⟨dABCD forgetting A, cBCD⟩) with ⟨BCD, _, _⟩ | ⟨_,CBD,_⟩ | ⟨_, _, BDC⟩
          · exfalso; idea "violates the guard condition"
            have CoffBD : C on line B D := obvious
            have : (line A C : Line) ≠ line B D := by intro h; rw [h] at DoffAC; exact DoffAC (by obvious)
            have : (line A C : Line) intersects line B D at C := by
              sorry
            have : line A C splits B and D := via lemma 2.0.22 BCD this
            exact (absurd ACguardsBD) this
          · exfalso; idea "ibid"
            have : B on line C D := obvious
            have : line A B intersects (segment C D : Line) at B := by sorry
            have : line A B splits C and D := via lemma 2.0.22 CBD this
            exact (absurd ABguardsCD) this
          · exact BDC
    · intro BDC
      idea "construct rays DB and DC and use 3.6"
      have ⟨h, j⟩ := via proposition 3.6 BDC
      constructor
      · constructor
        · sorry
        · sorry
      · suffices key : ∀ {B C : Point}, B - D - C → (line A C guards B and D) by
          exact ⟨key BDC, key BDC.symm⟩
        intro B C BDC
        sorry


end Geometry.Ch3.Prop
