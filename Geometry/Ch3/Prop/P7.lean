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
        separate; distinguish;
        obvious
        exact CneD
      rcases guardConditionBD with rfl | BDguard
      · obvious
      · rcases guardConditionCD with rfl | CDguard
        · exfalso; exact absurd DoffAC obvious
        · rcases (via axiom B.3 B C D ⟨dABCD forgetting A, cBCD⟩) with ⟨BCD, _, _⟩ | ⟨_,CBD,_⟩ | ⟨_, _, BDC⟩
          · exfalso; idea "violates the guard condition"
            exact BDguard C (by obvious) (by obvious : C on line A C)
          · exfalso; idea "ibid"
            exact CDguard B (by obvious) (by obvious : B on line A B)
          · exact BDC
    · intro BDC
      clearly B off line A C := by sorry
      clearly D off line A C := by sorry
      clearly C off segment B D := by sorry
      constructor
      · constructor
        · separate; distinguish
        · obvious
      · constructor
        · refine ⟨(by assumption), (by assumption), ?_⟩
          right
          intro P PonSegBD
          by_contra! PonAC
          have BDeqBC : (line B D : Line) = line B C := (via corollary 3.6 BDC).left
          have PonBD : P on line B D := via lemma 2.0.4 PonSegBD
          comment "Type shenanigans necessary because lines-as-sets is a leaky thing"
          change P ∈ (line B D : Line) at PonBD
          rw [BDeqBC] at PonBD
          have PeqC : P = C := by
            idea "P is on AC and BC, so P = C because intersections are uniqu"
            have : P ∈ (line A C : Line) ∩ (line B C) := by sorry
            have : line A C intersects line B C at P := by sorry
            have : line A C intersects line B C at C := by sorry
            obvious
          rw [PeqC] at PonSegBD
          contradiction
        · sorry

end Geometry.Ch3.Prop
