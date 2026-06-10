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

import Geometry.Tactics

import Geometry.Construction.AtlasField

import Geometry.Ch3.Prop.P6

import Atlas

namespace Geometry.Ch3.Prop


open Set
open Geometry.Theory
open Geometry.Ch3.Prop
open Atlas


-- p18 'Rays AB and AC are "opposite" if they are distinct, if they emanate from the same point A, and if they are part
-- of the same line AB = AC'
def OppositeRay (A B C : Point) : Prop :=
  (ray A B : Set Point) ≠ ray A C ∧ (line A B : Set Point) = line A C

-- TODO: Syntax `ray A B is opposite ray A C` -- only applies to rays I think.

-- p18, 'An "angle with vertex A" is a point A together with distinct, non-opposite rays AB and AC (called the _sides_
-- of the angle) emanating from A (see figure 1.7)[^9]
--
-- We use the notation ∠ A, ∠ BAC, or ∠ CAB for this angle. If r = ray A B and s = ray A C, then rays r, s are said to
-- be coterminal (meaning they emanate from the same vertex), and the angle is also denoted ∠(r, s).
--
-- [footnote 9] According to this definition, there is no such thing in our treatment as a "straight angle", nor is
-- there such a thing as a "zero angle." We eliminated those expressions because most of the assertions we will make
-- about angles do not apply to them.'
@[reducible] def Angle (A B C : Point) : Prop :=
  distinct A B C ∧ ¬OppositeRay A B C

-- FIXME: How do I _just_ talk about rays in my model? Some kind of 'abstract ray' type?
-- def Coterminal (r s : Ray) : Prop := ∃ A B C : Point, A on r ∧ B on r ∧ A on s ∧ C on s ∧ ¬OppositeRay r s
--
-- FIXME: not sure if this covers what I need, can't refer by handing it a whole ray, for sure. hm.
def Coterminal (A B C : Point) : Prop :=
  ¬ OppositeRay A B C ∧ (ray A B : Set Point) ≠ ray A C
  
-- TODO: Syntax ∠ B A C -> Angle B A C = Angle C A B; ∠(r,s) also needs support. ∠ (ray A B) (ray A C).
  
-- p115, 'Given an angle ∠ CAB, define a point D to be in the interior of ∠CAB if D is on the same side of AC as B and
-- if D is also on the same side of AB as C. (Thus, the interior of an angle is the intersection of two half-planes.)
-- See Figure 3.11.'
def InteriorOf (B A C D : Point) :=
  Angle B A C ∧ (ray A C guards B and D) ∧ (ray A B guards C and D)

atlas commentary := by
  via proposition 3.7
  page 115
  name "Given an angle ∠CAB and point D lying on line BC. Then D is in the interior of ∠CAB if and only if B-D-C (see
  figure 3.12"
  preface ""

  figure := by
    construction {
      exists A B C : Point
      exists D : Point
      exists L : Line
      assert distinct A B C
      assert ¬ collinear A B C
      construct rayAB := ray A B
      construct rayAC := ray A C
      construct lineBC := line B C
      assert incident D L
      assert incident B L
      assert incident C L
      assert between B D C
      focus D
    }
    title "Proposition 3.7"
    index 1
    caption ""


atlas proposition 3.7 "D on line BC is interior to ∠CAB iff B-D-C"
  { A B C D : Point } (DonBC : D on line B C) (aCAB : Angle C A B := by assumption) (DonBC : D on line B C := by assumption) :
    InteriorOf B A C D ↔ B-D-C := by
    have cBCD : collinear B C D := by
      use line B C
      intro P PisBCD; by_exhaustion PisBCD
      all_goals obvious
    obtain ⟨dABC, _⟩ := aCAB
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
        · separate; distinguish
        · by_contra!; obtain ⟨_, BAeqBC⟩ := this
          auxillary {
            -- need to force AC onto AB,
          }
          -- rw [<- BAeqBC] at DonBC -- why doesn't this work?

          sorry
      · constructor
        todo "this argument is symmetric about AD, so a suffices is probably usable here?"
        · sorry
        · sorry


end Geometry.Ch3.Prop
