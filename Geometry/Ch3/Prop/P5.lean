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
import Geometry.Ch3.Prop.P4
import Geometry.Ch3.Ex.Betweenness.Ex1
import Geometry.Theory.Distinct
import Geometry.Theory.Interpendices.A
import Geometry.Theory.Interpendices.B
import Geometry.Theory.Interpendices.C
import Geometry.Theory.Forgetting
import Geometry.Construction.AtlasField
import Atlas

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas


atlas commentary := by
  via proposition 3.5
  page 114
  aliases [
    exercise 3.Review.3.c
  ]
  name "Given A-B-C. Then AC = AB ∪ BC and B is the only point common to segments AB and BC."
  preface "Here are some more results on betweenness and separation that you will be asked to prove in the exercises"

  figure := by
    construction {
      exists A B C : Point
      assert distinct A B C
      assert between A B C
      construct segAB := segment A B
      construct segBC := segment B C
    }
    title "Proposition 3.5"
    index 1
    caption "With B between A and C, segment AC is the union of AB and BC; the intersection is the single point B."


atlas proposition 3.5 "If A-B-C then AC = AB ∪ BC..."
  {A B C : Point} (ABC : A - B - C := by assumption) :
  ((segment A C : Line) = (segment A B : Line) ∪ (segment B C)) := by
  apply Line.eq_of_subset
  · intro P PonAC
    rcases PonAC with APC | PeqA | PeqC
    · arranging ABC APC
    all_goals obvious
  · intro P PonABorBC
    arranging ABC PonABorBC into (APB | _ | _) | (BPC | _ | _)

atlas corollary 3.5 "[If A-B-C then ...], and AB intersects BC at B"
  {A B C : Point} (ABC : A - B - C := by assumption) :
  (segment A B intersects segment B C at B) := by
  ext P; constructor
  · intro ⟨PinAB, PinBC⟩
    rcases PinAB with APB | PeqA | PeqB
    · have APBC : A - P - B - C := by organize ABC APB
      have PoffBC : P off segment B C := via lemma 2.0.27 APBC
      contradiction
    · rw [PeqA] at ABC
      have PoffBC : P off segment B C := via lemma 2.0.27 ABC
      contradiction
    · obvious
  · intro PisB; obvious


end Geometry.Ch3.Prop
