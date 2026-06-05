import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Interpendices.B

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
  page 0
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
  constructor
  · sorry
  · apply Subset.antisymm
    · intro P PinAB
      sorry
    · intro P PinAC
      sorry


end Geometry.Ch3.Prop
