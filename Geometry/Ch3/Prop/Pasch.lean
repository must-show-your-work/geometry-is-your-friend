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
import Geometry.Ch3.Ex.Ex1
import Geometry.Theory.Distinct
import Geometry.Theory.Collinear.Ch1
import Geometry.Theory.Collinear.Ch2
import Geometry.Theory.Betweenness.Ch1
import Geometry.Theory.Betweenness.Ch2
import Geometry.Theory.Line.Ch1
import Geometry.Theory.Line.Ch2
import Geometry.Theory.Forgetting

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex


/-- p.114 If A,B,C are distinct noncollinear points and L is any line intersecting AB in a point between A and B, then L
also intersect AC or BC (see figure 3.10). If C does not lie on L, then L does not intersect both AC and BC.

  Intuititively, this theorem says that if a line "goes into" a triangle through one side, it must "come out" through
another side.-/
theorem pasch {A B C : Point} {L : Line}
  (triABC : ¬(collinear A B C)) (LintAB : L intersects segment A B) :
  ((L intersects segment A C) ∨ (L intersects segment B C)) ∧
  (C off L -> ¬((L intersects segment A C) ∧ (L intersects segment B C))) := by
    
    sorry


end Geometry.Ch3.Prop


