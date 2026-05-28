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
import Atlas

namespace Geometry.Ch3.Ex

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas


atlas commentary := by
  ref exercise 3.Review.2
  page 146
  preface "
    (a) Finish the proof of proposiiton 3.1 by showing that ray A B ∪ ray B A = line A B
    (b) Finish the proof of proposition 3.3 by showing that A-B-D
    (c) Prove the converse of Proposition 3.3 by applying Axiom B-1
    (d) Prove the corollary to Proposition 3.3
  "
  notes "Most of these are covered elsewhere, this just gangs the results to a complex"

atlas exercise 3.Review.2.c "Given B-C-D and A-B-D, then A-B-C and A-C-D"
  (BCD : B - C - D := by assumption) (ABD : A - B - D := by assumption) :
  A-B-C ∧ A-C-D := by arranging ABD BCD


end Geometry.Ch3.Ex
