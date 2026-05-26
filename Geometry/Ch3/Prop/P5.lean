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
import Geometry.Theory.Intersection.Ch3
import Atlas

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas


atlas commentary := by
  ref exercise ["3.B.3"]
  page 146
  preface "Given A-B-C
    (a) Use Proposition 3.3 to prove that AB ⊆ AC. Interchanging A and C, deduce CD ⊂ CA; which axiom justifies this
interchange?
    (b) Use Axiom B-4 to prove that AC ⊂ AB ∪ BC. (Hint: If P is a fourth point on AC, use another line through P to show P
    ∈ AB or P ∈ BC.)
    (c) Finish the proof of proposition 3.5. (Hint: If P ≠ B and P ∈ AB ∩ BC, use another line through P to get a
    contradiction.)
  "
  notes "Author has triggered a pet peeve, I would have written (b) and (c) as '(x) Statement (Hint).' and not '(x) Statement. (Hint.)'"

atlas exercise ["3.B.3.a"] "If A-B-C, then AB ⊆ AC"



atlas commentary := by
  ref proposition 3.5
  page 114
  aliases [
    -- (exercise ["3.B.3.c"])
  ]
  name "Given A-B-C. Then AC = AB ∪ BC and B is the only point common to segments AB and BC."
  preface "Here are some more results on betweenness and separation that you will be asked to prove in the exercises"
  notes "This theorem is essentially 'you can cut a segment into parts via betweenness.' I've aimed to just directly
prove the theorem without completing the other exercises. The exercises in this book are very good and well worth the
price of admission, so I don't want to spoil them all here."


atlas proposition 3.5 "If A-B-C then AC = AB ∪ BC..."
  {A B C : Point} (ABC : A - B - C := by assumption) :
  ((segment A C : Line) = (segment A B : Line) ∪ (segment B C)) := by
  apply Line.eq_of_subset
  · intro P PonAC
    rcases PonAC with APC | PeqA | PeqC
    · idea "Prop 3.3?"
      sorry
    all_goals obvious
  · intro P PonABorBC
    rcases PonABorBC with (APB | _ | _) | (BPC | _ | _)
    · have APC : A - P - C := (via proposition 3.3.ii ⟨APB, ABC⟩)
      obvious
    · obvious
    · obvious
    · have APC : A - P - C := by
        sorry
      obvious
    · obvious
    · obvious

atlas corollary 3.5 "[If A-B-C then ...], and AB intersects BC at B"
  {A B C : Point} (ABC : A - B - C := by assumption) :
  (segment A B intersects segment B C at B) := by
  sorry


end Geometry.Ch3.Prop
