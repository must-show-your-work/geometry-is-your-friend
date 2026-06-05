import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Interpendices.B
import Geometry.Theory.Arrangement

import Geometry.Tactics

import Geometry.Ch3.Prop.P3

import Geometry.Construction.AtlasField
import Atlas

namespace Geometry.Ch3.Ex

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas


atlas commentary := by
  -- TODO: We need support for theorem complexes. A 'virtual' theorem here and it's descriptions, then some
  -- way of saying "this is a complex of all the subparts.
  via exercise 3.Review.3
  page 146
  preface "Given A-B-C
    (a) Use Proposition 3.3 to prove that AB ⊆ AC. Interchanging A and C, deduce CD ⊂ CA; which axiom justifies this
interchange?
    (b) Use Axiom B-4 to prove that AC ⊂ AB ∪ BC. (Hint: If P is a fourth point on AC, use another line through P to show P
    ∈ AB or P ∈ BC.)
    (c) Finish the proof of proposition 3.5. (Hint: If P ≠ B and P ∈ AB ∩ BC, use another line through P to get a
    contradiction.)
  "
  notes "Author has triggered a pet peeve, I would have written (b) and (c) as '(x) Statement (Hint).' and not '(x) Statement. (Hint.)'

  Additionally, I think the second part of (a) and the assertion of (b) is wrong. For (a) Introducing a new point (`D`),
we can place that anywhere. I think the author clearly _meant_ B here, and that is what I've proved. In fact, place D
such that D-A-B, then clearly ¬(CD ⊂ CA), since A-B-C. However, BC ⊂ AC makes perfect sense. The use of proper vs
improper subset here is also odd, AB ⊂ AC clearly; but the author uses `⊆`. I've maintained fidelity despite the oddity.

  Similarly, for (b), We end up proving in 3.5 that AC = AB U BC so we certainly can't prove it's a proper subset.

  Finally, I've broken the first statement into individual sub exercises. Atlas gangs all these together as a theorem
complex, so it is easiest to just break down by conclusion.
  "

  figure := by
    construction {
      exists A B C : Point
      assert distinct A B C
      assert between A B C
      construct segAC := segment A C
    }

atlas exercise 3.Review.3.a.i "If A-B-C, then AB ⊆ AC"
  {A B C : Point} (ABC : A - B - C := by assumption) :
  ((segment A B : Line) ⊆ (segment A C)) := by
  intro P PonAB
  rcases PonAB with APB | rfl | rfl
  · have APBC : A - P - B - C := by organize ABC APB
    have APC : A - P - C := APBC
    obvious
  all_goals obvious

atlas exercise 3.Review.3.a.ii "[If A-B-C, then] CB ⊂ CA; which axiom justifies this interchange?"
  {A B C : Point} (ABC : A - B - C := by assumption) :
  ((segment C B : Line) ⊂ (segment C A)) := by
  refine ⟨?_, ?_⟩
  · exact via exercise 3.Review.3.a.i ABC.symm
  · by_contra! CAsubCB
    have AoffCB : A off segment C B := via corollary 2.0.27 ABC.symm
    have AinCA : A on segment C A := obvious
    obvious

atlas exercise 3.Review.3.b "[If A-B-C,] then AC ⊂ AB ∪ BC."
  {A B C : Point} (ABC : A - B - C := by assumption) :
  (segment A C : Line) ⊆ (segment A B) ∪ (segment B C) := by
  intro P PonAC
  rcases PonAC with APC | rfl | rfl
  · arranging ABC APC into ABP | rfl | BPC
  all_goals obvious


end Geometry.Ch3.Ex
