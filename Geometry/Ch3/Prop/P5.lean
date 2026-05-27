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
import Geometry.Theory.Interpendices.A
import Geometry.Theory.Interpendices.B
import Geometry.Theory.Interpendices.C
import Geometry.Theory.Forgetting
import Atlas

namespace Geometry.Ch3.Prop

open Set
open Geometry.Theory
open Geometry.Ch2.Prop
open Geometry.Ch3.Prop
open Geometry.Ch3.Ex
open Atlas


atlas commentary := by
  -- TODO: We need support for theorem complexes. A 'virtual' theorem here and it's descriptions, then some
  -- way of saying "this is a complex of all the subparts.
  ref exercise ["3.0.3"]
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

  Additionally, I think the second part of (a) is wrong. Introducing a new point (`D`), we can place that anywhere. I
think the author clearly _meant_ B here, and that is what I've proved. In fact, place D such that D-A-B, then clearly
¬(CD ⊂ CA), since A-B-C. However, BC ⊂ AC makes perfect sense. The use of proper vs improper subset here is also odd,
AB ⊂ AC clearly; but the author uses `⊆`. I've maintained fidelity despite the oddity.
  
  Finally, I've broken the first statement into individual sub exercises. Atlas gangs all these together as a theorem
complex, so it is easiest to just break down by conclusion.
  "

atlas exercise ["3.0.3.a.i"] "If A-B-C, then AB ⊆ AC"
  {A B C : Point} (ABC : A - B - C := by assumption) :
  ((segment A B : Line) ⊆ (segment A C)) := by
  intro P PonAB
  rcases PonAB with APB | rfl | rfl
  · have APBC : A - P - B - C := by organize ABC APB
    have APC : A - P - C := APBC
    obvious
  all_goals obvious

-- FIXME: commented because ssubset isn't supported
atlas exercise ["3.0.3.a.ii"] "[If A-B-C, then] CB ⊂ CA; which axiom justifies this interchange?"
  {A B C : Point} (ABC : A - B - C := by assumption) :
  ((segment C B : Line) ⊂ (segment C A)) := by 
  sorry

atlas exercise ["3.0.3.b"] "[If A-B-C,] then AC ⊂ AB ∪ BC."
  {A B C : Point} (ABC : A - B - C := by assumption) :
  (segment A C : Line) ⊂ (segment A B) ∪ (segment B C) := by
  sorry

atlas commentary := by
  ref exercise ["3.0.2"]
  page 146
  preface "
    (a) Finish the proof of proposiiton 3.1 by showing that ray A B ∪ ray B A = line A B
    (b) Finish the proof of proposition 3.3 by showing that A-B-D
    (c) Prove the converse of Proposition 3.3 by applying Axiom B-1
    (d) Prove the corollary to Proposition 3.3
  "
  notes "Most of these are covered elsewhere, this just gangs the results to a complex"

atlas exercise ["3.0.2.c"] "Given B-C-D and A-B-D, then A-B-C and A-C-D"
  (BCD : B - C - D := by assumption) (ABD : A - B - D := by assumption) :
  A-B-C ∧ A-C-D := by arranging ABD BCD
  
  
atlas commentary := by
  ref proposition 3.5
  page 114
  aliases [
    -- exercise ["3.0.3.c"]
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
      have PoffBC : P off segment B C := via lemma 2.0.30 APBC
      contradiction
    · rw [PeqA] at ABC
      have PoffBC : P off segment B C := via lemma 2.0.30 ABC
      contradiction
    · obvious
  · intro PisB; obvious


end Geometry.Ch3.Prop
