import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert

import Geometry.Theory.Axioms
import Geometry.Theory.Interpendices.B

import Geometry.Tactics

import Geometry.Construction.AtlasField
import Atlas

namespace Geometry.Ch3.Prop

open Geometry.Theory
open Atlas

atlas commentary := by
  via corollary B.4.iii
  page 111
  name "Corollary to B-4: splits + guards transitivity"
  preface "Corollary. (iii) If A and B are on opposite sides of L and if B and C are on the same side of L, then A and C are on opposite sides of L"
  notes "This gets shown here since it's a corollary and I need a lemma from the
previous proposition

FIXME: I think I need to drop the avoid hypothesis and do the by_cases argument."

  -- figure := by
    -- construction {
      -- exists A B C X : Point
      -- exists L : Line
      -- assert distinct A B C
      -- assert between A X B
      -- assert incident X L
      -- focus L
      -- construct segAB := segment A B
      -- construct segBC := segment B C
      -- construct segAC := segment A C
    -- }
    -- title "Corollary B.4 (iii)"
    -- index 1
    -- caption "L splits AB at X; B and C are on the same side, so A and C end up on opposite sides."

atlas corollary B.4.iii "Corollary to B-4: splits + guards transitivity"
  (AoffL : A off L := by assumption)
  (BoffL : B off L := by assumption)
  (CoffL : C off L := by assumption) :
  (L splits A and B) ∧ (L guards B and C) -> (L splits A and C) := by
  intro ⟨LsplitsAB, LguardsBC⟩
  by_contra! LguardsAC
  have h := via axiom B.4.i ⟨LguardsAC, LguardsBC.symm⟩
  contradiction


/-

As is often the case, the above theorem once looked like a 5 page epic, but was
rapidly reduced when I found the correct way to think about it.

When I was a kid, I was homeschooled, and I was frustrated by that because I never
had much chance to make what I usually thought of as 'academic friends.' The sort of
people who were interested in the same kinds of weird niche things I was -- linguistics,
mathematics, philosophy, art, music.

My Dad liked those things too, well, he preferred programming to pure math, and religion
subsumed and subsumes his philosophy, art, and music; but he was close enough. Trouble was
he wasn't around much, so -- being a bright homeschooled kid with nothing better to do, I
hatched a little plan.

-/
end Geometry.Ch3.Prop
