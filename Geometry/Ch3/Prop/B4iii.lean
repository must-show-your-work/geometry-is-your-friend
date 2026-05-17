
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Tactics

import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Ch2
import Geometry.Theory.Line.Ch2
import Geometry.Theory.Betweenness.Ch2
import Atlas

import Geometry.Ch2.Prop
import Geometry.Ch3.Prop.P1

namespace Geometry.Ch3.Prop

-- open Set
open Geometry.Theory
open Geometry.Ch2.Prop
-- (open removed: P1.i/P1.ii aliases inlined to titles)

-- p111

/-
"Corollary. (iii) If A and B are on opposite sides of L and if B and C are on the
same side of L, then A and C are on opposite sides of L"

Ed. This gets shown here since it's a corollary and I need a lemma from the
previous proposition


FIXME: I think I need to drop the avoid hypothesis and do the by_cases argument.
-/
atlas corollary ["B.4.iii"] "Corollary to B-4: splits + guards transitivity"
  : (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L splits A and B) ∧ (L guards B and C) -> (L splits A and C) := by
  intro ⟨AoffL, BoffL, CoffL⟩ ⟨LsplitsAB, LguardsBC⟩
  by_contra! LguardsAC
  have h := «Same-side is transitive across a common middle point» ⟨AoffL, CoffL, BoffL⟩ ⟨LguardsAC, ref lemma 2.0.30 LguardsBC⟩
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
