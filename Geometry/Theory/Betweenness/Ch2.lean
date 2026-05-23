import Mathlib.Data.Set.Defs
import Mathlib.Data.Set.Insert
import Geometry.Theory.Axioms
import Geometry.Theory.Ch1
import Geometry.Theory.Line.Ch1
import Geometry.Theory.Line.Ch2
import Geometry.Tactics
import Atlas

namespace Geometry.Theory

open Set
open Geometry.Theory
open Atlas

namespace Betweenness

atlas commentary := by
  ref lemma 2.0.30
  name "Guarding is symmetric in its two point arguments"
  preface "a line doesn't care about the order of the points it guards"

atlas lemma 2.0.30 "Guarding is symmetric in its two point arguments"
  : (L guards A and B) -> (L guards B and A) := by
    intro LguardsAB
    unfold Guards at *
    simp_all only [Segment.mem_def, «Betweenness Commutativity», eq_comm (a := B) (b := A)]
    aesop


atlas commentary := by
  ref lemma 2.0.31
  name "Splitting is symmetric in its two point arguments"
  preface "a line doesn't care about the order of the points it splits"

atlas lemma 2.0.31 "Splitting is symmetric in its two point arguments"
  : (L splits A and B) -> (L splits B and A) := by
    intro LsplitsAB
    unfold Splits Guards at *
    simp_all only [Segment.mem_def, «Betweenness Commutativity», eq_comm (a := B) (b := A)]
    aesop

end Betweenness

/-- Dot-notation wrapper: `h.symm` swaps the point args of an `L guards _ and _` hypothesis.
    Lives in `Geometry.Theory` (not the `Betweenness` sub-namespace) so dot-notation lookup
    finds it via the `Guards` type's namespace. -/
@[symm] def Guards.symm {A B : Point} {L : Line} (h : Guards A B L) : Guards B A L :=
  Betweenness.«Guarding is symmetric in its two point arguments» h

/-- Dot-notation wrapper: `h.symm` swaps the point args of an `L splits _ and _` hypothesis.
    Same namespace placement as `Guards.symm`. -/
@[symm] def Splits.symm {A B : Point} {L : Line} (h : Splits L A B) : Splits L B A :=
  Betweenness.«Splitting is symmetric in its two point arguments» h

section Examples
-- Confirms the `symm` tactic finds the `@[symm]` tags on `Guards.symm` / `Splits.symm` / `Between.symm`.
example {A B : Point} {L : Line} (h : Guards A B L) : Guards B A L := by symm; exact h
example {A B : Point} {L : Line} (h : Splits L A B) : Splits L B A := by symm; exact h
example {A B C : Point} (h : A - B - C) : C - B - A := by symm; exact h
-- And via dot notation.
example {A B : Point} {L : Line} (h : Guards A B L) : Guards B A L := h.symm
example {A B : Point} {L : Line} (h : Splits L A B) : Splits L B A := h.symm
example {A B C : Point} (h : A - B - C) : C - B - A := h.symm
end Examples

end Geometry.Theory
