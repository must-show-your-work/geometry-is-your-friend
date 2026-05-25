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

end Betweenness

/-- Dot-notation wrappers -/
@[symm] def Guards.symm {A B : Point} {L : Line} (h : Guards A B L) : Guards B A L := by obvious
@[symm] def Splits.symm {A B : Point} {L : Line} (h : Splits L A B) : Splits L B A := by obvious

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
