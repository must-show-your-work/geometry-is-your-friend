/-
Geometry/Tests/OrganizeBangSmoke.lean — smoke test for the `organize!`
lattice driver. Each example builds the smallest theorem that exercises
one branch of `runOrganizeLattice` (unique extension / 2-extension /
shared-left / shared-outer) and discharges via the introduced
arrangement.
-/

import Geometry.Theory.Arrangement

namespace Geometry.Tests.OrganizeBangSmoke

open Geometry.Theory

/-! ## Unique extension — single Between (n=3); goal is the Arrangement -/

example (A B C : Point) (ABC : A - B - C) : Arrangement [A, B, C] := by
  organize! ABC

/-! ## Unique extension — 4-point chain (n=4); goal is the Arrangement -/

example (A B C D : Point) (ABC : A - B - C) (BCD : B - C - D) :
    Arrangement [A, B, C, D] := by
  organize! ABC BCD

/-! ## Unique extension — goal is a Between projected from the arrangement -/

example (A B C D : Point) (ABC : A - B - C) (BCD : B - C - D) : A - C - D := by
  organize! ABC BCD

/-! ## Same shape, reverse-monotonic ranks ⇒ projection uses `.symm` -/

example (A B C D : Point) (ABC : A - B - C) (BCD : B - C - D) : D - C - A := by
  organize! ABC BCD

/-! ## 2-extension shared-left disjunction (P6 L104 shape) -/

example (A B C P : Point) (ABC : A - B - C) (ABP : A - B - P) (CneP : C ≠ P) :
    Arrangement [A, B, C, P] ∨ Arrangement [A, B, P, C] := by
  organize! ABC ABP CneP

/-! ## 2-extension shared-outer disjunction (P6 L113 shape) -/

example (A B C P : Point) (ABC : A - B - C) (APC : A - P - C) (PneB : P ≠ B) :
    Arrangement [A, P, B, C] ∨ Arrangement [A, B, P, C] := by
  organize! ABC APC PneB

/-! ## Inequality direction shouldn't matter (`.symm` applied internally) -/

example (A B C P : Point) (ABC : A - B - C) (ABP : A - B - P) (PneC : P ≠ C) :
    Arrangement [A, B, C, P] ∨ Arrangement [A, B, P, C] := by
  organize! ABC ABP PneC
  -- Goal-dispatch assigned directly; nothing else needed.

/-! ## Auto-orientation — `.symm` shouldn't be the user's burden -/

-- `BAP` is `B-A-P` (A between B and P). Combined with `ABC` (B between A and C),
-- the consistent linear order is `P, A, B, C` (or its mirror). organize! must
-- figure this out — flipping BAP via `.symm` to PAB internally — rather than
-- asking the user to do it.
example (A B C P : Point) (BAP : B - A - P) (ABC : A - B - C) :
    Arrangement [P, A, B, C] := by
  organize! BAP ABC

/-! ## LCtx inequality scan — `PneC` already in scope, don't repeat -/

example (A B C P : Point) (ABC : A - B - C) (ABP : A - B - P) (PneC : P ≠ C) :
    Arrangement [A, B, C, P] ∨ Arrangement [A, B, P, C] := by
  -- PneC NOT passed explicitly; organize! picks it up from LCtx.
  organize! ABC ABP

/-! ## LCtx inequality scan via `by_cases`'s false branch (`¬(P = C)` shape) -/

example (A B C P : Point) (ABC : A - B - C) (ABP : A - B - P) :
    (P = C) ∨ Arrangement [A, B, C, P] ∨ Arrangement [A, B, P, C] := by
  by_cases hPeqC : P = C
  · left; exact hPeqC
  · right
    organize! ABC ABP

/-! ## `arr_cases` — auto-named rcases on Arrangement disjunction -/

example (A B C P : Point) (ABC : A - B - C) (ABP : A - B - P) (CneP : C ≠ P) :
    Nonempty (Arrangement [A, B, C, P]) ∨ Nonempty (Arrangement [A, B, P, C]) := by
  organize! ABC ABP CneP
  arr_cases arrAC
  · left; exact ⟨ABCP⟩
  · right; exact ⟨ABPC⟩

end Geometry.Tests.OrganizeBangSmoke
