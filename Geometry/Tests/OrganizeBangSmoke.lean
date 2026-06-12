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

/-! ## Unique extension — single Between (n=3) -/

example (A B C : Point) (ABC : A - B - C) : Arrangement [A, B, C] := by
  organize! ABC as arr
  exact arr

/-! ## Unique extension — 4-point chain (n=4) -/

example (A B C D : Point) (ABC : A - B - C) (BCD : B - C - D) :
    Arrangement [A, B, C, D] := by
  organize! ABC BCD as arr
  exact arr

/-! ## 2-extension shared-left disjunction (P6 L104 shape) -/

example (A B C P : Point) (ABC : A - B - C) (ABP : A - B - P) (CneP : C ≠ P) :
    Arrangement [A, B, C, P] ∨ Arrangement [A, B, P, C] := by
  organize! ABC ABP CneP
  exact arrAC

/-! ## 2-extension shared-outer disjunction (P6 L113 shape) -/

example (A B C P : Point) (ABC : A - B - C) (APC : A - P - C) (PneB : P ≠ B) :
    Arrangement [A, P, B, C] ∨ Arrangement [A, B, P, C] := by
  organize! ABC APC PneB
  exact arrAC

/-! ## Inequality direction shouldn't matter (`.symm` applied internally) -/

example (A B C P : Point) (ABC : A - B - C) (ABP : A - B - P) (PneC : P ≠ C) :
    Arrangement [A, B, C, P] ∨ Arrangement [A, B, P, C] := by
  organize! ABC ABP PneC
  exact arrAC

end Geometry.Tests.OrganizeBangSmoke
