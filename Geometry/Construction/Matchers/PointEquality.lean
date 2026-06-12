/-
Geometry/Construction/Matchers/PointEquality.lean — match `A = B`
between two `Point` fvars and emit `assert equal A B` so the figure
collapses the two points to the same position.

Comes up in proofs that case-split on equality — e.g. `clearly B ≠ D
:= by ...` whose `by` branch has `B = D` in scope.
-/

import Figures.Construction.ProofState
import Geometry.Construction.Matchers.Helpers

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL
open Figures.Construction.ProofState

@[proof_state_matcher 50]
def matchPointEquality : Matcher := fun e => do
  let e ← instantiateMVars e
  -- Accept both `Eq Point A B` (the usual `=` elaboration) and
  -- `HEq Point A Point B` (heterogeneous equality, in case Lean stored
  -- the eq in a coerced form).
  match e.getAppFnArgs with
  | (``Eq, #[_ty, a, b]) =>
    let some na ← readPointName? a | return none
    let some nb ← readPointName? b | return none
    return some #[assertN "equal" #[na.toString, nb.toString]]
  | (``HEq, #[_ta, a, _tb, b]) =>
    let some na ← readPointName? a | return none
    let some nb ← readPointName? b | return none
    return some #[assertN "equal" #[na.toString, nb.toString]]
  | _ => return none

end Geometry.Construction.Matchers
