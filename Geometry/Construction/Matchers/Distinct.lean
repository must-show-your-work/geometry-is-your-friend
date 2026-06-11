/-
Geometry/Construction/Matchers/Distinct.lean — `Distinct {…} _ → assert distinct …`
-/

import Figures.Construction.ProofState
import Geometry.Construction.Matchers.Helpers

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL
open Figures.Construction.ProofState

@[proof_state_matcher 0]
def matchDistinct : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (`Geometry.Theory.Distinct, #[s, _n]) =>
    let some pts ← readFinsetPoints s | return none
    return some #[assertN "distinct" pts]
  | _ => return none

end Geometry.Construction.Matchers
