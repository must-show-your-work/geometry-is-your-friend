/-
Geometry/Construction/Matchers/Between.lean — `Between A B C → assert between A B C`
-/

import Figures.Construction.ProofState
import Geometry.Construction.Matchers.Helpers

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL
open Figures.Construction.ProofState

@[proof_state_matcher 0]
def matchBetween : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (`Geometry.Theory.Between, #[a, b, c]) =>
    let some args ← readPointArgs #[a, b, c] | return none
    return some #[assertN "between" args]
  | _ => return none

end Geometry.Construction.Matchers
