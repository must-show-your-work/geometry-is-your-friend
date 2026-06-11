/-
Geometry/Construction/Matchers/Intersects.lean — match
`L intersects M at X` (i.e. `Geometry.Theory.Intersects L M X`) and
emit constraints that pin X onto both shapes.

For figure purposes: `X` lies on the line `L` AND on whatever shape
`M` is (segment, line, ray). We emit:
- `assert incident X L`
- An on-shape annotation for M's shape via per-case sub-matchers
  (segment / line_through / ray)
-/

import Figures.Construction.ProofState
import Geometry.Construction.Matchers.Helpers

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL
open Figures.Construction.ProofState

@[proof_state_matcher 50]
def matchIntersectsAt : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (`Geometry.Theory.Intersects, #[lineExpr, shapeExpr, pointExpr]) =>
    let some nLine ← readLineName? lineExpr | return none
    let some nPoint ← readPointName? pointExpr | return none
    let xStr := nPoint.toString
    let lStr := nLine.toString
    -- Build a per-shape stmt for X-on-M based on M's head.
    let onShape ← match shapeExpr.getAppFnArgs with
      | (`Geometry.Theory.Segment.between, #[a, b]) =>
        let some na ← readPointName? a | pure none
        let some nb ← readPointName? b | pure none
        pure (some (assertN "on_segment" #[xStr, na.toString, nb.toString]))
      | (`Geometry.Theory.LineThrough.through, #[a, b]) =>
        let some na ← readPointName? a | pure none
        let some nb ← readPointName? b | pure none
        let lineName := lineAnchor na.toString nb.toString
        pure (some (assertN "incident" #[xStr, lineName]))
      | (`Geometry.Theory.Ray.from_, #[a, b]) =>
        let some na ← readPointName? a | pure none
        let some nb ← readPointName? b | pure none
        pure (some (assertN "on_ray" #[xStr, na.toString, nb.toString]))
      | _ => pure none
    let mut stmts : Array Stmt := #[assertN "incident" #[xStr, lStr]]
    if let some s := onShape then stmts := stmts.push s
    return some stmts
  | _ => return none

end Geometry.Construction.Matchers
