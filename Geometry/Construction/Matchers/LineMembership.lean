/-
Geometry/Construction/Matchers/LineMembership.lean — `D ∈ line_through B C`,
`P ∈ ray A B`, `P ∈ segment A B`.

All three match the `Membership.mem` shape with a recognized container.
Each emits the on-X assert + (for line_through) a `construct` for the
implied line anchor.
-/

import Figures.Construction.ProofState
import Geometry.Construction.Matchers.Helpers

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL
open Figures.Construction.ProofState

private def memArgs? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  match (← instantiateMVars e).getAppFnArgs with
  | (``Membership.mem, args) =>
    if args.size < 5 then return none
    return some (args[4]!, args[3]!)
  | _ => return none

@[proof_state_matcher 0]
def matchOnLineThrough : Matcher := fun e => do
  let some (elt, container) ← memArgs? e | return none
  match container.getAppFnArgs with
  | (`Geometry.Theory.LineThrough.through, #[b, c]) =>
    let some d ← readPointName? elt | return none
    let some nb ← readPointName? b | return none
    let some nc ← readPointName? c | return none
    let lineName := lineAnchor nb.toString nc.toString
    -- The line_through construct is a CONSTRAINT anchor — without
    -- marking it hidden, it would also render as a visible full line
    -- across the canvas, overlapping any rays emitted from `P on ray …`
    -- disjuncts. Better: mark it hidden so the constraint applies but
    -- the figure shows only the asserted rays / dashed collinearity.
    return some #[
      .construct lineName (.app "line_through"
        [.name nb.toString, .name nc.toString]),
      assertN "hidden" #[lineName],
      assertN "incident" #[d.toString, lineName]
    ]
  | _ => return none

@[proof_state_matcher 0]
def matchOnRay : Matcher := fun e => do
  let some (elt, container) ← memArgs? e | return none
  match container.getAppFnArgs with
  | (`Geometry.Theory.Ray.from_, #[a, b]) =>
    let some p ← readPointName? elt | return none
    let some na ← readPointName? a | return none
    let some nb ← readPointName? b | return none
    let aStr := na.toString
    let bStr := nb.toString
    return some #[
      .construct s!"ray_{aStr}_{bStr}" (.app "ray" [.name aStr, .name bStr]),
      assertN "on_ray" #[p.toString, aStr, bStr],
    ]
  | _ => return none

@[proof_state_matcher 0]
def matchOnSegment : Matcher := fun e => do
  let some (elt, container) ← memArgs? e | return none
  match container.getAppFnArgs with
  | (`Geometry.Theory.Segment.between, #[a, b]) =>
    let some p ← readPointName? elt | return none
    let some na ← readPointName? a | return none
    let some nb ← readPointName? b | return none
    let aStr := na.toString
    let bStr := nb.toString
    return some #[
      .construct s!"seg_{aStr}_{bStr}" (.app "segment" [.name aStr, .name bStr]),
      assertN "on_segment" #[p.toString, aStr, bStr],
    ]
  | _ => return none

end Geometry.Construction.Matchers
