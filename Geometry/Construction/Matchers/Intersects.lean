/-
Geometry/Construction/Matchers/Intersects.lean — match
`L intersects M at X` (`Geometry.Theory.Intersects L M X`) and the bare
`L intersects M` (`Geometry.Theory.IntersectsSome L M`).

Both emit a `construct` for the shape `M` (segment / line_through /
ray) so the shape is VISIBLE in the figure, plus on-shape constraints
when an explicit intersection point is known. Without the construct
emission, hypotheses like `L intersects segment A B at X` would put
constraints on A, B, X but no segment would actually be drawn —
because nothing in the proof state constructs it.
-/

import Figures.Construction.ProofState
import Geometry.Construction.Matchers.Helpers

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL
open Figures.Construction.ProofState

private def isShapeHead (e : Expr) : Bool :=
  match e.getAppFnArgs with
  | (`Geometry.Theory.Segment.between, _)
  | (`Geometry.Theory.LineThrough.through, _)
  | (`Geometry.Theory.Ray.from_, _)
  | (`Geometry.Theory.Extension.past, _)
  | (`Geometry.Theory.LineV2.mkLine, _)
  | (`Geometry.Theory.LineV2.mkRay, _)
  | (`Geometry.Theory.LineV2.mkSegment, _) => true
  | _ => false

/-- Walk through possible coercion wrappers to find the inner
shape-constructor application. -/
private partial def unwrapToShape (e : Expr) : Expr :=
  if isShapeHead e then e
  else
    let (_, args) := e.getAppFnArgs
    args.foldr (init := e) fun arg acc =>
      let recurse := unwrapToShape arg
      if isShapeHead recurse then recurse else acc

/-- Given a shape expression (segment/ray/line_through), produce the
`construct <name> := <head> A B` stmt that makes it visible, plus the
synthesized construct name. Unwraps coercions. Returns `none` if the
shape head isn't recognized. -/
private def shapeConstruct (shapeExpr : Expr) :
    MetaM (Option (Stmt × String × String × String)) := do
  let shapeExpr := unwrapToShape shapeExpr
  let abKind : Option (Expr × Expr × String) := match shapeExpr.getAppFnArgs with
    | (`Geometry.Theory.Segment.between, #[a, b]) => some (a, b, "segment")
    | (`Geometry.Theory.LineThrough.through, #[a, b]) => some (a, b, "line_through")
    | (`Geometry.Theory.Ray.from_, #[a, b]) => some (a, b, "ray")
    | (`Geometry.Theory.LineV2.mkSegment, args) =>
      if args.size ≥ 2 then some (args[0]!, args[1]!, "segment") else none
    | (`Geometry.Theory.LineV2.mkLine, args) =>
      if args.size ≥ 2 then some (args[0]!, args[1]!, "line_through") else none
    | (`Geometry.Theory.LineV2.mkRay, args) =>
      if args.size ≥ 2 then some (args[0]!, args[1]!, "ray") else none
    | _ => none
  let some (a, b, kind) := abKind | return none
  let some na ← readPointName? a | return none
  let some nb ← readPointName? b | return none
  let aStr := na.toString
  let bStr := nb.toString
  let name := match kind with
    | "line_through" => lineAnchor aStr bStr
    | "segment" => s!"seg_{aStr}_{bStr}"
    | "ray" => s!"ray_{aStr}_{bStr}"
    | _ => s!"shape_{aStr}_{bStr}"
  return some (.construct name (.app kind [.name aStr, .name bStr]),
               kind, aStr, bStr)

/-- The point-on-shape assert for X on the constructed shape. -/
private def onShapeAssert (shapeKind aStr bStr xStr : String) : Stmt :=
  match shapeKind with
  | "segment" => assertN "on_segment" #[xStr, aStr, bStr]
  | "line_through" => assertN "incident" #[xStr, lineAnchor aStr bStr]
  | "ray" => assertN "on_ray" #[xStr, aStr, bStr]
  | _ => assertN "incident" #[xStr, aStr]

@[proof_state_matcher 50]
def matchIntersectsAt : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (`Geometry.Theory.Intersects, #[lineExpr, shapeExpr, pointExpr]) =>
    let some nLine ← readLineName? lineExpr | return none
    let some nPoint ← readPointName? pointExpr | return none
    let xStr := nPoint.toString
    let lStr := nLine.toString
    -- Constructor shape (segment / line_through / ray) — emit the
    -- shape's construct + on-shape assertion.
    match (← shapeConstruct shapeExpr) with
    | some (constructStmt, kind, aStr, bStr) =>
      return some #[
        constructStmt,
        assertN "incident" #[xStr, lStr],
        onShapeAssert kind aStr bStr xStr,
      ]
    | none =>
      -- Fallback: shapeExpr is an fvar Line (e.g. P2.1's `L intersects
      -- M at X` with M a binder). Both lines already exist via the
      -- LCtx/Pi walk; just assert X lies on both.
      let some nShape ← readLineName? shapeExpr | return none
      return some #[
        assertN "incident" #[xStr, lStr],
        assertN "incident" #[xStr, nShape.toString],
      ]
  | _ => return none

@[proof_state_matcher 50]
def matchIntersectsSome : Matcher := fun e => do
  match (← instantiateMVars e).getAppFnArgs with
  | (`Geometry.Theory.IntersectsSome, #[lineExpr, shapeExpr])
  | (`Geometry.Theory.Intersects, #[lineExpr, shapeExpr]) =>
    -- No explicit intersection point — just make the shape visible
    -- and (if line is named) ensure the line exists.
    let some (constructStmt, _, _, _) ← shapeConstruct shapeExpr
      | return none
    -- If the first arg is a fvar Line, emit nothing else; otherwise
    -- include a placeholder line (best-effort).
    if (← readLineName? lineExpr).isSome then
      return some #[constructStmt]
    return some #[constructStmt]
  | _ => return none

end Geometry.Construction.Matchers
