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

/-- Walk through possible coercion wrappers to find the inner
shape-constructor application. Useful because `intersects segment A B`
elaborates with a Segment→Line coercion around `Segment.between A B`. -/
private partial def unwrapToShape (e : Expr) : Expr :=
  match e.getAppFnArgs with
  | (`Geometry.Theory.Segment.between, _)
  | (`Geometry.Theory.LineThrough.through, _)
  | (`Geometry.Theory.Ray.from_, _)
  | (`Geometry.Theory.Extension.past, _) => e
  | (_, args) =>
    -- Try each arg recursively; first match wins. Coercions typically
    -- wrap their target in the last arg.
    args.foldr (init := e) fun arg acc =>
      let recurse := unwrapToShape arg
      match recurse.getAppFnArgs with
      | (`Geometry.Theory.Segment.between, _)
      | (`Geometry.Theory.LineThrough.through, _)
      | (`Geometry.Theory.Ray.from_, _)
      | (`Geometry.Theory.Extension.past, _) => recurse
      | _ => acc

/-- Given a shape expression (segment/ray/line_through), produce the
`construct <name> := <head> A B` stmt that makes it visible, plus the
synthesized construct name. Unwraps coercions. Returns `none` if the
shape head isn't recognized. -/
private def shapeConstruct (shapeExpr : Expr) :
    MetaM (Option (Stmt × String × String × String)) := do
  let shapeExpr := unwrapToShape shapeExpr
  match shapeExpr.getAppFnArgs with
  | (`Geometry.Theory.Segment.between, #[a, b]) =>
    let some na ← readPointName? a | return none
    let some nb ← readPointName? b | return none
    let name := s!"seg_{na}_{nb}"
    return some (.construct name (.app "segment" [.name na.toString, .name nb.toString]),
                 "segment", na.toString, nb.toString)
  | (`Geometry.Theory.LineThrough.through, #[a, b]) =>
    let some na ← readPointName? a | return none
    let some nb ← readPointName? b | return none
    let name := lineAnchor na.toString nb.toString
    return some (.construct name (.app "line_through" [.name na.toString, .name nb.toString]),
                 "line_through", na.toString, nb.toString)
  | (`Geometry.Theory.Ray.from_, #[a, b]) =>
    let some na ← readPointName? a | return none
    let some nb ← readPointName? b | return none
    let name := s!"ray_{na}_{nb}"
    return some (.construct name (.app "ray" [.name na.toString, .name nb.toString]),
                 "ray", na.toString, nb.toString)
  | _ => return none

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
    let some (constructStmt, kind, aStr, bStr) ← shapeConstruct shapeExpr
      | return none
    return some #[
      constructStmt,
      assertN "incident" #[xStr, lStr],
      onShapeAssert kind aStr bStr xStr,
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
