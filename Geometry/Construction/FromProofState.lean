/-
Geometry/Construction/FromProofState.lean — classify a `LocalContext`
into a `DSL.Construction`. Each `Point`-typed local becomes an
`exists` stmt; each recognized hypothesis type (`Between`, `D ∈ ray …`,
`Distinct`, `Collinear`, `Angle`, …) becomes an `assert` stmt. Anything
unrecognized is silently dropped — graceful degradation, the figure
still renders the parts the classifier understood.
-/

import Geometry.Theory.Axioms
import Geometry.Theory.Constructors
import Geometry.Theory.Distinct
import Geometry.Theory.Collinear
import Geometry.Theory.Angle
import Geometry.Construction.DSL

namespace Geometry.Construction.FromProofState

open Lean Meta Figures
open Geometry.Construction.DSL

private def readPointName? (e : Expr) : MetaM (Option Lean.Name) := do
  let e ← instantiateMVars e
  unless e.isFVar do return none
  let decl ← e.fvarId!.getDecl
  let ty ← instantiateMVars decl.type
  if ty.isConstOf ``Geometry.Theory.Point then
    return some decl.userName
  return none

private def readPointArgs (es : Array Expr) : MetaM (Option (Array String)) := do
  let mut out : Array String := #[]
  for e in es do
    let some n ← readPointName? e | return none
    out := out.push n.toString
  return some out

private def assertN (head : String) (args : Array String) : Stmt :=
  .assert (.app head (args.toList.map .name))

/-- Synthesize a name for a "line through two points" anchor.
The lowering recognizes `incident P L` asserts and groups them by L;
emitting a stable synthetic name per (B, C) pair makes the constraint
group correctly. -/
private def lineAnchor (b c : String) : String := s!"L_{b}_{c}"

/-- Try to read a `Finset Point` expression as a list of Point names.
Handles `{a, b, c}` / `{a} ∪ {b, c}` / `insert a (insert b (singleton c))`
shapes — same as what `separate`/`distinct`'s elaborator produces. -/
private partial def readFinsetPoints (e : Expr) : MetaM (Option (Array String)) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  | (``Insert.insert, args) =>
    if args.size ≥ 4 then
      let some n ← readPointName? args[2]! | return none
      let some rest ← readFinsetPoints args[3]! | return none
      return some (#[n.toString] ++ rest)
    return none
  | (``Singleton.singleton, args) =>
    if args.size ≥ 3 then
      let some n ← readPointName? args[2]! | return none
      return some #[n.toString]
    return none
  | _ => return none

/-- Recognize a `Decl` whose type matches one of our known constraint
shapes; emit zero or more `Stmt`s. Conjunctions get walked recursively
so `Angle A B C` (= `distinct A B C ∧ ¬OppositeRay A B C`) splits into
its components. -/
private partial def classifyType (ty : Expr) : MetaM (Array Stmt) := do
  let ty ← instantiateMVars ty
  match ty.getAppFnArgs with
  | (``Geometry.Theory.Between, #[a, b, c]) =>
    let some args ← readPointArgs #[a, b, c] | return #[]
    return #[assertN "between" args]
  | (``Geometry.Theory.Distinct, #[s, _n]) =>
    let some pts ← readFinsetPoints s | return #[]
    return #[assertN "distinct" pts]
  | (``Geometry.Theory.Collinear, #[s]) =>
    let some pts ← readFinsetPoints s | return #[]
    return #[assertN "collinear" pts]
  | (``Geometry.Theory.OppositeRay, _) =>
    -- Skip for now — not a DSL primitive. A future pass can render
    -- opposite rays as a configuration anchor.
    return #[]
  | (``Membership.mem, args) =>
    -- `D ∈ <something>` — classify by the something's shape.
    if args.size < 5 then return #[]
    let elt := args[4]!
    let container := args[3]!
    match container.getAppFnArgs with
    | (``Geometry.Theory.LineThrough.through, #[b, c]) =>
      let some d ← readPointName? elt | return #[]
      let some nb ← readPointName? b | return #[]
      let some nc ← readPointName? c | return #[]
      let lineName := lineAnchor nb.toString nc.toString
      return #[
        .construct lineName (.app "line_through"
          [.name nb.toString, .name nc.toString]),
        assertN "incident" #[d.toString, lineName]
      ]
    | (``Geometry.Theory.Ray.from_, #[a, b]) =>
      let some p ← readPointName? elt | return #[]
      let some na ← readPointName? a | return #[]
      let some nb ← readPointName? b | return #[]
      return #[assertN "on_ray" #[p.toString, na.toString, nb.toString]]
    | (``Geometry.Theory.Segment.between, #[a, b]) =>
      let some p ← readPointName? elt | return #[]
      let some na ← readPointName? a | return #[]
      let some nb ← readPointName? b | return #[]
      return #[assertN "on_segment" #[p.toString, na.toString, nb.toString]]
    | _ => return #[]
  | (``And, #[l, r]) =>
    return (← classifyType l) ++ (← classifyType r)
  | (``Not, #[inner]) =>
    -- `B off ray A C` etc. Wrap each emitted constraint with a "¬" head.
    let inner ← classifyType inner
    return inner.map fun s => match s with
      | .assert (.app head args) _ => .assert (.app "¬" [.app head args]) ""
      | other => other
  | _ => return #[]

/-- Walk the current `LocalContext`; emit a `DSL.Construction` that
mirrors what the user could have hand-written as a `construction { … }`
block to describe the proof state. -/
def extract : MetaM Construction := do
  let lctx ← getLCtx
  let mut points : Array String := #[]
  let mut asserts : Array Stmt := #[]
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    if ty.isConstOf ``Geometry.Theory.Point then
      points := points.push decl.userName.toString
    else
      asserts := asserts ++ (← classifyType ty)
  let existsStmts : Array Stmt := if points.isEmpty then #[]
    else #[.«exists» points "Point"]
  return ⟨existsStmts ++ asserts⟩

end Geometry.Construction.FromProofState
