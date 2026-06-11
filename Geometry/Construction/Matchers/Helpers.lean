/-
Geometry/Construction/Matchers/Helpers.lean — shared helpers for the
matcher files. Lifted from `FromProofState.lean` so each matcher can
import them without dragging in the full classifier.

Note: matchers reference constants like `Geometry.Theory.Point` via
single-backtick Name literals (NOT `` ``Foo.bar ``) so each matcher
file stays light — no transitive imports of the declaring modules.
The actual constants are looked up by name at classification time.
-/

import Lean
import Figures.Construction.DSL

namespace Geometry.Construction.Matchers

open Lean Meta
open Figures.Construction.DSL

/-- Is `e` an fvar whose declared type is `Geometry.Theory.Point`?
Returns the userName if yes. -/
def readPointName? (e : Expr) : MetaM (Option Lean.Name) := do
  let e ← instantiateMVars e
  unless e.isFVar do return none
  let decl ← e.fvarId!.getDecl
  let ty ← instantiateMVars decl.type
  if ty.isConstOf `Geometry.Theory.Point then
    return some decl.userName
  return none

/-- Is `e` an fvar whose declared type is `Geometry.Theory.Line`?
Returns the userName if yes. -/
def readLineName? (e : Expr) : MetaM (Option Lean.Name) := do
  let e ← instantiateMVars e
  unless e.isFVar do return none
  let decl ← e.fvarId!.getDecl
  let ty ← instantiateMVars decl.type
  if ty.isConstOf `Geometry.Theory.Line then
    return some decl.userName
  return none

/-- Read a list of Exprs as Point names; all-or-nothing. -/
def readPointArgs (es : Array Expr) : MetaM (Option (Array String)) := do
  let mut out : Array String := #[]
  for e in es do
    let some n ← readPointName? e | return none
    out := out.push n.toString
  return some out

/-- Build `Stmt.assert (.app head args)`. -/
def assertN (head : String) (args : Array String) : Stmt :=
  .assert (.app head (args.toList.map .name))

/-- Synthesize a stable line-anchor name for "line through B and C".
The lowering recognizes `incident P L` asserts and groups them by L;
emitting a stable name per (B, C) pair makes the constraint group
correctly. -/
def lineAnchor (b c : String) : String := s!"L_{b}_{c}"

/-- Read a `Finset Point` expression as a list of Point names.
Handles `{a, b, c}` (Insert/Singleton typeclass form). -/
partial def readFinsetPoints (e : Expr) : MetaM (Option (Array String)) := do
  let e ← instantiateMVars e
  match e.getAppFnArgs with
  -- `@Insert.insert α γ inst a s` — 5 args. Element at index 3, tail at 4.
  | (``Insert.insert, args) =>
    if args.size ≥ 5 then
      let some n ← readPointName? args[3]! | return none
      let some rest ← readFinsetPoints args[4]! | return none
      return some (#[n.toString] ++ rest)
    return none
  -- `@Singleton.singleton α γ inst a` — 4 args. Element at index 3.
  | (``Singleton.singleton, args) =>
    if args.size ≥ 4 then
      let some n ← readPointName? args[3]! | return none
      return some #[n.toString]
    return none
  | _ => return none

end Geometry.Construction.Matchers
