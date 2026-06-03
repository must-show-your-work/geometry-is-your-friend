/-
Geometry/Construction/Syntax.lean — Surface syntax for the
Construction DSL.

Provides a `construction { … }` term-level block whose body uses the
three-verb syntax sketched in `Geometry/Ch3/Prop/Pasch.lean` (L54-69):

  construction {
    exists P Q : Point
    assert distinct P Q
    construct lPQ := line_through P Q
  }

elaborates to the same `Construction` value you'd hand-build via
`{ stmts := #[.«exists» #["P","Q"] "Point", …] }`.

V1 scope (sufficient for "two points determine a line"):
- `exists name+ : Sort` — fresh objects of a given sort
- `assert head arg*` — flat function-applied constraint
- `construct name := head arg*` — derived object from a constructor

Out of scope, will be added when an example forces it: `¬` for
negation, numeric literals, nested expressions, multi-line statement
descriptions. Until then, hand-build the AST for those cases.
-/

import Geometry.Construction.DSL

namespace Geometry.Construction.DSL

open Lean

/-- Argument to a constraint head: just an identifier in V1. The
expression `head a b c` lowers to `.app "head" [.name "a", .name "b",
.name "c"]`. Numeric literals and nested expressions will land here
later when needed. -/
declare_syntax_cat constrArg
syntax ident : constrArg

declare_syntax_cat constructionStmt
-- `rawIdent` (not `ident`) for head positions so Greenberg keywords
-- like `distinct` and `collinear`, which are reserved as term-level
-- syntax in Geometry.Theory, still parse as construction heads here.
syntax "exists " ident+ " : " ident                      : constructionStmt
syntax "assert " rawIdent constrArg*                     : constructionStmt
syntax "assert " "¬" rawIdent constrArg*                 : constructionStmt
syntax "construct " ident " := " rawIdent constrArg*     : constructionStmt
-- `focus <name>` makes the named element (a segment / ray / line_through
-- construct, or an existential Line) the canonical horizontal axis of
-- the figure. Without `focus`, the alphabetically-earliest segment-like
-- construct is chosen as the axis. Sugar over `assert focus <name>`.
syntax "focus " ident                                    : constructionStmt
-- `hidden <name>+` marks one or more existing points as layout-only:
-- they still participate in the solver (and anchor lines, etc.) but
-- are not emitted as visible `.point` shapes and get no auto-label.
-- Sugar over `assert hidden <name> ...`.
syntax "hidden " ident+                                  : constructionStmt

syntax (name := constructionBlock) "construction" "{" constructionStmt* "}" : term

/-- Lift a constraint argument to a `ConstraintExpr` term. Single
identifiers become `.name "id"`; nothing else is handled yet. -/
private def argToExpr (s : TSyntax `constrArg) : MacroM (TSyntax `term) :=
  match s with
  | `(constrArg| $i:ident) =>
    let lit := Syntax.mkStrLit i.getId.toString
    `(Figures.ConstraintExpr.name $lit)
  | _ => Macro.throwUnsupported

/-- Build `[expr1, expr2, …]` from the parsed `constrArg`s. -/
private def argsListExpr (args : Array (TSyntax `constrArg)) : MacroM (TSyntax `term) := do
  let exprs ← args.mapM argToExpr
  `([$exprs,*])

/-- Convert one parsed statement to a `Stmt` term. Done as a helper
(not `macro_rules` on `constructionStmt`) because category splicing
doesn't chain through nested macro rules — the outer block macro has
to do the conversion explicitly. -/
private def stmtToTerm (s : TSyntax `constructionStmt) : MacroM (TSyntax `term) :=
  match s with
  | `(constructionStmt| exists $names:ident* : $sort:ident) => do
    let nameStrs := names.map (fun n => Syntax.mkStrLit n.getId.toString)
    let sortStr  := Syntax.mkStrLit sort.getId.toString
    `(Geometry.Construction.DSL.Stmt.«exists» #[$nameStrs,*] $sortStr)
  | `(constructionStmt| assert $head:ident $args:constrArg*) => do
    let headStr := Syntax.mkStrLit head.getId.toString
    let argsList ← argsListExpr args
    `(Geometry.Construction.DSL.Stmt.assert (Figures.ConstraintExpr.app $headStr $argsList))
  | `(constructionStmt| assert ¬ $head:ident $args:constrArg*) => do
    let headStr := Syntax.mkStrLit head.getId.toString
    let argsList ← argsListExpr args
    `(Geometry.Construction.DSL.Stmt.assert
        (Figures.ConstraintExpr.app "¬" [Figures.ConstraintExpr.app $headStr $argsList]))
  | `(constructionStmt| construct $name:ident := $head:ident $args:constrArg*) => do
    let nameStr := Syntax.mkStrLit name.getId.toString
    let headStr := Syntax.mkStrLit head.getId.toString
    let argsList ← argsListExpr args
    `(Geometry.Construction.DSL.Stmt.construct $nameStr (Figures.ConstraintExpr.app $headStr $argsList))
  | `(constructionStmt| focus $name:ident) => do
    let nameStr := Syntax.mkStrLit name.getId.toString
    `(Geometry.Construction.DSL.Stmt.assert
        (Figures.ConstraintExpr.app "focus" [Figures.ConstraintExpr.name $nameStr]))
  | `(constructionStmt| hidden $names:ident*) => do
    let nameExprs ← names.mapM (fun n => do
      let lit := Syntax.mkStrLit n.getId.toString
      `(Figures.ConstraintExpr.name $lit))
    `(Geometry.Construction.DSL.Stmt.assert
        (Figures.ConstraintExpr.app "hidden" [$nameExprs,*]))
  | _ => Macro.throwUnsupported

macro_rules
  | `(construction { $stmts:constructionStmt* }) => do
    let stmtTerms ← stmts.mapM stmtToTerm
    `({ stmts := #[$stmtTerms,*] : Geometry.Construction.DSL.Construction })


end Geometry.Construction.DSL
