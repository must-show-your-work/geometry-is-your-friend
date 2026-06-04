import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import LeanTeX

namespace Geometry.Theory

/-- A point is the fundamental, opaque type we're working with. -/
axiom Point : Type

/-- Greenberg reasons classically throughout. Granting decidable equality on `Point`
    via `Classical.decEq` lets us use `Finset Point` and the associated decidable
    membership/cardinality machinery. -/
noncomputable instance : DecidableEq Point := Classical.decEq Point

structure Line where
  toSet : Set Point

instance : Membership Point Line where
  mem L P := P ∈ L.toSet

instance : HasSubset Line where
  Subset L M := L.toSet ⊆ M.toSet

instance : HasSSubset Line where
  SSubset L M := L.toSet ⊂ M.toSet

instance : Inter Line where
  inter L M := ⟨L.toSet ∩ M.toSet⟩

instance : Union Line where
  union L M := ⟨L.toSet ∪ M.toSet⟩

instance : EmptyCollection Line where
  emptyCollection := ⟨∅⟩

instance : Singleton Point Line where
  singleton p := ⟨{p}⟩

@[simp, obvious] theorem Line.mem_def {L : Line} {P : Point} : P ∈ L ↔ P ∈ L.toSet := Iff.rfl

@[simp, obvious] theorem Line.subset_def {L M : Line} : L ⊆ M ↔ L.toSet ⊆ M.toSet := Iff.rfl

@[simp, obvious] theorem Line.ssubset_def {L M : Line} : L ⊂ M ↔ L.toSet ⊂ M.toSet := Iff.rfl

@[simp, obvious] theorem Line.inter_toSet (L M : Line) : (L ∩ M).toSet = L.toSet ∩ M.toSet := rfl

@[simp, obvious] theorem Line.union_toSet (L M : Line) : (L ∪ M).toSet = L.toSet ∪ M.toSet := rfl

@[simp, obvious] theorem Line.empty_toSet : (∅ : Line).toSet = ∅ := rfl

@[simp, obvious] theorem Line.singleton_toSet (P : Point) : ({P} : Line).toSet = {P} := rfl

@[ext] theorem Line.ext_set {L M : Line} (h : L.toSet = M.toSet) : L = M := by
  cases L; cases M; congr

theorem Line.eq_iff_toSet {L M : Line} : L = M ↔ L.toSet = M.toSet :=
  ⟨fun h => by rw [h], Line.ext_set⟩

@[simp, obvious] theorem Line.singleton_eq_singleton {P Q : Point} :
    ({P} : Line) = ({Q} : Line) ↔ P = Q := by
  rw [Line.eq_iff_toSet]; simp [Line.singleton_toSet, Set.singleton_eq_singleton_iff]

@[simp, obvious] theorem Line.mem_singleton {P Q : Point} :
    P ∈ ({Q} : Line) ↔ P = Q := by
  simp [Line.mem_def]

theorem Line.inter_comm (L M : Line) : L ∩ M = M ∩ L := by
  ext; simp [Set.mem_inter_iff, And.comm]

theorem Line.eq_of_subset {L M : Line} (h₁ : L ⊆ M) (h₂ : M ⊆ L) : L = M :=
  Line.ext_set (Set.Subset.antisymm h₁ h₂)

@[simp, obvious] theorem Line.mem_inter {L M : Line} {P : Point} :
    P ∈ L ∩ M ↔ P ∈ L ∧ P ∈ M := Set.mem_inter_iff P L.toSet M.toSet

@[simp, obvious] theorem Line.mem_union {L M : Line} {P : Point} :
    P ∈ L ∪ M ↔ P ∈ L ∨ P ∈ M := Set.mem_union P L.toSet M.toSet

@[simp, obvious] theorem Line.not_mem_empty {P : Point} : P ∉ (∅ : Line) := by
  simp [Line.mem_def]

syntax:50 (name := onNotation) term:51 " on " term:50 : term

macro_rules (kind := onNotation)
  | `($P on $L) => `($P ∈ $L)

-- Goal-state display: `Line` membership unfolds via the instance body
-- (`mem L P := P ∈ L.toSet`), which leaks `.toSet` into proof states like
-- `P ∈ (segment A B).toSet`. The unexpander below strips the projection
-- so `Line.toSet L` renders as just `L`, and the surrounding membership
-- collapses back to `P ∈ L` (further turned into `P on L` by the
-- `Membership.mem` delab below).
@[app_unexpander Geometry.Theory.Line.toSet]
def Line.toSet.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $L) => `($L)
  | _        => throw ()

-- Render `P ∈ L.toSet` (the unfolded form of Line membership — Lean
-- inlines the `instance Membership Point Line` body before delab sees
-- it, so the type arg is `Set Point`, not `Line`) as `P on L`. We
-- detect the Line layer via the *collection* shape (`Line.toSet X`).
open Lean PrettyPrinter.Delaborator SubExpr in
@[app_delab Membership.mem]
def delabMembershipOnLine : Delab := do
  let e ← getExpr
  guard <| e.isAppOfArity ``Membership.mem 5
  let collection := e.getArg! 3
  guard <| collection.isAppOfArity ``Geometry.Theory.Line.toSet 1
  let element ← withNaryArg 4 delab
  let lineStx ← withNaryArg 3 (withNaryArg 0 delab)
  `($element on $lineStx)

notation:80 P:81 " off " L:81 => P ∉ L
notation:80 L:81 " has " P:81 => P ∈ L
notation:80 L:81 " avoids " P:81 => P ∉ L

axiom Between : Point -> Point -> Point -> Prop

-- Ed: In the text, the author uses `*`, but Lean reserves that, so I've chosen `-`. `∗` is available, but I don't want
-- to type `\ast` every time.
syntax:65 (name := dashChain)
  term:66 " - " term:66 " - " term:66 (" - " term:66)* : term

macro_rules (kind := dashChain)
  | `($a:term - $b:term - $c:term) => `(Between $a $b $c)

open Lean PrettyPrinter.Delaborator SubExpr in
@[app_delab Geometry.Theory.Between]
def delabBetween : Delab := do
  guard <| (← getExpr).isAppOfArity ``Geometry.Theory.Between 3
  let a ← withNaryArg 0 delab
  let b ← withNaryArg 1 delab
  let c ← withNaryArg 2 delab
  `($a - $b - $c)

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.Between)
  | _, #[a, b, c] => do
    let pa ← latexPP a
    let pb ← latexPP b
    let pc ← latexPP c
    return pa.protectRight 50
        ++ LatexData.binOp " - " .none 50
        ++ pb.protect 50
        ++ LatexData.binOp " - " .none 50
        ++ pc.protectLeft 50

/-! ## LeanTeX const rules — strip the `Geometry.Theory.` namespace for the
    two opaque types so they render as `\text{Point}` and `\text{Line}`
    rather than `\text{Geometry.Theory.Point}`. -/

open LeanTeX in
latex_pp_const_rule Geometry.Theory.Point := return LatexData.atomString "\\text{Point}"

open LeanTeX in
latex_pp_const_rule Geometry.Theory.Line := return LatexData.atomString "\\text{Line}"

/-! ## LeanTeX rule — `Line.mk x` renders as just `x`. Lean's
    `(carrier : Line)` coercion produces `Line.mk (X.carrier)`; pairing
    this with the carrier-projection rules in `Constructors.lean` makes
    `(segment A B : Line)` render as `\overline{AB}`. -/

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.Line.mk)
  | _, #[x] => latexPP x

/-! ## LeanTeX override — gang consecutive same-type `∀` binders.

LeanTeX's upstream `forallE` printer (Builtins.lean:92) renders one
binder at a time, so `∀ A B C : Point, P` comes out as
`∀ A : Point, ∀ B : Point, ∀ C : Point, P`. We override only the
pure-forall case (proposition, non-arrow, non-pi) and gang consecutive
binders whose domain is structurally equal. Everything else
(implications, function arrows, Π-types) falls through to the upstream
rule via `failure`.

The dispatch lookup in `LeanTeX.latexPPFor` iterates handlers in
reverse-definition order: later registrations win first. Since this
giyf-side rule is registered after `Geometry` imports LeanTeX, it
gets tried before the builtin and we can pick our cases. -/

/-- Walk a chain of `∀ _ : dom, …` forallE's whose binding domain
matches `dom` (structurally), accumulating their binder names, then
invoke the continuation `k` with the names and the residual body —
all within the stacked `withBindingBodyUnusedName` scopes so the
freshly-introduced fvars stay in the local context for the body's
own LaTeX render. -/
private partial def gangSameTypeForall
    (dom : Lean.Expr) (e : Lean.Expr) (acc : Array Lean.Name)
    (k : Array Lean.Name → Lean.Expr → LeanTeX.LatexPrinterM LeanTeX.LatexData) :
    LeanTeX.LatexPrinterM LeanTeX.LatexData :=
  match e with
  | .forallE _ dom' _ _ =>
    if dom == dom' then
      LeanTeX.withBindingBodyUnusedName e fun name body =>
        gangSameTypeForall dom body (acc.push name) k
    else
      k acc e
  | _ => k acc e

open LeanTeX in
latex_pp_rules (kind := forallE) | e => do
  -- Take the pure-forall branch only: `e` must be a proposition, not
  -- an arrow (which is implication when the domain is a prop, or a
  -- function type otherwise), and not a Π-type over Sort.
  let prop? ← try Lean.Meta.isProp e catch _ => pure false
  guard prop?
  guard !e.isArrow
  let dom := e.bindingDomain!
  -- Π-type sanity: if the domain is a prop, fall through to the upstream
  -- printer (which renders the `arrow? ∧ domProp?` case as implication).
  let domProp? ← try Lean.Meta.isProp dom catch _ => pure true
  guard !domProp?
  let pdom ← latexPP dom
  -- Open the first binder and collect any consecutive same-type
  -- followers. The continuation runs INSIDE every introduced fvar's
  -- scope so the body's render sees them in the local context.
  withBindingBodyUnusedName e fun firstName body0 => do
    gangSameTypeForall dom body0 #[firstName] fun names residual => do
      let pbody ← latexPP residual
      let nameStr := " ".intercalate (names.toList.map Lean.Name.toLatex)
      let binder :=
        if (← read).omitBinders then LatexData.atomString ""
        else " : " ++ pdom.resetBP .Infinity .Infinity
      let pall := s!"\\forall {nameStr}" ++ binder ++ ",\\ " ++ pbody
      return pall |>.resetBP (lbp := .Infinity) |>.mergeBP (rbp := .NonAssoc 0)

/-! ## LeanTeX rule — list literals render as `[A, B, C, …]`. Standalone
    rule rather than a Geometry concern; lives here because List is a
    core Lean type that we use throughout (Arrangement, etc.) and
    LeanTeX upstream doesn't ship a rule. Mirrors the cons/nil walker
    pattern in Arrangement.lean. -/

/-- Walk a cons-chain and split it into `(literal-prefix-elements, optional
non-literal tail expression)`. The walker stops at the first node that isn't
a `List.cons` or `List.nil`; if it's neither, the tail is returned as the
non-literal `Some Expr` so the printer can emit `[A, B, …xs]` instead of
giving up. Returns `none` only when there's truly nothing to render
(empty acc and the node isn't a list constructor) — which can't happen
from a successful `List.cons` rule entry. -/
private partial def listConsSpine (e : Lean.Expr) (acc : Array Lean.Expr) :
    Array Lean.Expr × Option Lean.Expr :=
  match Lean.Expr.getAppFnArgs e with
  | (``List.cons, args) =>
    if args.size ≥ 3 then listConsSpine args[2]! (acc.push args[1]!)
    else (acc, some e)
  | (``List.nil, _) => (acc, none)
  | _ => (acc, some e)

open LeanTeX in
latex_pp_app_rules (const := List.cons)
  | e, _ => do
    let (elems, tail?) := listConsSpine e #[]
    if elems.isEmpty then failure
    let texs ← elems.mapM latexPP
    let body := LatexData.intercalate ", " texs
    let body := match tail? with
      | none => body
      | some _ => body ++ LatexData.atomString ", \\ldots"
    return (LatexData.atomString "[") ++ body ++ (LatexData.atomString "]")

open LeanTeX in
latex_pp_app_rules (const := List.nil)
  | _, _ => return LatexData.atomString "[]"

/- Examples -/

section Examples
variable (P : Point) (L : Line) (A B C : Point)

example : (P on L) ↔ (P ∈ L) := Iff.rfl
example : (P off L) ↔ (P ∉ L) := Iff.rfl
example : (L has P) ↔ (P ∈ L) := Iff.rfl
example : (L avoids P) ↔ (P ∉ L) := Iff.rfl
example : (A - B - C) ↔ Between A B C := Iff.rfl
end Examples

end Geometry.Theory
