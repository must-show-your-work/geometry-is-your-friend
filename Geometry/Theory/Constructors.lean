import Geometry.Theory.Primitives
import Mathlib.Data.Set.Basic
import LeanTeX

/-!
# Constructors

Derived geometric objects built on `Point` + `Between`: segments, rays,
extensions, line-through-two-points, and intersections. Each line-part is
a typed `structure` parameterized by its defining points, with a
`@[reducible]` `carrier : Set Point` projection holding the underlying
disjunction-set Greenberg's original defs used.

`Membership Point X` and `CoeHead X (Set Point)` instances let these
behave transparently as sets — `P ∈ segment A B` and `segment A B ⊆ line A B`
work without manual coercion.

The surface syntax (`segment A B`, `ray A B`, etc., plus the `the X`
prefixed forms) is unchanged from the original Set-Point-based defs;
only the underlying types differ. The `on` macro_rules expand
`P on segment A B` to `P ∈ (segment A B)`.
-/

namespace Geometry.Theory

/-! ## Typed line-part structures

    Each structure carries a `Unit` token to keep it in `Type` (Lean's
    structure-is-Prop rule would otherwise fire on an empty record).
    Endpoints are *type-level* parameters, not fields — recoverable by
    unification at use sites.
-/

structure Segment (A B : Point) where
  type_token : Unit := ()

structure Ray (A B : Point) where
  type_token : Unit := ()

structure Extension (A B : Point) where
  type_token : Unit := ()

structure LineThrough (A B : Point) where
  type_token : Unit := ()

@[inline] def Segment.between (A B : Point) : Segment A B := ⟨()⟩
@[inline] def Ray.from_ (A B : Point) : Ray A B := ⟨()⟩
@[inline] def Extension.past (A B : Point) : Extension A B := ⟨()⟩
@[inline] def LineThrough.through (A B : Point) : LineThrough A B := ⟨()⟩

/-! ## LeanTeX rules — endpoints in textbook glyphs

Render each line-part by composing its endpoints under the matching
diacritic: `\overline` for segments, `\overrightarrow` for rays and
extensions (extensions are rays past the second endpoint), and
`\overleftrightarrow` for the line through two points.

Atoms at infinity BP — these are noun-phrase constructions; they
shouldn't get extra parens regardless of surrounding context. -/

private def renderEndpointPair (diacritic : String) (a b : Lean.Expr) :
    LeanTeX.LatexPrinterM LeanTeX.LatexData := do
  let pa ← LeanTeX.latexPP a
  let pb ← LeanTeX.latexPP b
  let inner := pa.latex.1 ++ pb.latex.1
  return LeanTeX.LatexData.atomString (diacritic ++ "{" ++ inner ++ "}")

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.Segment.between)
  | _, #[a, b] => renderEndpointPair "\\overline" a b

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.Ray.from_)
  | _, #[a, b] => renderEndpointPair "\\overrightarrow" a b

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.Extension.past)
  | _, #[a, b] => renderEndpointPair "\\overrightarrow" a b

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.LineThrough.through)
  | _, #[a, b] => renderEndpointPair "\\overleftrightarrow" a b

/-! ## Carriers — projection to `Set Point`

    Reducible defs that unfold to the same set-theoretic content as
    Greenberg's original `Segment`/`Ray`/`Extension`/`LineThrough`. The
    bodies are *literally* the old definitions — no semantic shift.
-/

@[reducible] def Segment.carrier {A B : Point} (_s : Segment A B) : Set Point :=
  {C | (A - C - B) ∨ A = C ∨ B = C}

@[reducible] def Extension.carrier {A B : Point} (_e : Extension A B) : Set Point :=
  {C | A - B - C ∧ A ≠ C ∧ B ≠ C}

@[reducible] def Ray.carrier {A B : Point} (_r : Ray A B) : Set Point :=
  {C | (A - C - B) ∨ A = C ∨ B = C} ∪ {C | A - B - C ∧ A ≠ C ∧ B ≠ C}

@[reducible] def LineThrough.carrier {A B : Point} (_L : LineThrough A B) : Set Point :=
  {C | C = A ∨ C = B ∨ A - C - B ∨ A - B - C ∨ C - A - B}

/-! ## Carrier-projection rules — render `x.carrier` exactly as `x`.

The CoeHead from a typed line-part to `Line` produces `Line.mk (x.carrier)`.
Combined with the `Line.mk` rule in `Primitives.lean` (which unwraps to its
arg) and these rules (which unwrap `x.carrier` to `x` itself), the chain
collapses to the typed line-part's own render — so `(segment A B : Line)`
emerges as just `\overline{AB}`. -/

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.Segment.carrier)
  | _, #[_, _, s] => latexPP s

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.Ray.carrier)
  | _, #[_, _, r] => latexPP r

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.Extension.carrier)
  | _, #[_, _, e] => latexPP e

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.LineThrough.carrier)
  | _, #[_, _, L] => latexPP L

/-! ## Pretty-printer unexpanders — proof states show the surface syntax

    Without these, goals render the elaborated form (e.g.
    `{ toSet := (Segment.between A B).carrier }`) which is unreadable.
    Each unexpander brings constructor applications back to surface form.
-/

@[app_unexpander Segment.between]
def Segment.between.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $A $B) => `(segment $A $B)
  | _ => throw ()

@[app_unexpander Ray.from_]
def Ray.from_.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $A $B) => `(ray $A $B)
  | _ => throw ()

@[app_unexpander Extension.past]
def Extension.past.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $A $B) => `(extension $A $B)
  | _ => throw ()

@[app_unexpander LineThrough.through]
def LineThrough.through.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $A $B) => `(line $A $B)
  | _ => throw ()

-- The Coe insertion from a line-part to `Line` produces
-- `Line.mk (X.carrier)`, which Lean prints as `{ toSet := X.carrier }`
-- (anonymous structure literal). The unexpanders below recognize the
-- carrier projection on line-parts and render it as `↑(segment A B)`
-- (etc.), so proof states stay readable.

@[app_unexpander Segment.carrier]
def Segment.carrier.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $s) => `(($s : Line))
  | _ => throw ()

@[app_unexpander Ray.carrier]
def Ray.carrier.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $r) => `(($r : Line))
  | _ => throw ()

@[app_unexpander Extension.carrier]
def Extension.carrier.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $e) => `(($e : Line))
  | _ => throw ()

@[app_unexpander LineThrough.carrier]
def LineThrough.carrier.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $L) => `(($L : Line))
  | _ => throw ()

-- Strip the `Line.mk` wrap when its argument is already an ascribed
-- `(X : Line)` form (which our carrier unexpanders produce). This
-- collapses `{ toSet := (segment A B : Line) }` back to `(segment A B : Line)`.
@[app_unexpander Line.mk]
def Line.mk.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ ($x : $_)) => `($x)
  | `($_ $x) => `(($x : Line))
  | _ => throw ()

/-! ## Membership instances -/

instance {A B : Point} : Membership Point (Segment A B) where
  mem s P := P ∈ s.carrier

instance {A B : Point} : Membership Point (Ray A B) where
  mem r P := P ∈ r.carrier

instance {A B : Point} : Membership Point (Extension A B) where
  mem e P := P ∈ e.carrier

instance {A B : Point} : Membership Point (LineThrough A B) where
  mem L P := P ∈ L.carrier

/-! ## `CoeHead` instances — typed line-parts behave as `Set Point` -/

instance {A B : Point} : CoeHead (Segment A B) (Set Point) where
  coe s := s.carrier

instance {A B : Point} : CoeHead (Ray A B) (Set Point) where
  coe r := r.carrier

instance {A B : Point} : CoeHead (Extension A B) (Set Point) where
  coe e := e.carrier

instance {A B : Point} : CoeHead (LineThrough A B) (Set Point) where
  coe L := L.carrier

/-! ## `CoeHead` to the abstract `Line`

    With `Line` now an opaque-ish wrapper around `Set Point`, line-parts
    coerce to `Line` by wrapping their carrier. This makes
    `ray A B ⊆ line A B`, `segment A B = L`, etc. work without the
    `(... : Set Point)` ascription — both sides land in `Line` via Coe.
-/

instance {A B : Point} : CoeHead (Segment A B) Line where
  coe s := ⟨s.carrier⟩

instance {A B : Point} : CoeHead (Ray A B) Line where
  coe r := ⟨r.carrier⟩

instance {A B : Point} : CoeHead (Extension A B) Line where
  coe e := ⟨e.carrier⟩

instance {A B : Point} : CoeHead (LineThrough A B) Line where
  coe L := ⟨L.carrier⟩

/-! ## Cross-line-part comparison auto-coercion — bottom of the warren

    `Eq` / `Ne` / `⊆` / `∩` / `∪` between two typed line-parts of different
    shapes (e.g. `segment A B = segment B C`) fail to elaborate by default
    because Lean picks the LHS type and refuses to coerce the RHS to a
    common ambient.

    **What we tried, and why each failed:**

    1. `macro_rules` matching `$lhs = $rhs`: never fires. `=` / `≠` / `⊆`
       go through Lean's `binrel%` machinery which intercepts the syntax
       below the macro layer. Term-level `macro_rules` never sees these.

    2. Replacing `CoeHead X Line` with `Coe X Line` (so Lean's `binrel%`
       might use it to find a common type): hits "instance does not
       provide concrete values for (semi-)out-params" at the instance
       declaration. The line-parts being parameterized by `A B : Point`
       means a `Coe (Segment A B) Line` instance has free A and B that
       Lean's typeclass resolver can't pin down at search time.

    3. `term_elab` / `binop_elab` hook on `Eq` directly: would require
       writing a Lean elaborator extension that inspects elaborated
       argument types, recognizes the line-part-vs-line-part pattern,
       and inserts `CoeHead.coe` to `Line` on both sides. ~80 LOC of
       elaborator code, touches Lean's elaboration loop, and requires
       intimate knowledge of how `binrel%` / `Lean.Elab.BinOp` interact
       with `Lean.Meta.coercedTo?` — interface that's not stable across
       Lean versions.

    **Convention going forward:** at the ~25 cross-line-part comparison
    sites in the codebase, anchor the LHS with `(... : Line)`. The RHS
    auto-coerces via `CoeHead`. Example:
    ```
    (segment A B : Line) = segment B A   -- ✓ — LHS anchors, RHS auto-coerces
    (segment A B : Line) ⊆ line A B      -- ✓ — same pattern
    segment A B = segment B C            -- ✗ — Lean picks Segment A B as type, can't coerce
    ```

    If the elaborator extension ever becomes worth ~80 LOC + the
    Lean-internal API risk, the right hook point is `binrel%` / each
    operator's elabFn. We've exhausted the cheaper options.
-/

/-! ## Cross-type subset is via explicit `(↑x : Set Point)` ascription.

    `HasSubset` is a unary typeclass — same type both sides — so writing
    `ray A B ⊆ line A B` (different typed structures) doesn't elaborate.
    The `CoeHead X (Set Point)` instances above let call sites coerce
    explicitly: `(↑(ray A B) : Set Point) ⊆ line A B` (or the symmetric
    ascription on the RHS). Affects only the few subset-between-line-parts
    lemmas (1.0.8, 2.0.4); the typical `P on x` / `s ≠ L` use cases work
    without ascription.
-/

/-! ## `mem_def` bridges — `Iff.rfl` to the underlying disjunction

    Tagged `@[simp, obvious]` so tactics see through to the same shape
    Greenberg's set-based defs exposed directly.
-/

@[simp, obvious] theorem Segment.mem_def {A B : Point} {s : Segment A B} {P : Point} :
  P ∈ s ↔ (A - P - B) ∨ A = P ∨ B = P := Iff.rfl

@[simp, obvious] theorem Ray.mem_def {A B : Point} {r : Ray A B} {P : Point} :
  P ∈ r ↔ ((A - P - B) ∨ A = P ∨ B = P) ∨ (A - B - P ∧ A ≠ P ∧ B ≠ P) := Iff.rfl

@[simp, obvious] theorem Extension.mem_def {A B : Point} {e : Extension A B} {P : Point} :
  P ∈ e ↔ A - B - P ∧ A ≠ P ∧ B ≠ P := Iff.rfl

@[simp, obvious] theorem LineThrough.mem_def {A B : Point} {L : LineThrough A B} {P : Point} :
  P ∈ L ↔ P = A ∨ P = B ∨ A - P - B ∨ A - B - P ∨ P - A - B := Iff.rfl

/-! ## Coercion-membership bridges

    `P ∈ (↑x : Line) ↔ P ∈ x` for each line-part. Both sides reduce to
    `P ∈ x.carrier`, but they go through different `Membership` instances
    (Line's via `.toSet`, line-part's via `.carrier`), so simp doesn't
    unify them without an explicit bridge.

    Tagged `@[simp, obvious]` so `Line.mem_inter` etc. can rewrite a goal
    like `X ∈ L ∩ ray A B` into `X ∈ L ∧ X ∈ ray A B` and have the second
    conjunct match a `X ∈ ray A B` hypothesis. -/

@[simp, obvious] theorem Segment.mem_coe_line {A B P : Point} {s : Segment A B} :
  P ∈ (↑s : Line) ↔ P ∈ s := Iff.rfl

@[simp, obvious] theorem Ray.mem_coe_line {A B P : Point} {r : Ray A B} :
  P ∈ (↑r : Line) ↔ P ∈ r := Iff.rfl

@[simp, obvious] theorem Extension.mem_coe_line {A B P : Point} {e : Extension A B} :
  P ∈ (↑e : Line) ↔ P ∈ e := Iff.rfl

@[simp, obvious] theorem LineThrough.mem_coe_line {A B P : Point} {L : LineThrough A B} :
  P ∈ (↑L : Line) ↔ P ∈ L := Iff.rfl

/-! ## Surface syntax — unchanged from the Set-Point era -/

syntax:max "segment " term:max term:max : term
syntax:max "ray " term:max term:max : term
syntax:max "extension " term:max term:max : term
syntax:max "line " term:max term:max : term

syntax:1000 "the " "segment " term:max term:max : term
syntax:1000 "the " "ray " term:max term:max : term
syntax:1000 "the " "extension " term:max term:max : term
syntax:1000 "the " "line " term:max term:max : term

-- Extend the `on` macro_rules (declared in `Primitives.lean`) — surface
-- shape unchanged, expansion now targets `Membership.mem` on the typed
-- value (`Segment.between A B` etc.).
macro_rules (kind := onNotation)
  | `($P on segment $A $B) => `($P ∈ Segment.between $A $B)
  | `($P on ray $A $B) => `($P ∈ Ray.from_ $A $B)
  | `($P on extension $A $B) => `($P ∈ Extension.past $A $B)
  | `($P on line $A $B) => `($P ∈ LineThrough.through $A $B)
  | `($P on $L) => `($P ∈ $L)

-- Standalone constructors (and `the X` forms) elaborate to typed values.
macro_rules
  | `(segment $A $B) => `(Segment.between $A $B)
  | `(ray $A $B) => `(Ray.from_ $A $B)
  | `(extension $A $B) => `(Extension.past $A $B)
  | `(line $A $B) => `(LineThrough.through $A $B)
  | `(the segment $A $B) => `(Segment.between $A $B)
  | `(the ray $A $B) => `(Ray.from_ $A $B)
  | `(the extension $A $B) => `(Extension.past $A $B)
  | `(the line $A $B) => `(LineThrough.through $A $B)

/-! ## Intersections -/

@[reducible, obvious.intersects]
def Intersects (L M : Line) (X : Point) : Prop := L ∩ M = ({X} : Line)

/-- Bare form of `L intersects M` — asserts the intersection is non-empty (i.e.
    `L` and `M` share *at least one* point, allowing the "L coincides with M"
    case). Kept as an opaque `def` so the goal stays readable; the unexpander
    below renders this as `L intersects M` in proof states.

    Going from this to a unique intersection point (`L intersects M at X`)
    requires extra work — typically `via lemma 3.0.1` for lines,
    which uses `line_trichotomy` to rule out coincidence. -/
def IntersectsSome (L M : Line) : Prop := ∃ P, P ∈ L ∧ P ∈ M

/-- Extract a point in the intersection from a bare `intersects` hypothesis.
    Note: the returned `X` is *some* shared point, not necessarily a unique one. -/
lemma IntersectsSome.intersection_point {L M : Line} (h : IntersectsSome L M)
  : ∃ X, X ∈ L ∧ X ∈ M := h

/-- Forget the witness: `L intersects M at X` ⇒ `L intersects M`. Use via dot
    notation as `h.bare` at call sites where the bare (witness-free) form is
    expected. -/
theorem Intersects.bare {L M : Line} {X : Point}
  (h : Intersects L M X) : IntersectsSome L M := by
  refine ⟨X, ?_, ?_⟩
  · have : X ∈ (L ∩ M : Line) := by rw [h]; exact rfl
    exact this.1
  · have : X ∈ (L ∩ M : Line) := by rw [h]; exact rfl
    exact this.2

/-- Bare intersection is symmetric. Tagged `@[symm]` so the `symm` tactic picks
    it up; `h.symm` works via dot notation. -/
@[symm] theorem IntersectsSome.symm {L M : Line}
  (h : IntersectsSome L M) : IntersectsSome M L := by
  obtain ⟨X, hL, hM⟩ := h
  exact ⟨X, hM, hL⟩


-- Syntax for "L intersects M at X" (specific intersection point) and the bare
-- form "L intersects M" asserting a unique shared point exists.
syntax:50 (name := intersectsAt) term:51 " intersects " term:51 " at " term:50 : term
syntax:50 (name := intersectsBare) term:51 " intersects " term:51 : term

macro_rules (kind := intersectsAt)
  | `($L intersects $M at $X) => `(Intersects $L $M $X)

macro_rules (kind := intersectsBare)
  | `($L intersects $M) => `(IntersectsSome $L $M)

-- Pretty-print `IntersectsSome L M` as `L intersects M` so the goal stays readable
@[app_unexpander IntersectsSome]
def IntersectsSome.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $L $M) => `($L intersects $M)
  | _ => throw ()

/-! ## LeanTeX rules — `Intersects L M X` / `IntersectsSome L M` -/

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.Intersects)
  | _, #[l, m, x] => do
    let pl ← latexPP l
    let pm ← latexPP m
    let px ← latexPP x
    return pl.protect 50
        ++ LatexData.atomString " \\text{ intersects } " ++ pm.protect 50
        ++ LatexData.atomString " \\text{ at } " ++ px.protect 50

open LeanTeX in
latex_pp_app_rules (const := Geometry.Theory.IntersectsSome)
  | _, #[l, m] => do
    let pl ← latexPP l
    let pm ← latexPP m
    return pl.protect 50
        ++ LatexData.atomString " \\text{ intersects } " ++ pm.protect 50

/-! ## Examples -/

section Examples
variable (A B P : Point) (L M : Line) (X : Point)

example : (P on segment A B) ↔ (P ∈ Segment.between A B) := Iff.rfl
example : (P on ray A B) ↔ (P ∈ Ray.from_ A B) := Iff.rfl
example : (P on extension A B) ↔ (P ∈ Extension.past A B) := Iff.rfl
example : (P on line A B) ↔ (P ∈ LineThrough.through A B) := Iff.rfl
example : (segment A B) = Segment.between A B := rfl
example : (the segment A B) = Segment.between A B := rfl
example : (L intersects M at X) ↔ (Intersects L M X) := Iff.rfl
example : (L intersects M) ↔ (IntersectsSome L M) := Iff.rfl

-- `symm` tactic + dot notation for the bare intersection.
example {L M : Line} (h : L intersects M) : M intersects L := by symm; exact h
example {L M : Line} (h : L intersects M) : M intersects L := h.symm
end Examples

end Geometry.Theory
