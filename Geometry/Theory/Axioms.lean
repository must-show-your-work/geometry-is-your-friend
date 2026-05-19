/- The core geometric theory presented in the text is contained here as simple structures/axia taken as needed into
proofs. -/

import Geometry.Tactics
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert

import Mathlib.Tactic.Lemma  -- explicitly bring in Mathlib's bare-`lemma` syntax
import Geometry.Theory.Distinct
import Atlas

namespace Geometry.Theory

/-- A point is the fundamental, opaque type we're working with. -/
axiom Point : Type

/-- Greenberg reasons classically throughout. Granting decidable equality on `Point`
    via `Classical.decEq` lets us use `Finset Point` and the associated decidable
    membership/cardinality machinery. -/
noncomputable instance : DecidableEq Point := Classical.decEq Point

/-- Ed: In the text, the author ends up using the 'Line is a Set of points' to define segments, rays, and implicitly
uses the intuitive idea ("A line is the set of collinear points that contain at least two known points"). However, Ch2
uses an opaque 'Line' type and reasons only about it's properties without definition. I try to replicate this in my
implementation of Ch2, but do define it as a set 'up front' -/
@[reducible] def Line := Set Point

-- TODO: Review binding values for all this notation
syntax:50 (name := onNotation) term:51 " on " term:50 : term

-- Macro rules for "on" notation - we need to specify these rules incrementally, so that
-- I can introduce collinear as a definition.
macro_rules (kind := onNotation)
  | `($P on $L) => `($P ∈ $L)


---- COLLINEARITY (FINITE) AND POINTWISE (INFINITE)

/-- Collinear: finite set of points on a common line -/
def Collinear (points : Finset Point) : Prop := ∃ L : Line, ∀ p ∈ points, p ∈ L

-- Syntax: collinear A B C (space-separated)
syntax "collinear" ident+ : term

macro_rules
  | `(collinear $x $xs*) => do
      let allArgs := #[x] ++ xs
      let last := allArgs[allArgs.size - 1]!
      let front := allArgs.pop
      let mut acc ← `((Singleton.singleton $last : Finset _))
      for y in front.reverse do
        acc ← `(insert $y $acc)
      `(Collinear $acc)

-- Pretty printer: TODO restore after Finset-literal unexpander is written

-- Extract the line from collinearity
noncomputable def Collinear.line {points : Finset Point} (h : Collinear points) : Line := Classical.choose h

-- Natural projections from the Collinear def — not book content, not atlas'd.
lemma Collinear.on_line {points : Finset Point} (h : Collinear points)
  : ∀ p ∈ points, p on h.line := Classical.choose_spec h

@[simp] lemma Collinear.mem
  {points : Finset Point} (h : Collinear points) (p : Point) (hp : p ∈ points := by simp)
  : p on h.line := h.on_line p hp

example : collinear A B C ↔ ∃ L : Line, A on L ∧ B on L ∧ C on L := by
  constructor
  · intro colABC; use colABC.line;
    exact ⟨colABC.mem A, colABC.mem B, colABC.mem C⟩
  · rintro ⟨L, AonL, BonL, ConL⟩
    use L
    intro P PinABC
    simp only [Finset.mem_insert, Finset.mem_singleton] at PinABC
    rcases PinABC with eq | eq | eq
    repeat rwa [eq]

---- END COLLINEARITY

notation:80 P:81 " off " L:81 => P ∉ L
notation:80 L:81 " has " P:81 => P ∈ L
notation:80 L:81 " avoids " P:81 => P ∉ L

-- -- GEOMETRIC AXIOMS

-- -- -- INCIDENCE GEOMETRY

-- p. 69-70, Ed. The author provides these as very terse statements, I've tried to give informal
-- respellings as documentation.
/--
For any two distinct points P and Q, there exists a unique line L which has P and Q
-/
atlas axiom I.1 "Two distinct points determine a unique line through them"
  : ∀ P Q : Point, P ≠ Q -> ∃! L : Line, (P on L) ∧ (Q on L)
attribute [simp] «Two distinct points determine a unique line through them»

/-- For any line, there are at least two distinct points on it -/
atlas axiom I.2 "Every line contains at least two distinct points"
  : ∀ L : Line, ∃ A B : Point, A ≠ B ∧ (A on L) ∧ (B on L)
attribute [simp] «Every line contains at least two distinct points»

/-- There exists three distinct points not on any single line ("There exists
three non-collinear points", but without mentioning the undefined notion of collinearity) -/
atlas axiom I.3 "There exist three points not all lying on a common line"
  : ∃ A B C : Point, (A ≠ B ∧ A ≠ C ∧ B ≠ C) ∧ (∀ (L : Line), (A on L) → (B on L) → (C off L))
attribute [simp] «There exist three points not all lying on a common line»

/--
p.70 "Three ... lines ... are _concurrent_ if there exists a point incident with all of them"

Ed. Author technically makes this apply to any number of lines, if it ever comes up maybe it's worth
a refactor to any finite set of lines?
-/
@[reducible] def Concurrent (L M N : Line) : Prop :=
    ∃ P : Point, (P on L) ∧ (P on M) ∧ (P on N)

/--
p. 20, "Two lines `l` and `m` are parallel if they do not intersect, i.e., if no point lies on both
of them. We denote this by `l ‖ m`"

p. 70, "Lines `l` and `m` are _parallel_ if they are distinct lines and no point is incident to both
of them."

Ed. This gets defined twice, the definitions are equivalent
-/
@[reducible] def Parallel (L M : Line) : Prop := L ≠ M ∧ ∀ P : Point, ¬((P on L) ∧ (P on M))

notation:20 L " ∥ " M => Parallel L M
notation:20 L " ∦ " M => ¬(Parallel L M)


/- BETWEENNESS GEOMETRY -/

axiom Between : Point -> Point -> Point -> Prop
-- Ed: In the text, the author uses `*`, but Lean reserves that, so I've chosen `-`. `∗` is available, but I don't want
-- to type `\ast` every time.
notation:65 A:66 " - " B:66 " - " C:65 => Between A B C
-- Segment, Ray, Extension, LineThrough

/- Betweenness lets us define line-parts -/
@[reducible] def Segment (A B : Point) := {C | (A - C - B) ∨ A = C ∨ B = C}
@[reducible] def Extension (A B : Point) := {C | A - B - C ∧ A ≠ C ∧ B ≠ C}
@[reducible] def Ray (A B : Point) := (Segment A B) ∪ (Extension A B)
@[reducible] def LineThrough (A B : Point) := {C | C = A ∨ C = B ∨ A - C - B ∨ A - B - C ∨ C - A - B}

syntax:max "segment " term:max term:max : term
syntax:max "ray " term:max term:max : term
syntax:max "extension " term:max term:max : term
syntax:max "line " term:max term:max : term

syntax:1000 "the " "segment " term:max term:max : term
syntax:1000 "the " "ray " term:max term:max : term
syntax:1000 "the " "extension " term:max term:max : term
syntax:1000 "the " "line " term:max term:max : term

-- Re-running
macro_rules (kind := onNotation)
  | `($P on segment $A $B) => `($P ∈ Segment $A $B)
  | `($P on ray $A $B) => `($P ∈ Ray $A $B)
  | `($P on extension $A $B) => `($P ∈ Extension $A $B)
  | `($P on line $A $B) => `($P ∈ LineThrough $A $B)
  | `($P on $L) => `($P ∈ $L)

-- Macro rules for standalone geometric objects (without "the")
macro_rules
  | `(segment $A $B) => `(Segment $A $B)
  | `(ray $A $B) => `(Ray $A $B)
  | `(extension $A $B) => `(Extension $A $B)
  | `(line $A $B) => `(LineThrough $A $B)
  | `(the segment $A $B) => `(Segment $A $B)
  | `(the ray $A $B) => `(Ray $A $B)
  | `(the extension $A $B) => `(Extension $A $B)
  | `(the line $A $B) => `(LineThrough $A $B)



/--
p.108a "If A - B - C, then A,B,C are distinct points on the same line...
-/
atlas axiom B-1a "A-B-C implies A B C are distinct and collinear"
  {A B C : Point} : A - B - C -> distinct A B C ∧ collinear A B C
attribute [simp] «A-B-C implies A B C are distinct and collinear»


/--
p.108b ... and [A - B - C iff] C - B - A.""

Ed. Note, I separated these parts of the axiom to make rewriting
a bit easier. The author even notes, "The second part (C * B * A) makes the obvious remark
that 'betwen A and C' means the same as 'between C and A'" Making it a separate axiom means
I won't have to dig it out of the pile of parts that is 1a.
-/
atlas axiom B-1b "Betweenness Commutativity"
  {A B C : Point} : A - B - C ↔ C - B - A
attribute [simp] «Betweenness Commutativity»

/-- Endpoint-reversal projection of B-1b — exposes B-1b's commutativity
    via dot notation: `BCD.symm` instead of `(«Betweenness Commutativity»).mp BCD`.
    Not atlas-tagged (this is a structural projection on the underlying
    `Between` relation, not book content). -/
def Between.symm {A B C : Point} (h : A - B - C) : C - B - A :=
  («Betweenness Commutativity»).mp h


/-- `normalize_eq` walks the local context and flips `=` / `≠` hypotheses between
    free variables so the LHS comes lex-before the RHS by user-name. Useful when
    a downstream tactic (`simp`, `tauto`) doesn't know about `Ne.symm` / `Eq.symm`
    and is stuck on an inequality whose orientation is "backwards". -/
syntax "normalize_eq" : tactic

open Lean Meta Elab.Tactic in
elab_rules : tactic
  | `(tactic| normalize_eq) => withMainContext do
    -- Snapshot the list of hypotheses to flip; applying them mutates the local
    -- context, so collect first and apply after.
    let lctx ← getLCtx
    let mut toFlip : Array (Name × Bool) := #[]  -- (hypothesis name, isEq?)
    for ldecl in lctx do
      if ldecl.isImplementationDetail then continue
      let ty ← instantiateMVars ldecl.type
      let (isEq, a?, b?) ←
        if ty.isAppOfArity ``Eq 3 then
          pure (true, some (ty.getArg! 1), some (ty.getArg! 2))
        else if ty.isAppOfArity ``Ne 3 then
          pure (false, some (ty.getArg! 1), some (ty.getArg! 2))
        else
          pure (false, none, none)
      match a?, b? with
      | some a, some b =>
        if a.isFVar && b.isFVar then
          let aName := (← a.fvarId!.getUserName).toString
          let bName := (← b.fvarId!.getUserName).toString
          if aName > bName then
            toFlip := toFlip.push (ldecl.userName, isEq)
      | _, _ => pure ()
    for (hName, isEq) in toFlip do
      let hIdent := mkIdent hName
      let symIdent := mkIdent (if isEq then ``Eq.symm else ``Ne.symm)
      evalTactic (← `(tactic| replace $hIdent:ident := $symIdent:ident $hIdent:ident))

-- `register_simp_attr obvious_simp` lives in `Geometry/Tactics.lean`
-- (Lean requires the registration to be in a different file from the
-- first `attribute [obvious_simp]` use). This block tags the
-- chapter-0 / axiom-level lemmas that count as Greenberg's
-- minimum-standard intuition. Tag conservatively: a bad simp rule
-- here propagates to every `obvious` invocation downstream.

attribute [obvious_simp]
  -- set
  Set.mem_setOf_eq Set.mem_union Set.mem_inter_iff Set.mem_singleton_iff
  -- finset
  Finset.mem_insert Finset.mem_singleton Finset.mem_erase Finset.notMem_empty
  -- propositional
  ne_eq true_or or_true false_or or_false or_self
  true_and and_true false_and and_false and_self
  not_true_eq_false not_false_eq_true not_or not_and not_not

attribute [obvious_simp]
  -- line parts (unfolded forms)
  Segment Ray Extension LineThrough
  -- betweenness normalizing (title form — `ref axiom` doesn't
  -- parse inside `simp only [...]` arg lists)
  «Betweenness Commutativity»
  «A-B-C implies A B C are distinct and collinear»

/-- Attempts to unfold any geometric objects in the vicinity and eliminate booleans
 and the like. Tries to capture the author's intuition for 'by definition' in the text.

 The last alternative handles Finset literal equality (`{A,B,C} = {C,A,B}` etc.) by
 reducing to membership and tautology — convenient since Finsets are unordered.

 `normalize_eq` runs first to canonicalize `=` / `≠` orientations so `simp_all` can
 close hypotheses regardless of which side they were originally written on.

 The simp set is the `obvious_simp` attribute — each chapter tags its
 own canonical normalizations and they accumulate progressively. -/
macro "obvious" : tactic =>
  `(tactic| (
      normalize_eq
      first
      -- Pure rewrite closes the goal entirely (definitional only).
      | (simp_all only [obvious_simp]; done)
      -- Rewrite hyps and goal via `obvious_simp`, then let `tauto` do
      -- the propositional closing. This handles patterns like:
      --   hyp: `A - P - B`  ⊢  `P ∈ LineThrough B A`
      -- where the rewrite turns the hyp into a form that matches one
      -- disjunct of the unfolded goal, and `tauto` picks it.
      | (simp_all only [obvious_simp]; tauto)
      -- Goal-only unfold + propositional close (some sites have hyps
      -- in normalized form already).
      | (simp only [Segment, Ray, Extension, LineThrough]; tauto)
      -- Last-ditch: unfold geometric defs everywhere and tauto.
      | (unfold Segment Ray Extension LineThrough at *; tauto)
      -- The `ext` alternative is for Finset-literal equality goals
      -- (`{A,B,C} = {C,A,B}`). Guard with `first` so a `fail`
      -- alternative gives a clean error message when nothing closed.
      | (first
          | (ext; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, ne_eq]; tauto)
          | fail "obvious: no alternative closed the goal")))

macro "obvious" : term => `(by obvious)


/--
p.108 "Given any two distinct points B and D, there exist points A, C, and E lying on →ₗBD such that
A * B * D, B * C * D, and B * D * E".

Ed. I like to call this the 'density' axiom because, used recursively, it posits
something like the density of rationals -- for any two distinct points on a
line, there is always a point between them.
-/
atlas axiom B.2 "Two distinct points admit a left, middle, and right witness on their line"
  : ∀ B D : Point, B ≠ D ->
  ∃ A C E : Point, collinear A B C D E ∧ distinct A B C D E ∧ (A - B - D) ∧ (B - C - D) ∧ (B - D - E)
attribute [simp] «Two distinct points admit a left, middle, and right witness on their line»


/-- Construct a point 'to the left' of points BD on the induced line B D -/
atlas lemma 1.0.5 "Density axiom witness: a point left of two distinct points"
  : ∀ B D : Point, B ≠ D -> ∃ A : Point, collinear A B D ∧ distinct A B D ∧ (A - B - D) := by
      intro B D BneD
      have ⟨A, _, _, colABCDE, distinctABCDE, ABD, _, _⟩ := ref axiom B.2 B D BneD
      use A
      obvious


/-- Construct a point 'in between' points BD on the induced line B D -/
atlas lemma 1.0.6 "Density axiom witness: a point between two distinct points"
  : ∀ B D : Point, B ≠ D -> ∃ C : Point, collinear B C D ∧ distinct B C D ∧ (B - C - D) := by
      intro B D BneD
      have ⟨_, C, _, colABCDE, distinctABCDE, _, BCD, _⟩ := ref axiom B.2 B D BneD
      use C
      obvious


/-- Construct a point 'to the right' points BD on the induced line B D -/
atlas lemma 1.0.7 "Density axiom witness: a point right of two distinct points"
  : ∀ B D : Point, B ≠ D -> ∃ E : Point, collinear B D E ∧ distinct B D E ∧ (B - D - E) := by
      intro B D BneD
      have ⟨_, _, E, colABCDE, distinctABCDE, _, _, BDE⟩ := ref axiom B.2 B D BneD
      use E
      obvious


/-- p.108 "If A, B, and C are three distinct points lying on the same line, then
 one and only one of the points is between the other two."
-/
atlas axiom B.3 "Three distinct collinear points have exactly one between-arrangement"
  : ∀ A B C : Point, distinct A B C ∧ collinear A B C ->
  ( (A - B - C) ∧ ¬(B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧  (B - A - C) ∧ ¬(A - C - B)) ∨
  (¬(A - B - C) ∧ ¬(B - A - C) ∧  (A - C - B))
attribute [simp] «Three distinct collinear points have exactly one between-arrangement»

/--
p.110 "Definition. Let L be any line, and A and B points that do not lie on L. If A = B or if the segment A B
contains no points that lie on L, we say that A and B are _on the same side_ of L; whereas, if A ≠ B and segment A B
does intersect L, we say that A and B are _on opposite sides_ of L (see Figure 3.6). The law of the excluded middle
(Logic Rule 10) tells us that A and B are either on the same side or on opposite sides of L"
-/
@[reducible] def SameSide (A B : Point) (L : Line)
  := (A off L) ∧ (B off L) ∧ ((A = B) ∨ (∀ P : Point, (P on segment A B) -> (L avoids P)))

/--
"Splits" and "Guards", L "splits" A and B if A and B are on opposite sides of the 'wall' L, it 'guards'
them if they are both on the same side of the wall (we presume all points are allied with other points
on their side of the line).
-/
notation:20 L " splits " A " and " B => ¬(SameSide A B L)
notation:20 L " guards " A " and " B => SameSide A B L

/--
p.110 "Betweenness Axiom 4 (Plane Separation). For every line L and for any
three points A, B, and C not on L: (i) If A and B are on the same side of L and
if B and C are on the same side of L, the A and C are on the same side of L..."
-/
atlas axiom B-4i "Same-side is transitive across a common middle point"
  {A B C : Point} {L : Line} :
  (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L guards A and B) ∧ (L guards B and C) -> (L guards A and C)
attribute [simp] «Same-side is transitive across a common middle point»

/--
"... (ii) If A and B are on opposite sides of L and if B and C are opposite
sides of L, then A and C are on the same side of L."
-/
atlas axiom B-4ii "Two opposite-side relations chain to a same-side relation"
  {A B C : Point} {L : Line} :
  (L avoids A) ∧ (L avoids B) ∧ (L avoids C) ->
  (L splits A and B) ∧ (L splits B and C) -> (L guards A and C)
attribute [simp] «Two opposite-side relations chain to a same-side relation»

@[reducible] def Intersects (L M : Line) (X : Point) : Prop := L ∩ M = {X}

/-- Bare form of `L intersects M` — asserts the intersection is non-empty (i.e.
    `L` and `M` share *at least one* point, allowing the "L coincides with M"
    case). Kept as an opaque `def` so the goal stays readable; the unexpander
    below renders this as `L intersects M` in proof states.

    Going from this to a unique intersection point (`L intersects M at X`)
    requires extra work — typically `ref lemma 3.0.1` for lines,
    which uses `line_trichotomy` to rule out coincidence. -/
def IntersectsSome (L M : Set Point) : Prop := Set.Nonempty (L ∩ M)

/-- Extract a point in the intersection from a bare `intersects` hypothesis.
    Note: the returned `X` is *some* shared point, not necessarily a unique one. -/
lemma IntersectsSome.intersection_point {L M : Set Point} (h : IntersectsSome L M)
  : ∃ X, X ∈ L ∩ M := h


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

/-- `clearly P := by body` introduces `P` as a fact for the rest of the proof, having
    discharged the negation branch — i.e. the body proves the main goal under the
    assumption `¬P`. The reading is: "clearly P, because if not, the goal is immediate
    (`body`); proceeding under `P`".

    Supported shapes for `P` (auto-named hypotheses derived from the identifiers):
    - `A ≠ B`: rest of proof gets `AneB : A ≠ B`; body sees `AeqB : A = B`.
    - `A = B`: rest of proof gets `AeqB : A = B`; body sees `AneB : A ≠ B`.
    - `P on L`: rest of proof gets `PonL : P on L`; body sees `PoffL : P off L`.
    - `P off L`: rest of proof gets `PoffL : P off L`; body sees `PonL : P on L`. -/
syntax "clearly " term " := " "by " tacticSeq : tactic
syntax "clearly " term : tactic

/-- Derive an auto-name component from a term used in a `clearly` clause.
    Identifiers map to their user-name; line-part expressions get short
    capitalized prefixes (`segment A B` → `SegAB`, `line A B` → `LineAB`, etc.). -/
private def clearlyTermName (s : Lean.Syntax) : Lean.MacroM String := do
  match s with
  | `($id:ident) => return id.getId.toString
  | `(segment $A:ident $B:ident) => return s!"Seg{A.getId}{B.getId}"
  | `(ray $A:ident $B:ident) => return s!"Ray{A.getId}{B.getId}"
  | `(extension $A:ident $B:ident) => return s!"Ext{A.getId}{B.getId}"
  | `(line $A:ident $B:ident) => return s!"Line{A.getId}{B.getId}"
  | _ => Lean.Macro.throwError "clearly: cannot derive an auto-name from this term"

-- `macro_rules` (rather than `elab_rules`) expansion keeps the resulting tactics
-- visible to the LSP. However, see FIXME below.
--
-- FIXME: LSP doesn't render the body-side hypothesis (e.g. `ConL` inside a
-- `clearly C off L := by ...` block) in the goal panel at intermediate lines of
-- the body, even though it IS in scope (usable in the proof and visible via
-- `trace_state`). The other-side hypothesis (e.g. `CoffL` on the line after the
-- `clearly` block) renders fine. Suspected cause: macro-introduced `rcases` /
-- `case inl =>` tokens get synthetic source positions that the LSP's info-tree
-- walker doesn't query against. Workaround: put a `trace_state` at the body's
-- start to confirm the hypothesis is there.
macro_rules
  | `(tactic| clearly $prop) => `(tactic| clearly $prop := by obvious)
  | `(tactic| clearly $lhs ≠ $rhs := by $body) => do
    let lName ← clearlyTermName lhs
    let rName ← clearlyTermName rhs
    let eqIdent := Lean.mkIdent (.mkSimple s!"{lName}eq{rName}")
    let neIdent := Lean.mkIdent (.mkSimple s!"{lName}ne{rName}")
    `(tactic| (
      rcases Classical.em ($lhs = $rhs) with $eqIdent:ident | $neIdent:ident
      case inl => $body))
  | `(tactic| clearly $lhs = $rhs := by $body) => do
    let lName ← clearlyTermName lhs
    let rName ← clearlyTermName rhs
    let eqIdent := Lean.mkIdent (.mkSimple s!"{lName}eq{rName}")
    let neIdent := Lean.mkIdent (.mkSimple s!"{lName}ne{rName}")
    `(tactic| (
      rcases Classical.em ($lhs = $rhs) with $eqIdent:ident | $neIdent:ident
      case inr => $body))
  | `(tactic| clearly $P on $L := by $body) => do
    let pName ← clearlyTermName P
    let lName ← clearlyTermName L
    let onIdent := Lean.mkIdent (.mkSimple s!"{pName}on{lName}")
    let offIdent := Lean.mkIdent (.mkSimple s!"{pName}off{lName}")
    `(tactic| (
      rcases Classical.em ($P ∈ $L) with $onIdent:ident | $offIdent:ident
      case inr => $body))
  | `(tactic| clearly $P off $L := by $body) => do
    let pName ← clearlyTermName P
    let lName ← clearlyTermName L
    let onIdent := Lean.mkIdent (.mkSimple s!"{pName}on{lName}")
    let offIdent := Lean.mkIdent (.mkSimple s!"{pName}off{lName}")
    `(tactic| (
      rcases Classical.em ($P ∈ $L) with $onIdent:ident | $offIdent:ident
      case inl => $body))


/-- `by_exhaustion h` where `h : P ∈ {A, B, C, ...}` (a Finset literal) splits
    the proof into one goal per element, with the corresponding equality
    auto-named like `clearly`: `PeqA`, `PeqB`, etc.

    Stands in for `fin_cases h` (which requires a computable `DecidableEq` and
    thus doesn't apply to `Point`). Internally: `simp` unfolds Finset membership
    to a disjunction, then `rcases` destructures with the generated names. -/
syntax "by_exhaustion " ident : tactic

open Lean Meta Elab Elab.Tactic in
elab_rules : tactic
  | `(tactic| by_exhaustion $h:ident) => withMainContext do
    -- Step 1: unfold Finset membership into a disjunction of equalities.
    evalTactic (← `(tactic|
      simp only [Finset.mem_insert, Finset.mem_singleton] at $h:ident))
    -- Step 2: walk the resulting Or chain, collecting auto-names like `<lhs>eq<rhs>`.
    withMainContext do
      let hFVar ← getFVarId h
      let hType ← instantiateMVars (← hFVar.getType)
      let getName : Expr → MetaM String := fun e => do
        match e with
        | .fvar fid => return (← fid.getUserName).toString
        | _ => return "x"
      let extractEq (e : Expr) : MetaM (Option String) := do
        if e.isAppOfArity ``Eq 3 then
          let lN ← getName (e.getArg! 1)
          let rN ← getName (e.getArg! 2)
          return some s!"{lN}eq{rN}"
        else
          return none
      let mut names : Array String := #[]
      let mut current := hType
      while current.isAppOfArity ``Or 2 do
        if let some n ← extractEq (current.getArg! 0) then
          names := names.push n
        current := current.getArg! 1
      if let some n ← extractEq current then
        names := names.push n
      if names.isEmpty then
        throwError "by_exhaustion: could not extract eq disjuncts from hypothesis type"
      -- Step 3: build and run `rcases h with name_1 | name_2 | ...` via string parse.
      let patStr := String.intercalate " | " names.toList
      let tacStr := s!"rcases {h.getId} with {patStr}"
      match Parser.runParserCategory (← getEnv) `tactic tacStr with
      | .ok stx => evalTactic stx
      | .error err =>
          throwError s!"by_exhaustion: failed to build rcases tactic from '{tacStr}': {err}"


end Geometry.Theory
