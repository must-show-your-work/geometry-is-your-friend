/-
# Atlas: book-style theorem metadata

A custom attribute and command macros for tagging theorems with their
**kind** (proposition / corollary / lemma / theorem / axiom / exercise /
definition / remark / postulate), their **book reference number**, and
their **prose title**. The atlas viewer (scripts/graph.html) uses these
to render proper book-style cards instead of bare decl names.

## Defining

Every kind goes through the same `atlas <kind>` prefix to dodge any
collision with Lean's built-in `theorem`/`lemma`/`axiom` command
keywords:

```
atlas proposition 3.4 "Pasch's Postulate" : <type> := <proof>
atlas alternate   3.4 "Pasch's Postulate (geometric proof)" : <type> := <proof>
atlas corollary   3.5 "Triangle Inequality" : <type> := <proof>
atlas exercise    3.7 "First Isomorphism" : <type> := <proof>
atlas definition  2.1 "Linear Order" : <type> := <def>
atlas remark      3.8 "Note on hyperbolic case" : <type> := <proof>
atlas postulate   2.0 "Parallel Postulate" : <type> := <proof>
atlas theorem     3.4 "Major Result"      : <type> := <proof>
atlas lemma       3.4 "Pasch helper"      : <type> := <proof>
atlas axiom       I.1 "Two-point line"    : <type>
```

The book reference number can be `num.num` (`3.4`) or `ident.num`
(`I.1`). The generated decl name is the French-quoted title verbatim:
`theorem «Pasch's Postulate» : ...`. No sanitization, no aliasing.

## Referencing

In term position the bare kind keyword works (no `atlas` prefix needed —
no parser conflict in term position):

```
apply proposition 3.4
exact axiom I.1
refine theorem 3.7
```

Or by title directly (requires French-quote input method):

```
apply «Pasch's Postulate»
```

Both forms resolve to the same underlying decl. The `atlas` prefix at
definition sites is asymmetric on purpose: definitions are rare and
tolerate the extra word; references are frequent and benefit from
brevity.
-/

import Lean

open Lean Elab Command

namespace Atlas

/-! ## State -/

/-- Per-decl atlas metadata. -/
structure AtlasEntry where
  kind   : String
  number : String
  title  : String
  deriving Inhabited, Repr, BEq

/-- The persistent representation of one entry. -/
abbrev AtlasRow := Name × String × String × String

/-- In-memory state: per-decl entries plus the two reverse indexes used
    by elab-term lookups.

    `byKindNumber` stores a *list* of names per (kind, number) key
    because multi-part propositions and alternate proofs legitimately
    share keys. The elab term `proposition 3.4` consults this list:
      • 0 entries → error "no decl tagged"
      • 1 entry  → resolves unambiguously
      • 2+       → error with the list of titles, prompting the user
                   to disambiguate via the «Title» form. -/
structure AtlasState where
  byName       : NameMap AtlasEntry           := {}
  byKindNumber : Std.HashMap String (List Name) := {}  -- key: `"{kind}/{number}"`
  byTitle      : Std.HashMap String Name      := {}
  deriving Inhabited

private def insertEntry (s : AtlasState) (row : AtlasRow) : AtlasState :=
  let (n, k, num, t) := row
  let entry : AtlasEntry := { kind := k, number := num, title := t }
  let key := k ++ "/" ++ num
  let existing := s.byKindNumber.get? key |>.getD []
  { byName       := s.byName.insert n entry
    byKindNumber := s.byKindNumber.insert key (n :: existing)
    byTitle      := s.byTitle.insert t n }

initialize atlasExt : SimplePersistentEnvExtension AtlasRow AtlasState ←
  registerSimplePersistentEnvExtension {
    name          := `Atlas.atlasExt
    addEntryFn    := insertEntry
    addImportedFn := fun arr =>
      arr.foldl (init := ({} : AtlasState)) fun s sub =>
        sub.foldl insertEntry s
  }

/-- Walk `getModuleEntries` for every imported module and fold the
    results back into a fresh `AtlasState`. Workaround for the case
    where the in-memory `getState` doesn't seem to honour
    `addImportedFn` reliably across module boundaries — useful for
    consumers like `scripts/DumpDecls.lean` that need the merged
    forward-lookup map. -/
def atlasStateFromImports (env : Environment) : AtlasState := Id.run do
  let mut st : AtlasState := {}
  let mut i : Nat := 0
  let n := env.allImportedModuleNames.size
  while i < n do
    let entries := PersistentEnvExtension.getModuleEntries atlasExt env i
    for row in entries do
      st := insertEntry st row
    i := i + 1
  return st

/-! ## Query helpers (read by `DumpDecls.lean` and the elab rules below) -/

def atlasEntry? (env : Environment) (n : Name) : Option AtlasEntry :=
  match (atlasExt.getState env).byName.find? n with
  | some e => some e
  | none   => (atlasStateFromImports env).byName.find? n

/-- Return every name tagged with `(kind, number)`. May be empty (no
    match) or contain more than one entry (multi-part propositions,
    alternate proofs, etc.). Callers decide how to handle ambiguity. -/
def atlasLookupByNumber (env : Environment) (kind number : String) : List Name :=
  (atlasExt.getState env).byKindNumber.get? (kind ++ "/" ++ number) |>.getD []

def atlasLookupByTitle (env : Environment) (title : String) : Option Name :=
  (atlasExt.getState env).byTitle.get? title

/-- Kind-tier table — used by `atlasLookupCascading`. A reference to a
    kind in some tier T cascades through T and every tier below it,
    collecting decls tagged with the requested number. The choice-
    resolver downstream picks by type unification.

    Kinds *not* listed in any tier are looked up *exactly* — they
    don't cascade and they don't get cascaded into. That's the right
    default for kinds where a request is intentional and specific:
    `alternate K` means "I want the alternate proof of K, not K
    itself", `definition K` means "the definition, not a result".

    Vocabulary covers most book-math kind names. If a project needs
    a kind not listed here, add it to whichever tier matches its
    role; the cascade is purely structural so adding entries is
    cheap. Conjecture/hypothesis are deliberately omitted — they
    name *unproven* things and don't fit the "result" or "commentary"
    framing; add them later if a use case appears. -/
def kindTiers : List (List String) :=
  [ -- T1: main results — what a reader cites as "the theorem"
    [ "theorem", "proposition", "postulate", "lemma", "axiom"
    , "exercise", "law", "principle", "fact", "scholium" ]
    -- T2: derivative — strict consequences of T1 (or each other)
  , [ "corollary", "consequence", "claim" ]
    -- T3: commentary — prose that doesn't carry the proof but
    -- clarifies or illustrates it
  , [ "remark", "note", "observation", "example", "discussion" ]
  ]

/-- Cascading lookup. Given a starting `kind` and `number`, find the
    tier containing `kind`, then collect every decl tagged `number`
    whose kind is in that tier or any tier below. Returns the names
    flat-in-tier-order. Kinds outside the tier table are exact-lookup
    only. -/
def atlasLookupCascading (env : Environment) (kind number : String) : List Name :=
  -- Find the starting tier (the one that contains `kind`). If `kind`
  -- isn't in any tier, the lookup stays exact — no cascade.
  let rec dropUntil : List (List String) → List (List String)
    | []         => []
    | t :: rest  => if t.contains kind then t :: rest else dropUntil rest
  let tiers := dropUntil kindTiers
  if tiers.isEmpty then
    atlasLookupByNumber env kind number
  else
    -- Search current + all lower tiers, in order. Within the starting
    -- tier, the user's requested kind goes first so it gets first
    -- crack at unification.
    let preferredFirst : List String := tiers.head!.filter (· != kind) |>.cons kind
    let allKinds : List String := preferredFirst ++ (tiers.tail!.foldl (· ++ ·) [])
    allKinds.foldl (init := []) fun acc k =>
      acc ++ atlasLookupByNumber env k number

/-! ## Attribute -/

syntax (name := atlasAttr) "atlas" str str str : attr

initialize registerBuiltinAttribute {
  name  := `atlasAttr
  descr := "tag a declaration with atlas metadata (kind, number, title)"
  add   := fun decl stx _attrKind => do
    let kindStr  ← match stx[1].isStrLit? with
      | some s => pure s
      | none   => throwError "atlas: expected string literal for `kind`"
    let numStr   ← match stx[2].isStrLit? with
      | some s => pure s
      | none   => throwError "atlas: expected string literal for `number`"
    let titleStr ← match stx[3].isStrLit? with
      | some s => pure s
      | none   => throwError "atlas: expected string literal for `title`"
    if titleStr.isEmpty then
      throwError "atlas: `title` cannot be empty"
    let env := (← getEnv)
    let st  := atlasExt.getState env
    -- No (kind, number) duplicate check: multi-part propositions
    -- (P1.i, P1.ii sharing 3.1), alternate proofs, and theory lemmas
    -- with empty numbers all legitimately share keys. Title
    -- uniqueness is what catches real conflicts.
    --
    -- The elab terms (`proposition 3.4`, `alternate 3.4`, …) error
    -- on ambiguous lookup — they refuse to silently pick one. The
    -- user disambiguates via the `«Title»` form.
    if let some existing := st.byTitle.get? titleStr then
      throwError s!"atlas: duplicate title \"{titleStr}\" — already on `{existing}`"
    setEnv <| atlasExt.addEntry env (decl, kindStr, numStr, titleStr)
}

/-! ## Reference-number syntax -/

declare_syntax_cat atlasNum
-- Lean lexes `3.4` / `0.1` as a single `scientific` token, NOT as
-- `num "." num` (which would require whitespace).
--
-- Supported forms:
--   * `3.4` — single scientific (book chapter . prop number)
--   * `I.1` — `ident "." num` for letter-prefixed axioms
--   * `2.0.1` — `scientific "." num` for theory lemmas keyed
--     `chapter . level . index`
--
-- For compound book labels like `B.1.a` (Greenberg's Betweenness Axiom
-- 1, part a), the bare-dotted form `B.1.a` cannot be written: Lean's
-- lexer reads `1.` as the start of a decimal literal and then errors
-- on the trailing letter. Use a bracketed-string fallback instead:
-- `atlas axiom ["B.1.a"] "Title" : T`. The brackets disambiguate from
-- the un-numbered `atlas <kind> "Title" ...` form (which has only one
-- leading string).
syntax scientific  : atlasNum
syntax ident "." num : atlasNum
syntax scientific "." num : atlasNum
-- `ident "-" num ident` handles compound book labels like `B-1a` /
-- `B-4ii` (matching Greenberg's notation). The hyphen separator is
-- critical: a `.` variant would make `B.2 B D` greedy-match as
-- atlasNum `B.2B` (consuming the next axiom-call arg), but `-` here
-- shares no tokens with the existing `ident "." num` form (`B.2`)
-- so the two are unambiguously distinct. Avoids the bracketed-string
-- fallback for this common case (B-axiom sub-parts a/b/i/ii/iii).
syntax ident "-" num ident : atlasNum
syntax "[" str "]"   : atlasNum

/-- Pull the source text out of a parsed scientific-literal node.
    Lean wraps the literal in a node whose first child is the atom. -/
private def scientificAtomText (s : TSyntax `scientific) : Option String :=
  match s.raw[0] with
  | .atom _ str => some str
  | _ => none

/-- Render an `atlasNum` syntax tree to the canonical string we store
    and look up. `3.4` → `"3.4"`, `I.1` → `"I.1"`, `"B.1.a"` → `"B.1.a"`. -/
def atlasNumToString : TSyntax `atlasNum → MacroM String
  | `(atlasNum| $s:scientific . $n:num) =>
    match scientificAtomText s with
    | some str => return s!"{str}.{n.getNat}"
    | none     => Macro.throwUnsupported
  | `(atlasNum| $s:scientific) =>
    match scientificAtomText s with
    | some str => return str
    | none     => Macro.throwUnsupported
  | `(atlasNum| $i:ident - $n:num $j:ident) => return s!"{i.getId}-{n.getNat}{j.getId}"
  | `(atlasNum| $i:ident . $n:num) => return s!"{i.getId}.{n.getNat}"
  | `(atlasNum| [ $s:str ]) => return s.getString
  | _ => Macro.throwUnsupported

/-! ## Command macros -/

/-- The TSyntax type for a sequence of bracketed binders
    (`{A : T}`, `(x : T)`, `[h : T]`, etc.). Passed through verbatim
    to the underlying `theorem`/`axiom`/`def` declaration. -/
abbrev BracketedBinders := TSyntaxArray ``Lean.Parser.Term.bracketedBinder

/-- An optional doc comment, captured before the `atlas` keyword and
    forwarded onto the generated declaration so `/-- … -/` attaches
    normally. -/
abbrev DocComment? := Option (TSyntax ``Lean.Parser.Command.docComment)

/-- Generate `@[atlas "kind" "num" "title"] theorem «title» <binders> : type := body`,
    prepending an optional doc comment so the macro can be preceded by
    `/-- … -/` like any builtin theorem. Helpers take `numStr : String`
    directly — callers either feed `← atlasNumToString n` (numbered
    form) or `""` (un-numbered form). The attribute hook treats empty
    string as "no book number" and skips the (kind, number) duplicate
    check accordingly. -/
private def expandAtlasTheorem
    (kind : String) (numStr : String)
    (title : TSyntax `str) (binders : BracketedBinders)
    (doc? : DocComment?) (ty body : Term)
    : MacroM (TSyntax `command) := do
  let kindLit := Syntax.mkStrLit kind
  let numLit  := Syntax.mkStrLit numStr
  -- Preserve the source range of `title` on the generated identifier
  -- so downstream tooling (e.g. SubVerso highlighter) sees a real
  -- definition-site token rather than a synthetic one. `mkIdent` alone
  -- produces a positionless ident, which `SubVerso.Highlighted.definedNames`
  -- treats as not-a-def-site and so omits from the per-decl extraction.
  let ident   := mkIdentFrom title.raw (Name.mkSimple title.getString)
  match doc? with
  | some doc =>
    `($doc:docComment
      @[atlas $kindLit $numLit $title] theorem $ident $binders* : $ty := $body)
  | none =>
    `(@[atlas $kindLit $numLit $title] theorem $ident $binders* : $ty := $body)

private def expandAtlasAxiom
    (kind : String) (numStr : String)
    (title : TSyntax `str) (binders : BracketedBinders)
    (doc? : DocComment?) (ty : Term)
    : MacroM (TSyntax `command) := do
  let kindLit := Syntax.mkStrLit kind
  let numLit  := Syntax.mkStrLit numStr
  -- Preserve the source range of `title` on the generated identifier
  -- so downstream tooling (e.g. SubVerso highlighter) sees a real
  -- definition-site token rather than a synthetic one. `mkIdent` alone
  -- produces a positionless ident, which `SubVerso.Highlighted.definedNames`
  -- treats as not-a-def-site and so omits from the per-decl extraction.
  let ident   := mkIdentFrom title.raw (Name.mkSimple title.getString)
  match doc? with
  | some doc =>
    `($doc:docComment
      @[atlas $kindLit $numLit $title] axiom $ident $binders* : $ty)
  | none =>
    `(@[atlas $kindLit $numLit $title] axiom $ident $binders* : $ty)

private def expandAtlasDef
    (kind : String) (numStr : String)
    (title : TSyntax `str) (binders : BracketedBinders)
    (doc? : DocComment?) (ty body : Term)
    : MacroM (TSyntax `command) := do
  let kindLit := Syntax.mkStrLit kind
  let numLit  := Syntax.mkStrLit numStr
  -- Preserve the source range of `title` on the generated identifier
  -- so downstream tooling (e.g. SubVerso highlighter) sees a real
  -- definition-site token rather than a synthetic one. `mkIdent` alone
  -- produces a positionless ident, which `SubVerso.Highlighted.definedNames`
  -- treats as not-a-def-site and so omits from the per-decl extraction.
  let ident   := mkIdentFrom title.raw (Name.mkSimple title.getString)
  match doc? with
  | some doc =>
    `($doc:docComment
      @[atlas $kindLit $numLit $title] def $ident $binders* : $ty := $body)
  | none =>
    `(@[atlas $kindLit $numLit $title] def $ident $binders* : $ty := $body)

-- Every atlas decl carries a number — this is what lets us add the
-- uniform term-position `atlas <kind> <num>` form below without parser
-- ambiguity. (An un-numbered command form would compete with that term
-- form on the `atlas <ident>` prefix and prevent backtracking.)
--
-- For theory lemmas without a book reference, use the three-part
-- `<chapter>.<level>.<index>` scheme — `<chapter>` is the book chapter
-- the file belongs to, `<level>` is the proposition number that the
-- lemma's deps require (0 if independent), `<index>` is sequential.
--
-- The kind word is parsed as `rawIdent` — accepts any identifier
-- including those reserved as keywords elsewhere (Mathlib's `lemma`,
-- Lean's `axiom`, etc.). This is what lets `atlas lemma <num> "Title"`
-- coexist with bare `lemma X : T := body` in the same module: no
-- token shadowing. The kind ident's text is validated in `macro_rules`
-- below.
syntax (docComment)? "atlas" rawIdent atlasNum str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" rawIdent atlasNum str (bracketedBinder)* ":" term            : command

-- Known kinds that expand to `def`; everything else expands to
-- `theorem` (or `axiom` for the body-less arm).
private def isDefKind (kind : String) : Bool := kind == "definition"

macro_rules
  -- Numbered, body-having.
  | `($[$doc?:docComment]? atlas $k:ident $n:atlasNum $t:str $bs:bracketedBinder* : $ty := $b) => do
      let kind := k.raw.getId.toString
      if kind == "axiom" then
        Macro.throwErrorAt k
          "atlas axiom takes no `:= body`; write `atlas axiom <num> \"<title>\" : <type>`"
      let numStr ← atlasNumToString n
      if isDefKind kind then
        expandAtlasDef kind numStr t bs doc? ty b
      else
        expandAtlasTheorem kind numStr t bs doc? ty b
  -- Numbered axiom (no body).
  | `($[$doc?:docComment]? atlas $k:ident $n:atlasNum $t:str $bs:bracketedBinder* : $ty) => do
      let kind := k.raw.getId.toString
      if kind != "axiom" then
        Macro.throwErrorAt k
          s!"atlas {kind} requires `:= body` (only `atlas axiom` is body-less)"
      expandAtlasAxiom kind (← atlasNumToString n) t bs doc? ty

/-! ## Reference (term-position) elaboration -/

-- Helper used by every term-elab below. Looks up the (kind, number)
-- pair in the atlas reverse index and emits a constant reference with
-- fresh universe metavariables (the standard pattern for emitting a
-- reference to a polymorphic decl from elab code).
private def elabAtlasRefAux (kind : String) (num : TSyntax `atlasNum)
    (expectedType? : Option Expr := none)
    : Elab.Term.TermElabM Expr := do
  let numStr : String ← match num with
    | `(atlasNum| $s:scientific) =>
      match scientificAtomText s with
      | some str => pure str
      | none     => throwError "atlas: malformed number reference (scientific)"
    | `(atlasNum| $s:scientific . $n:num) =>
      match scientificAtomText s with
      | some str => pure s!"{str}.{n.getNat}"
      | none     => throwError "atlas: malformed number reference (scientific.num)"
    | `(atlasNum| $i:ident - $n:num $j:ident) => pure s!"{i.getId}-{n.getNat}{j.getId}"
    | `(atlasNum| $i:ident . $n:num) => pure s!"{i.getId}.{n.getNat}"
    | `(atlasNum| [ $s:str ]) => pure s.getString
    | _ => throwError "atlas: malformed number reference"
  let env ← getEnv
  -- Tier cascade: when the user writes `<kind> N`, we collect every
  -- decl tagged `N` whose kind is in the same tier as `<kind>` OR a
  -- lower (more derivative) tier. The collected list is then wrapped
  -- in an overload-choice node; Lean's elaborator picks by unifying
  -- each branch's type against the expected type.
  --
  -- Tiers (in order, top-first):
  --   T1 results:       theorem, proposition, postulate, lemma,
  --                     axiom, exercise, alternate
  --   T2 derived:       corollary
  --   T3 commentary:    remark
  --
  -- So `theorem 3.3` searches theorems first, then corollaries of
  -- 3.3, then remarks of 3.3 — picking the first that unifies. The
  -- starting tier is whichever tier contains the kind the user wrote,
  -- so `corollary 3.3` does *not* fall back up to T1 (you asked
  -- for the corollary specifically); only T2→T3 cascade.
  --
  -- Definitions and axioms (the foundational kinds) don't cascade —
  -- their lookup stays exact. Querying `axiom B-1b` for a corollary
  -- would surprise.
  let ns := atlasLookupCascading env kind numStr
  match ns with
  | []  => throwError s!"atlas: no {kind} (or derivative tier) tagged `{numStr}` found"
  | [n] =>
    -- Singleton: don't thread the expected type — passing a metavariable
    -- expected type interferes with `have ⟨pat⟩ := …` destructuring,
    -- which needs the rhs to elaborate to a concrete type unaided.
    Lean.Elab.Term.elabTerm (mkIdent n) none
  | _  =>
    -- Multiple candidates — wrap in an overload-choice node so Lean's
    -- built-in elab tries each branch against `expectedType?`. Caveat:
    -- this only disambiguates when `expectedType?` is a concrete (or
    -- partially-concrete) type at the choice's elab site. In
    -- function-application position (`ref proposition 3.3 ⟨…⟩` is
    -- the function part), the expected type is `?α → ?β`-shaped and
    -- every candidate unifies trivially — so an outer `have x : T :=`
    -- annotation alone is not sufficient to dispatch. Those sites
    -- still need the «Title» form, or an out-of-line `have foo : T :=
    -- ref kind N args` extraction.
    let alts : Array Syntax := ns.toArray.map (fun n => (mkIdent n).raw)
    let choice : Syntax := mkNode choiceKind alts
    Lean.Elab.Term.elabTerm choice expectedType?

-- `:max` precedence so these can stand in function position of an
-- application: `proposition 3.4 heq` parses as `(proposition 3.4) heq`
-- instead of consuming `heq` as part of the elab-term syntax and bailing.
--
-- NOTE: we deliberately do *not* expose term-position keywords for
-- `theorem`/`lemma`/`axiom`, even though they are valid `atlas` kinds.
-- Registering those as term-position tokens would mark them as parser
-- keywords, which then breaks the *command*-position parsing of bare
-- `lemma X {b : T} : ...` / `axiom X : ...` (Lean's parser gets confused
-- between the term-position and command-position uses). For references
-- to those kinds, use the French-quoted title form: «My Title».
syntax:max (name := atlasRefProposition) "proposition" atlasNum : term
-- `alternate N.K` refers to an alternate proof of proposition N.K.
-- If multiple alternates share a number, the reference errors with
-- the list of titles; use «Title» to disambiguate.
syntax:max (name := atlasRefAlternate)   "alternate"   atlasNum : term
syntax:max (name := atlasRefCorollary)   "corollary"   atlasNum : term
syntax:max (name := atlasRefExercise)    "exercise"    atlasNum : term
syntax:max (name := atlasRefRemark)      "remark"      atlasNum : term
syntax:max (name := atlasRefPostulate)   "postulate"   atlasNum : term
syntax:max (name := atlasRefDefinition)  "definition"  atlasNum : term

-- Uniform `atlas <kind> <num>` term-position form. Works for *every*
-- atlas kind including `lemma`/`axiom`/`theorem` (which can't have bare
-- term keywords because that would reserve those tokens and break bare
-- command parsing of `lemma X.Y {b}: T := body`). The leading `"atlas"`
-- keyword disambiguates from the command form: command needs a string
-- title next, term form takes an `atlasNum` (none of whose variants
-- start with `"`, since the string-form is bracketed as `["..."]`).
syntax:max (name := atlasRef) "ref" rawIdent atlasNum : term

-- Vararg-capturing variant: `apply kind N args*` parses as one unit (the
-- args are consumed into the parse tree, not left for `App`). Used when
-- the kind+num resolves to *multiple* atlas decls and we need
-- type-directed dispatch on the application — which Lean's `elabAppFn`
-- can't do for our custom `ref` (it only dispatches choices that are
-- syntactically `choiceKind` *before* macro expansion of `stx[0]`).
-- With args captured, we try each candidate and pick the one that fits.
--
-- Backward-compat note: `ref kind N` (no varargs) stays the canonical
-- form when the lookup is unambiguous; reserve `apply kind N args*` for
-- paired-decl sites where dispatch is needed. The two keywords keep the
-- greedy-vararg issue contained: `subset_inter ref lemma 2.0.4 ref
-- lemma 2.0.14` still parses with sibling refs (the old way), and
-- only sites that opt in to `apply` accept trailing args.
syntax:max (name := atlasApply) "apply" rawIdent atlasNum (ppSpace colGt term:max)+ : term
-- An `@`-explicit variant of `ref` was attempted (`eref`, also `@ref`).
-- Neither composes cleanly with Lean's built-in `@`: that lives at
-- the syntactic level and gates which `TermElab` runs, while our
-- elab_rule resolves and elaborates the constant directly, bypassing
-- the explicit-mode flag. For positional-implicits call sites, use
-- `@«Title»` form (Lean handles French-quoted idents natively after `@`).

-- Use `@[term_elab kind]` form (rather than `elab_rules : term <= expectedType`)
-- so the rule fires in every position — including function-application slots
-- like `ref lemma 0.0.5 S`, where `ref lemma 0.0.5` is elaborated with no
-- expected type because it's the function part of an application. The `<=`
-- form gates rules to only fire when an expected type is provided directly,
-- which is too restrictive here. The `expectedType?` arg gives us the same
-- info when available, without the gating.

@[term_elab atlasRefProposition]
def elabAtlasRefPropositionTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| proposition $n:atlasNum) => elabAtlasRefAux "proposition" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefAlternate]
def elabAtlasRefAlternateTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| alternate $n:atlasNum) => elabAtlasRefAux "alternate" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefCorollary]
def elabAtlasRefCorollaryTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| corollary $n:atlasNum) => elabAtlasRefAux "corollary" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefExercise]
def elabAtlasRefExerciseTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| exercise $n:atlasNum) => elabAtlasRefAux "exercise" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefRemark]
def elabAtlasRefRemarkTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| remark $n:atlasNum) => elabAtlasRefAux "remark" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefPostulate]
def elabAtlasRefPostulateTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| postulate $n:atlasNum) => elabAtlasRefAux "postulate" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRefDefinition]
def elabAtlasRefDefinitionTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| definition $n:atlasNum) => elabAtlasRefAux "definition" n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

@[term_elab atlasRef]
def elabAtlasRefTerm : Lean.Elab.Term.TermElab := fun stx expectedType? =>
  match stx with
  | `(term| ref $k:ident $n:atlasNum) =>
      elabAtlasRefAux k.getId.toString n expectedType?
  | _ => Lean.Elab.throwUnsupportedSyntax

-- Vararg-capturing `apply kind N args*` elab. Used when the (kind, num)
-- key resolves to multiple atlas decls and we need type-directed
-- dispatch on the application. Lean's `elabAppFn` can't disambiguate a
-- choice in function-position because it doesn't propagate return type
-- to the function elab; capturing args ourselves lets us try each
-- candidate against the full application + expected type.
@[term_elab atlasApply]
def elabAtlasApplyTerm : Lean.Elab.Term.TermElab := fun stx expectedType? => do
  match stx with
  | `(term| apply $k:ident $n:atlasNum $args*) => do
      let kind := k.getId.toString
      let numStr ← match n with
        | `(atlasNum| $s:scientific) =>
          match scientificAtomText s with
          | some str => pure str
          | none     => throwError "atlas: malformed number reference (scientific)"
        | `(atlasNum| $s:scientific . $m:num) =>
          match scientificAtomText s with
          | some str => pure s!"{str}.{m.getNat}"
          | none     => throwError "atlas: malformed number reference (scientific.num)"
        | `(atlasNum| $i:ident - $m:num $j:ident) => pure s!"{i.getId}-{m.getNat}{j.getId}"
        | `(atlasNum| $i:ident . $m:num) => pure s!"{i.getId}.{m.getNat}"
        | `(atlasNum| [ $s:str ]) => pure s.getString
        | _ => throwError "atlas: malformed number reference"
      let env ← getEnv
      -- Use *exact* (non-cascading) lookup for `apply`. The cascade
      -- (T1 → T2 → T3) is the right default for the loose-typing
      -- `ref kind N` form — "I want the result-tier thing at N, don't
      -- care if it's labeled `theorem` or `proposition`". But for
      -- `apply kind N args*`, the user is explicit about which kind
      -- they want, and pulling in adjacent kinds (corollaries when
      -- `proposition` was requested) creates spurious type-equivalent
      -- candidates that defeat dispatch.
      let ns := atlasLookupByNumber env kind numStr
      match ns with
      | []  =>
        throwError s!"atlas apply: no {kind} tagged `{numStr}` found (exact lookup; cascade is disabled for `apply`)"
      | [n] =>
        -- Single match — just elaborate as a normal application.
        let head := mkIdent n
        let appStx ← `($head $args*)
        Lean.Elab.Term.elabTerm appStx expectedType?
      | _  =>
        -- Multi-match. Need a concrete `expectedType` to dispatch on.
        -- Postpone if it's None or contains *any* metavariables (not
        -- just at the head) — Lean re-runs after surrounding context
        -- pins them. Without this, sites like `ref lemma X ⟨apply prop
        -- 3.3 …, sibling⟩` get elaborated before `sibling` constrains
        -- the implicits, so the apply slot sees a metavar-laden
        -- expected type and every candidate trivially unifies.
        --
        -- `tryPostponeIfNoneOrMVar` only checks the *head* — we need
        -- `tryPostponeIfHasMVars?` which scans the whole expression
        -- and postpones if any unassigned mvars remain.
        let some expected ← Lean.Elab.Term.tryPostponeIfHasMVars? expectedType?
          | throwError s!"atlas apply: {kind} `{numStr}` expected type still has metavariables after postpone — can't dispatch ({ns.length} candidates). Add `: T` annotation or restructure (e.g., extract to `have x : T := ...`)."
        let mut successes : List Name := []
        let mut lastError : Option MessageData := none
        for cand in ns do
          let snap ← Lean.Elab.Term.saveState
          try
            let head := mkIdent cand
            let appStx ← `($head $args*)
            -- Elaborate without expected-type guidance, then *explicitly*
            -- check inferred type against expected via `isDefEq`.
            -- `elabTerm`/`elabTermEnsuringType` defer most unification
            -- via postponed metavars and don't surface failures
            -- synchronously; the only reliable way to know whether the
            -- candidate's return type matches is to compare types directly.
            let e ← Lean.Elab.Term.elabTerm appStx (some expected)
            Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
            let e ← Lean.instantiateMVars e
            -- Reject candidates whose elaborated form still has
            -- unresolved metavariables — that means the args didn't
            -- fully pin the implicits and `isDefEq` would aggressively
            -- unify them downstream to make types appear to match.
            if e.hasExprMVar then
              snap.restore
            else
              let inferredType ← Lean.Meta.inferType e
              let inferredType ← Lean.instantiateMVars inferredType
              if ← Lean.Meta.isDefEq inferredType expected then
                successes := successes ++ [cand]
              snap.restore
          catch ex =>
            lastError := some ex.toMessageData
            snap.restore
        match successes with
        | [] =>
          match lastError with
          | some msg => throwError m!"atlas apply: no {kind} `{numStr}` candidate fits this application:\n{msg}"
          | none     => throwError s!"atlas apply: no {kind} `{numStr}` candidate fits this application"
        | [cand] =>
          let head := mkIdent cand
          let appStx ← `($head $args*)
          Lean.Elab.Term.elabTerm appStx expectedType?
        | _ =>
          throwError s!"atlas apply: multiple {kind} candidates at `{numStr}` fit this application: {successes}"
  | _ => Lean.Elab.throwUnsupportedSyntax

end Atlas
