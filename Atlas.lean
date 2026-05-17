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
  let ident   := mkIdent (Name.mkSimple title.getString)
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
  let ident   := mkIdent (Name.mkSimple title.getString)
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
  let ident   := mkIdent (Name.mkSimple title.getString)
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
    | `(atlasNum| $i:ident . $n:num) => pure s!"{i.getId}.{n.getNat}"
    | `(atlasNum| [ $s:str ]) => pure s.getString
    | _ => throwError "atlas: malformed number reference"
  let env ← getEnv
  match atlasLookupByNumber env kind numStr with
  | []  => throwError s!"atlas: no {kind} tagged `{numStr}` found"
  | [n] =>
    -- Delegate to the standard term elaborator on a synthesised identifier
    -- so implicit-arg metavars are inserted the same way they would be
    -- when the user writes the constant name directly. Plain
    -- `mkConstWithFreshMVarLevels` returns the Π-typed constant without
    -- opening its implicit binders, which fails when the ref is used in
    -- application position against an expected type that already has
    -- those implicits resolved.
    Lean.Elab.Term.elabTerm (mkIdent n) none
  | ns  =>
    -- Multiple decls share this (kind, number). Refuse to pick one
    -- silently; list the titles so the user can disambiguate via the
    -- `«Title»` form.
    let st := atlasExt.getState env
    let titles := ns.filterMap fun n =>
      st.byName.find? n |>.map (fun e => s!"«{e.title}»")
    throwError s!"atlas: reference {kind} {numStr} is ambiguous; \
      matches {ns.length} decls — use one of: {titles}"

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
syntax:max "proposition" atlasNum : term
-- `alternate N.K` refers to an alternate proof of proposition N.K.
-- If multiple alternates share a number, the reference errors with
-- the list of titles; use «Title» to disambiguate.
syntax:max "alternate"   atlasNum : term
syntax:max "corollary"   atlasNum : term
syntax:max "exercise"    atlasNum : term
syntax:max "remark"      atlasNum : term
syntax:max "postulate"   atlasNum : term
syntax:max "definition"  atlasNum : term

-- Uniform `atlas <kind> <num>` term-position form. Works for *every*
-- atlas kind including `lemma`/`axiom`/`theorem` (which can't have bare
-- term keywords because that would reserve those tokens and break bare
-- command parsing of `lemma X.Y {b}: T := body`). The leading `"atlas"`
-- keyword disambiguates from the command form: command needs a string
-- title next, term form takes an `atlasNum` (none of whose variants
-- start with `"`, since the string-form is bracketed as `["..."]`).
syntax:max "ref" rawIdent atlasNum : term

elab_rules : term
  | `(term| proposition $n:atlasNum) => elabAtlasRefAux "proposition" n
  | `(term| alternate   $n:atlasNum) => elabAtlasRefAux "alternate"   n
  | `(term| corollary   $n:atlasNum) => elabAtlasRefAux "corollary"   n
  | `(term| exercise    $n:atlasNum) => elabAtlasRefAux "exercise"    n
  | `(term| remark      $n:atlasNum) => elabAtlasRefAux "remark"      n
  | `(term| postulate   $n:atlasNum) => elabAtlasRefAux "postulate"   n
  | `(term| definition  $n:atlasNum) => elabAtlasRefAux "definition"  n
  | `(term| ref $k:ident $n:atlasNum) =>
      elabAtlasRefAux k.getId.toString n

end Atlas
