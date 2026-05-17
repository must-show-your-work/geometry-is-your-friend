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
    by elab-term lookups. -/
structure AtlasState where
  byName       : NameMap AtlasEntry           := {}
  byKindNumber : Std.HashMap String Name      := {}  -- key: `"{kind}/{number}"`
  byTitle      : Std.HashMap String Name      := {}
  deriving Inhabited

private def insertEntry (s : AtlasState) (row : AtlasRow) : AtlasState :=
  let (n, k, num, t) := row
  let entry : AtlasEntry := { kind := k, number := num, title := t }
  { byName       := s.byName.insert n entry
    byKindNumber := s.byKindNumber.insert (k ++ "/" ++ num) n
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

def atlasLookupByNumber (env : Environment) (kind number : String) : Option Name :=
  (atlasExt.getState env).byKindNumber.get? (kind ++ "/" ++ number)

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
    -- Empty number is the convention for "no book reference"; skip the
    -- (kind, number) duplicate check in that case since lots of theory
    -- lemmas legitimately share the empty key.
    if !numStr.isEmpty then
      if let some existing := st.byKindNumber.get? (kindStr ++ "/" ++ numStr) then
        throwError s!"atlas: duplicate ({kindStr}, {numStr}) — already on `{existing}`"
    if let some existing := st.byTitle.get? titleStr then
      throwError s!"atlas: duplicate title \"{titleStr}\" — already on `{existing}`"
    setEnv <| atlasExt.addEntry env (decl, kindStr, numStr, titleStr)
}

/-! ## Reference-number syntax -/

declare_syntax_cat atlasNum
-- Lean lexes `3.4` / `0.1` as a single `scientific` token, NOT as
-- `num "." num` (which would require whitespace). For text-style refs
-- like `I.1`, use `ident "." num`.
syntax scientific  : atlasNum
syntax ident "." num : atlasNum

/-- Pull the source text out of a parsed scientific-literal node.
    Lean wraps the literal in a node whose first child is the atom. -/
private def scientificAtomText (s : TSyntax `scientific) : Option String :=
  match s.raw[0] with
  | .atom _ str => some str
  | _ => none

/-- Render an `atlasNum` syntax tree to the canonical string we store
    and look up. `3.4` → `"3.4"`, `I.1` → `"I.1"`. -/
def atlasNumToString : TSyntax `atlasNum → MacroM String
  | `(atlasNum| $s:scientific) =>
    match scientificAtomText s with
    | some str => return str
    | none     => Macro.throwUnsupported
  | `(atlasNum| $i:ident . $n:num) => return s!"{i.getId}.{n.getNat}"
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

-- Every kind is reached by prefixing `atlas` to the kind keyword. This
-- sidesteps the parser conflict for `theorem`/`lemma`/`axiom` — `atlas`
-- isn't reserved, so the production is unambiguous. Uniform shape:
--
--     atlas proposition 3.4 "Pasch's Postulate" : T := by …
--     atlas theorem     3.7 "Major Result"      : T := by …
--     atlas axiom       I.1 "Two-point line"    : T
-- Numbered forms: `atlas <kind> <number> "<title>" …`. The book-style.
syntax (docComment)? "atlas" "proposition" atlasNum str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "corollary"   atlasNum str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "exercise"    atlasNum str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "remark"      atlasNum str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "postulate"   atlasNum str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "definition"  atlasNum str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "theorem"     atlasNum str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "lemma"       atlasNum str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "axiom"       atlasNum str (bracketedBinder)* ":" term            : command

-- Un-numbered forms: `atlas <kind> "<title>" …`. Used for theory lemmas
-- and other things that aren't book-cited. The atlas attribute records
-- `number = ""` for these; the (kind, number) duplicate check is
-- skipped when the number is empty. Title duplicates are still
-- prohibited.
syntax (docComment)? "atlas" "proposition" str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "corollary"   str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "exercise"    str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "remark"      str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "postulate"   str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "definition"  str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "theorem"     str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "lemma"       str (bracketedBinder)* ":" term ":=" term : command
syntax (docComment)? "atlas" "axiom"       str (bracketedBinder)* ":" term            : command

macro_rules
  -- Numbered forms.
  | `($[$doc?:docComment]? atlas proposition $n:atlasNum $t:str $bs:bracketedBinder* : $ty := $b) => do
      expandAtlasTheorem "proposition" (← atlasNumToString n) t bs doc? ty b
  | `($[$doc?:docComment]? atlas corollary   $n:atlasNum $t:str $bs:bracketedBinder* : $ty := $b) => do
      expandAtlasTheorem "corollary"   (← atlasNumToString n) t bs doc? ty b
  | `($[$doc?:docComment]? atlas exercise    $n:atlasNum $t:str $bs:bracketedBinder* : $ty := $b) => do
      expandAtlasTheorem "exercise"    (← atlasNumToString n) t bs doc? ty b
  | `($[$doc?:docComment]? atlas remark      $n:atlasNum $t:str $bs:bracketedBinder* : $ty := $b) => do
      expandAtlasTheorem "remark"      (← atlasNumToString n) t bs doc? ty b
  | `($[$doc?:docComment]? atlas postulate   $n:atlasNum $t:str $bs:bracketedBinder* : $ty := $b) => do
      expandAtlasTheorem "postulate"   (← atlasNumToString n) t bs doc? ty b
  | `($[$doc?:docComment]? atlas definition  $n:atlasNum $t:str $bs:bracketedBinder* : $ty := $b) => do
      expandAtlasDef     "definition"  (← atlasNumToString n) t bs doc? ty b
  | `($[$doc?:docComment]? atlas theorem     $n:atlasNum $t:str $bs:bracketedBinder* : $ty := $b) => do
      expandAtlasTheorem "theorem"     (← atlasNumToString n) t bs doc? ty b
  | `($[$doc?:docComment]? atlas lemma       $n:atlasNum $t:str $bs:bracketedBinder* : $ty := $b) => do
      expandAtlasTheorem "lemma"       (← atlasNumToString n) t bs doc? ty b
  | `($[$doc?:docComment]? atlas axiom       $n:atlasNum $t:str $bs:bracketedBinder* : $ty) => do
      expandAtlasAxiom   "axiom"       (← atlasNumToString n) t bs doc? ty
  -- Un-numbered forms (empty `numStr`).
  | `($[$doc?:docComment]? atlas proposition $t:str $bs:bracketedBinder* : $ty := $b) =>
      expandAtlasTheorem "proposition" "" t bs doc? ty b
  | `($[$doc?:docComment]? atlas corollary   $t:str $bs:bracketedBinder* : $ty := $b) =>
      expandAtlasTheorem "corollary"   "" t bs doc? ty b
  | `($[$doc?:docComment]? atlas exercise    $t:str $bs:bracketedBinder* : $ty := $b) =>
      expandAtlasTheorem "exercise"    "" t bs doc? ty b
  | `($[$doc?:docComment]? atlas remark      $t:str $bs:bracketedBinder* : $ty := $b) =>
      expandAtlasTheorem "remark"      "" t bs doc? ty b
  | `($[$doc?:docComment]? atlas postulate   $t:str $bs:bracketedBinder* : $ty := $b) =>
      expandAtlasTheorem "postulate"   "" t bs doc? ty b
  | `($[$doc?:docComment]? atlas definition  $t:str $bs:bracketedBinder* : $ty := $b) =>
      expandAtlasDef     "definition"  "" t bs doc? ty b
  | `($[$doc?:docComment]? atlas theorem     $t:str $bs:bracketedBinder* : $ty := $b) =>
      expandAtlasTheorem "theorem"     "" t bs doc? ty b
  | `($[$doc?:docComment]? atlas lemma       $t:str $bs:bracketedBinder* : $ty := $b) =>
      expandAtlasTheorem "lemma"       "" t bs doc? ty b
  | `($[$doc?:docComment]? atlas axiom       $t:str $bs:bracketedBinder* : $ty) =>
      expandAtlasAxiom   "axiom"       "" t bs doc? ty

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
    | `(atlasNum| $i:ident . $n:num) => pure s!"{i.getId}.{n.getNat}"
    | _ => throwError "atlas: malformed number reference"
  let env ← getEnv
  match atlasLookupByNumber env kind numStr with
  | some n => Lean.Meta.mkConstWithFreshMVarLevels n
  | none   => throwError s!"atlas: no {kind} tagged `{numStr}` found"

-- `:max` precedence so these can stand in function position of an
-- application: `lemma 0.2 heq` parses as `(lemma 0.2) heq` instead of
-- consuming `heq` as part of the elab-term syntax and bailing.
syntax:max "proposition" atlasNum : term
syntax:max "corollary"   atlasNum : term
syntax:max "exercise"    atlasNum : term
syntax:max "remark"      atlasNum : term
syntax:max "postulate"   atlasNum : term
syntax:max "definition"  atlasNum : term
syntax:max "theorem"     atlasNum : term
syntax:max "lemma"       atlasNum : term
syntax:max "axiom"       atlasNum : term

elab_rules : term
  | `(term| proposition $n:atlasNum) => elabAtlasRefAux "proposition" n
  | `(term| corollary   $n:atlasNum) => elabAtlasRefAux "corollary"   n
  | `(term| exercise    $n:atlasNum) => elabAtlasRefAux "exercise"    n
  | `(term| remark      $n:atlasNum) => elabAtlasRefAux "remark"      n
  | `(term| postulate   $n:atlasNum) => elabAtlasRefAux "postulate"   n
  | `(term| definition  $n:atlasNum) => elabAtlasRefAux "definition"  n
  | `(term| theorem     $n:atlasNum) => elabAtlasRefAux "theorem"     n
  | `(term| lemma       $n:atlasNum) => elabAtlasRefAux "lemma"       n
  | `(term| axiom       $n:atlasNum) => elabAtlasRefAux "axiom"       n

end Atlas
