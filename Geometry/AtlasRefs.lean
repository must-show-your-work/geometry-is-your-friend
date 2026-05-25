import Lean.Elab.Command
import ProofWidgets.Data.Html
import ProofWidgets.Component.HtmlDisplay
import Atlas

/-!
# Atlas refs widget

For every atlas proof (theorem-flavored kind, not `axiom` or `definition`),
the InfoView shows a "References in <decl>" panel listing the atlas-tagged
decls cited transitively from its body. The panel renders as a three-column
table: kind+number / title / French-quoted form.

Wiring is automatic via a `macro_rules` override of the
`atlas <kind> <num> "<title>" ... := by <tacs>` pattern — every tactic-mode
atlas proof gets `with_atlas_refs` injected as a wrapping panel-widget tactic.
Term-mode bodies (`:= <expr>`) and `atlas axiom` fall through to Atlas's
own expansion.

This module is imported by `Geometry/Tactics.lean` so the override is
available wherever `Geometry.Tactics` is — which is essentially the whole
project.
-/

namespace Geometry.AtlasRefs

open Lean Meta Server ProofWidgets

/-- For a given decl name, walk its body (and any `_proof_*`/`.proof_N`
auxiliary lemmas it pulls in) collecting every transitively-referenced
atlas-tagged decl with `(kind, number, title)` metadata. Sorted by
atlas number.

Transitivity is needed because Lean factors tactic-mode proofs into
aux defs (`Pasch.proof_1`, etc.) — the outer theorem body just calls
the aux, so a non-transitive walk misses every `ref lemma X.Y.Z` that
lives inside one of those auxes. We stop the recursion at atlas-tagged
decls (those are the citation edges we want to record) and at decls
with no extractable body. -/
partial def atlasRefs (name : Name) : MetaM (Array (Name × Atlas.AtlasEntry)) := do
  let env ← getEnv
  let mut visited : NameSet := {}
  let mut found : Std.HashMap Name Atlas.AtlasEntry := {}
  let mut stack : List Name := [name]
  while !stack.isEmpty do
    let n :: rest := stack | unreachable!
    stack := rest
    if visited.contains n then continue
    visited := visited.insert n
    if n != name then
      if let some entry := Atlas.atlasEntry? env n then
        found := found.insert n entry
        continue
    let some info := env.find? n | continue
    let value? : Option Expr := match info with
      | .thmInfo t => some t.value
      | .defnInfo d => some d.value
      | _ => none
    let some body := value? | continue
    for m in body.getUsedConstants do
      if !visited.contains m then
        stack := m :: stack
  let out := found.toList.toArray.map (fun (n, e) => (n, e))
  return out.qsort fun a b => a.2.number < b.2.number

/-- Walk past leading implicit foralls, introducing each as an fvar
in the local context, then call `k` with the resulting body Expr. -/
private partial def stripImplicits (e : Expr) (k : Expr → MetaM α) : MetaM α := do
  match e with
  | .forallE name dom body bi =>
    if bi.isExplicit then k e
    else
      Meta.withLocalDecl name bi dom fun fvar => do
        stripImplicits (body.instantiate1 fvar) k
  | _ => k e

/-- Replace every `autoParam α tacName` subterm with just `α`, so the
displayed type shows the user-visible shape (e.g. `A ≠ B → …`) instead
of the elaborator-internal `autoParam (A ≠ B) _._auto_1 → …`. -/
private partial def unfoldAutoParam : Expr → Expr
  | .app (.app (.const ``autoParam _) α) _ => unfoldAutoParam α
  | .app f a => .app (unfoldAutoParam f) (unfoldAutoParam a)
  | .forallE n d b bi => .forallE n (unfoldAutoParam d) (unfoldAutoParam b) bi
  | .lam n d b bi => .lam n (unfoldAutoParam d) (unfoldAutoParam b) bi
  | .letE n t v b ndep =>
    .letE n (unfoldAutoParam t) (unfoldAutoParam v) (unfoldAutoParam b) ndep
  | .mdata d e => .mdata d (unfoldAutoParam e)
  | .proj s i e => .proj s i (unfoldAutoParam e)
  | e => e

/-- Pretty-print a decl's statement type for the InfoView panel:
- strip leading implicit binders (the `∀ {L} {A B},` prefix is noise),
- unwrap `autoParam` (the elaborator-internal default-tactic encoding
  on `(AneB : A ≠ B := by assumption)`-style binders),
- strip per-line trailing whitespace. -/
private def ppDeclType (n : Name) : MetaM String := do
  let env ← getEnv
  match env.find? n with
  | none => return ""
  | some info =>
    let cleaned := unfoldAutoParam info.type
    stripImplicits cleaned fun body => do
      let fmt ← Lean.Meta.ppExpr body
      let raw := fmt.pretty
      let lines := raw.splitOn "\n" |>.map String.trimRight
      return "\n".intercalate lines

/-- Render a single ref as a `<div>` containing a header line
(`kind number — title`) and an indented type line. Two-line per-ref
layout (instead of a table) avoids the TUI renderer's column-width
padding, which surfaces as trailing whitespace and early wrapping
in `lean.nvim`. -/
private def renderRef (n : Name) (e : Atlas.AtlasEntry) (typeStr : String) : Html :=
  let _ := n  -- kept for future linking work
  let header := Html.element "div" #[]
    #[Html.element "span"
        #[("style", json% {
            fontFamily: "JetBrains Mono, monospace",
            fontSize: "0.85em",
            color: "#268bd2"
          })]
        #[Html.text s!"{e.kind} {e.number}"],
      Html.element "span"
        #[("style", json% { color: "#888888" })]
        #[Html.text "  —  "],
      Html.element "span" #[] #[Html.text e.title]]
  let typeBlock := Html.element "div"
    #[("style", json% {
        fontFamily: "JetBrains Mono, monospace",
        fontSize: "0.85em",
        color: "#93a1a1",
        whiteSpace: "pre-wrap",
        paddingLeft: "1.5em"
      })]
    #[Html.text typeStr]
  Html.element "div"
    #[("style", json% { marginBottom: "0.5em" })]
    #[header, typeBlock]

/-- Walk a Syntax tree collecting all `ref <kind> <atlasNum>` and
`via <kind> <atlasNum>` patterns. Returns `(kindString, numberString)`
pairs — these are the atlas-DSL citations the proof body makes.

Syntactic counterpart to the env-walking `atlasRefs` above. Runs at
tactic-elaboration time when the enclosing decl isn't yet in the
environment. Misses transitive refs hidden inside `_proof_*` auxes. -/
private partial def collectAtlasRefSyntax (stx : Syntax) (acc : Array (String × String)) :
    Array (String × String) :=
  let acc :=
    if stx.getKind == ``Atlas.atlasRef then
      let kindStr := stx[1].getId.toString
      let numStx := stx[2]
      let numStr := numStx.reprint.getD ""
      acc.push (kindStr, numStr.trim)
    else acc
  stx.getArgs.foldl (init := acc) fun acc child => collectAtlasRefSyntax child acc

/-- Look up an atlas decl by (kind, number) via the live env. Returns
`none` if no atlas decl matches. -/
private def resolveAtlasRef (env : Environment) (kindStr numStr : String) :
    Option (Name × Atlas.AtlasEntry) :=
  let candidates := Atlas.atlasLookupByNumber env kindStr numStr
  candidates.head?.bind fun n => (Atlas.atlasEntry? env n).map ((n, ·))

/-- Shared Html-builder used by both `atlasRefsHtml` (env-based) and
`atlasRefsHtmlFromSyntax` (syntactic). Renders each ref's type via
`ppDeclType`, so this is MetaM. -/
private def buildHtml (name : Name) (refs : Array (Name × Atlas.AtlasEntry)) : MetaM Html := do
  let rows ← refs.mapM fun (n, e) => do
    let typeStr ← ppDeclType n
    return renderRef n e typeStr
  -- Show only the title component of the FQN (the last `.` segment is
  -- the French-quoted title), not the full `Geometry.Ch3.Prop.…` prefix.
  let titleOnly := name.getString!
  let header := Html.element "h4"
    #[("style", json% { margin: "0 0 0.5em 0" })]
    #[Html.text s!"References in {titleOnly}", Html.element "span"
        #[("style", json% { color: "#888888", marginLeft: "0.5em", fontWeight: "normal" })]
        #[Html.text s!"({refs.size})"]]
  let body : Html :=
    if refs.isEmpty then
      Html.element "p"
        #[("style", json% { color: "#888888", fontStyle: "italic" })]
        #[Html.text "(no atlas-tagged references — proof body uses only definitions / non-atlas lemmas)"]
    else
      Html.element "div" #[] rows
  return Html.element "div"
    #[("style", json% {
        fontFamily: "EB Garamond, Iowan Old Style, Georgia, serif",
        padding: "0.5em",
        border: "1px solid #93a1a1",
        borderRadius: "4px"
      })]
    #[header, body]

/-- Compute the refs Html for an atlas proof by syntactically scanning
its tactic body. Used at `with_atlas_refs` tactic time when the decl
isn't yet committed to the env. -/
def atlasRefsHtmlFromSyntax (declName : Name) (body : Syntax) : MetaM Html := do
  let env ← getEnv
  let rawPairs := collectAtlasRefSyntax body #[]
  let mut seen : Std.HashSet (String × String) := {}
  let mut refs : Array (Name × Atlas.AtlasEntry) := #[]
  for pair in rawPairs do
    if seen.contains pair then continue
    seen := seen.insert pair
    if let some entry := resolveAtlasRef env pair.1 pair.2 then
      refs := refs.push entry
  refs := refs.qsort fun a b => a.2.number < b.2.number
  buildHtml declName refs

/-- Build the full Html panel for a decl's atlas references (env-based;
used by `#refs <name>` after the decl is committed). -/
def atlasRefsHtml (name : Name) : MetaM Html := do
  let refs ← atlasRefs name
  buildHtml name refs

/-- `with_atlas_refs <tacticSeq>` — wraps a proof in a panel that displays
the enclosing decl's atlas references throughout the proof. Used directly
or injected by the `atlas`-macro override below. -/
syntax (name := withAtlasRefs) "with_atlas_refs" tacticSeq : tactic

open Elab Tactic in
@[tactic withAtlasRefs]
def elabWithAtlasRefs : Tactic := fun stx => match stx with
  | `(tactic| with_atlas_refs $seq) => do
    let some declName ← Term.getDeclName?
      | throwError "with_atlas_refs: no enclosing declaration"
    let html ← atlasRefsHtmlFromSyntax declName seq
    -- Attach the panel to `seq`'s source range (the user's actual proof
    -- body), not `stx`'s — `stx` includes our synthesized
    -- `with_atlas_refs` keyword which has no source position, so anchoring
    -- there points the widget at nowhere and the InfoView never displays it.
    Widget.savePanelWidgetInfo
      (hash HtmlDisplayPanel.javascript)
      (return json% { html: $(← rpcEncode html) })
      seq
    evalTacticSeq seq
  | _ => throwUnsupportedSyntax

-- Intercept tactic-bodied `atlas <kind> <num> "<title>" ... := by <tacs>`
-- commands and auto-wrap the body in `with_atlas_refs`. Every atlas proof
-- (theorem-flavored kind) gets the refs panel by default. Term-mode
-- bodies and body-less `atlas axiom` fall through to Atlas's own
-- `macro_rules` via `Macro.throwUnsupported`.
open Atlas in
macro_rules
  | `($[$doc?:docComment]? atlas $k:ident $n:atlasNum $t:str $bs:bracketedBinder* : $ty := by $tacs:tacticSeq) => do
    let kindStr := k.raw.getId.toString
    if kindStr == "axiom" || kindStr == "definition" then
      Macro.throwUnsupported
    let numStr ← Atlas.atlasNumToString n
    let kindLit := Syntax.mkStrLit kindStr
    let numLit := Syntax.mkStrLit numStr
    let ident := mkIdentFrom t.raw (Name.mkSimple t.getString)
    let wrappedBody ← `(by with_atlas_refs $tacs)
    match doc? with
    | some doc =>
      `($doc:docComment
        @[atlas $kindLit $numLit $t] theorem $ident $bs* : $ty := $wrappedBody)
    | none =>
      `(@[atlas $kindLit $numLit $t] theorem $ident $bs* : $ty := $wrappedBody)

end Geometry.AtlasRefs
