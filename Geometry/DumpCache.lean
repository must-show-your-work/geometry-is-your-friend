import Lean
import Atlas
import LeanTeX

/-! ## Dump cache — fingerprint-based skip for `scripts/Dump*.lean`

Each dumper computes a fingerprint over the env state it actually
reads, compares against a sidecar `blueprint/<name>.cache.hash`,
and skips its work when the fingerprint matches. After a successful
run the new fingerprint is written.

Fingerprint composition:

- `atlasFingerprint` — names + type expr hash of every atlas-tagged
  decl. Catches added/removed decls and type changes.
- `figuresFingerprint` — keys + expr hashes from `Atlas.baseIRExprExt`.
  Catches added/removed/edited figures.
- `leanTexFingerprint` — registered decl names under `latex_pp` /
  `latex_pp_app`. Catches added/removed render rules.
- `importsFingerprint` — sorted imported module names.

`defaultFingerprint` combines atlas + figures + imports — the common
case. `DumpTypeTeX` additionally folds in the LeanTeX rule state via
`withLeanTexFingerprint` so that adding a new render rule re-renders
the JSON even when no decl types changed.

To force a re-dump from outside: `rm blueprint/<name>.cache.hash`. -/

namespace Geometry.DumpCache

open Lean

def cachePath (name : String) : System.FilePath :=
  ("blueprint" : System.FilePath) / s!"{name}.cache.hash"

def readCached (name : String) : IO (Option UInt64) := do
  let p := cachePath name
  if ← p.pathExists then
    let s := (← IO.FS.readFile p).trimAscii.toString
    match s.toNat? with
    | some n => return some n.toUInt64
    | none   => return none
  else
    return none

def writeCached (name : String) (fp : UInt64) : IO Unit := do
  IO.FS.createDirAll "blueprint"
  IO.FS.writeFile (cachePath name) (toString fp ++ "\n")

/-- Run `work` only if the fingerprint differs from the on-disk cache.
On success, writes the new fingerprint. On failure (exception raised
by `work`), leaves the cache untouched so the next run retries. -/
def runIfChanged (name : String) (fp : UInt64) (work : IO Unit) : IO Unit := do
  if (← readCached name) == some fp then
    IO.eprintln s!"[{name}] cache hit (fingerprint {fp}), skipping"
  else
    work
    writeCached name fp

/-- Merged atlas decl table: imported entries unioned with the live
extension state, live wins on conflict. Identical to the merge loop
each dumper does inline. -/
def mergedAtlasByName (env : Environment) : NameMap Atlas.AtlasEntry :=
  let imported := Atlas.atlasStateFromImports env
  let live := Atlas.atlasExt.getState env
  imported.byName.foldl (init := live.byName) fun acc n e =>
    match acc.find? n with
    | some _ => acc
    | none   => acc.insert n e

/-- Hash sorted `(declName.toString, type.hash)` pairs. -/
def atlasFingerprint (env : Environment) : UInt64 := Id.run do
  let m := mergedAtlasByName env
  let mut pairs : Array (String × UInt64) := #[]
  for (n, _) in m do
    let typeHash := match env.find? n with
      | some ci => ci.type.hash
      | none    => 0
    pairs := pairs.push (n.toString, typeHash)
  let sorted := pairs.qsort (·.1 < ·.1)
  let mut acc : UInt64 := 0
  for (n, h) in sorted do
    acc := mixHash acc (mixHash (hash n) h)
  return acc

/-- Hash sorted `(kind, num, exprHash)` triples from
`Atlas.baseIRExprExt`. -/
def figuresFingerprint (env : Environment) : UInt64 := Id.run do
  let entries := Atlas.baseIRExprExt.getState env
  let mut triples : Array (String × String × UInt64) := #[]
  for ((k, n), e) in entries do
    triples := triples.push (k, n, e.hash)
  let sorted := triples.qsort fun a b =>
    if a.1 == b.1 then a.2.1 < b.2.1 else a.1 < b.1
  let mut acc : UInt64 := 0
  for (k, n, h) in sorted do
    acc := mixHash acc (mixHash (mixHash (hash k) (hash n)) h)
  return acc

/-- Hash the registered decl names under each `latex_pp` and
`latex_pp_app` key. Two rules with identical bodies but different
locations therefore hash differently, which is what we want — a
render rule moving counts as a change. -/
def leanTexFingerprint (env : Environment) : UInt64 := Id.run do
  let mut acc : UInt64 := 0
  for (k, entries) in (LeanTeX.latexPPAttribute.ext.getState env).table.toList do
    let entriesHash := entries.foldl (init := (0 : UInt64)) fun a e =>
      mixHash a (hash e.declName.toString)
    acc := mixHash acc (mixHash (hash k.toString) entriesHash)
  for (k, entries) in (LeanTeX.latexPPAppAttribute.ext.getState env).table.toList do
    let entriesHash := entries.foldl (init := (0 : UInt64)) fun a e =>
      mixHash a (hash e.declName.toString)
    acc := mixHash acc (mixHash (hash k.toString) entriesHash)
  return acc

/-- Hash the sorted imported module name set. -/
def importsFingerprint (env : Environment) : UInt64 := Id.run do
  let names := env.allImportedModuleNames.qsort (·.toString < ·.toString)
  let mut acc : UInt64 := 0
  for n in names do
    acc := mixHash acc (hash n.toString)
  return acc

/-- Combined fingerprint covering the common dumper inputs. -/
def defaultFingerprint (env : Environment) : UInt64 :=
  mixHash (atlasFingerprint env) (mixHash (figuresFingerprint env) (importsFingerprint env))

/-- Default fingerprint plus the LeanTeX rule state — for dumpers
that read attribute-driven dispatch (currently only `DumpTypeTeX`). -/
def withLeanTexFingerprint (env : Environment) : UInt64 :=
  mixHash (defaultFingerprint env) (leanTexFingerprint env)

end Geometry.DumpCache
