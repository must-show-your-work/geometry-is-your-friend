/-
Geometry/Construction/Cache.lean — env-extension cache of solved
particle positions for `Lowering.lower`.

The force-directed solver dominates the per-figure cost (≈10-30ms
even for a 5-point construction). Most invocations re-render the same
construction over and over — every cursor move in the editor triggers
a fresh `with_atlas_panels` elaboration, which rebuilds every
progressive-figure widget. Caching the solver output by the
construction's textual hash means re-elabs on unrelated edits skip
the solver entirely.

Cache key = (solverVersion, hash printConstruction). Bump
`solverVersion` whenever the solver algorithm changes so olean-
resident entries from older algorithms get invalidated.

Cache value = solved pre-fit-to-canvas positions per named point.
`Lowering.lower` accepts a `cachedPositions` parameter; when present
it skips `buildWorld`/`Solver.solve`/`mergeSolved` and uses the
cached positions directly. Fit-to-canvas + label layout still run
each time — they're cheap and they take the canvas dimensions into
account.
-/

import Lean
import Figures
import Geometry.Construction.DSL

namespace Geometry.Construction.Cache

open Lean Figures Geometry.Construction.DSL

/-- Bump whenever the solver algorithm changes so olean-resident
entries written by an older algorithm get invalidated automatically.

History:
- v1: initial Verlet + projections + label sub-solver
- v2: multi-incidence collinear projection; noncollinear soft force
-/
def solverVersion : Nat := 2

structure Key where
  version : Nat
  hash    : UInt64
deriving DecidableEq, Hashable, Inhabited, Repr

abbrev Value := Array (Figures.Name × Pos2)

abbrev Entry := Key × Value

initialize ext : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    name          := `Geometry.Construction.Cache.ext
    addImportedFn := fun arrs => arrs.foldl (· ++ ·) #[]
    addEntryFn    := fun arr entry => arr.push entry
    toArrayFn     := List.toArray
  }

/-- Compute the cache key for a construction. -/
def keyOf (c : Construction) : Key :=
  { version := solverVersion, hash := hash (printConstruction c) }

/-- Look up a previously-stored solved position list. -/
def lookup (env : Environment) (c : Construction) : Option Value :=
  let key := keyOf c
  (ext.getState env).findSome? fun (k, v) => if k == key then some v else none

/-- Store a solved position list. Run in any monad with `MonadEnv`
access (e.g. `CoreM`, `TermElabM`, `TacticM`). -/
def store [Monad m] [MonadEnv m] (c : Construction) (val : Value) : m Unit := do
  modifyEnv (ext.addEntry · (keyOf c, val))

end Geometry.Construction.Cache
