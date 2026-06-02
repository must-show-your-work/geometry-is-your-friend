/-
Geometry/Construction/AtlasField.lean — `construction { … }` figure
field for atlas commentary blocks.

Wires the Construction DSL into atlas's `figure := by …` syntax as
sugar over `intermediate_representation`. The user writes

  figure := by
    construction {
      exists A B C : Point
      assert distinct A B C
      …
    }
    title "…"

and the macro rewrites the field to
`intermediate_representation (Geometry.Construction.DSL.construction { … })`,
which atlas handles via the `Renderable Construction String` instance.

The figure-field keyword and the term-level macro share the name
`construction`; they live in different syntax categories so there's no
conflict. Reads well in either reading: "this figure IS a
construction" or "this figure is built BY a construction".
-/

import Atlas
import Geometry.Construction.Syntax
import Geometry.Construction.Lowering

namespace Geometry.Construction

/-! ## Base-construction tracking

For the `auxillary` tactic to act as an addendum to the current
figure (rather than a standalone), we need to remember the
commentary's Construction across decl boundaries within a file. We
plumb the value through an `IO.Ref` set as a side-effect during
elaboration of the commentary's `construction { … }` field, and read
back from the proof's `auxillary` tactic.

This is per-process state: it works within the language server's
elaboration of a single file (commentary elabs before the theorem)
and within a single lake build process. Cross-file sharing needs an
env-extension upgrade. -/

initialize baseConstructionRef : IO.Ref (Option Construction.DSL.Construction) ←
  IO.mkRef none

private unsafe def registerBaseImpl (c : Construction.DSL.Construction) :
    Construction.DSL.Construction :=
  unsafeBaseIO do
    baseConstructionRef.set (some c)
    return c

@[implemented_by registerBaseImpl]
opaque registerBase (c : Construction.DSL.Construction) : Construction.DSL.Construction

def getBase : IO (Option Construction.DSL.Construction) := baseConstructionRef.get

end Geometry.Construction


open Lean Atlas

syntax (name := afConstruction)
  "construction" "{" constructionStmt* "}" : atlasFigureField

macro_rules
  | `(atlasFigureField| construction { $stmts:constructionStmt* }) =>
    `(atlasFigureField|
       intermediate_representation
         (Geometry.Construction.registerBase
            (construction { $stmts:constructionStmt* })))
