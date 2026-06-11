/-
Geometry/Construction/DSL.lean — re-export shim.

The IR types (`Stmt`, `Construction`) and their pretty-printers moved
to `Figures.Construction.DSL` so the figures package can host the
proof-state matcher registry alongside the types it returns. Consumers
of giyf code keep using `Geometry.Construction.DSL.X` through this
shim; over time we may migrate import sites directly to
`Figures.Construction.DSL` and retire this file.
-/

import Figures.Construction.DSL

namespace Geometry.Construction.DSL

export Figures.Construction.DSL (Stmt Construction printStmt printConstruction)

end Geometry.Construction.DSL
