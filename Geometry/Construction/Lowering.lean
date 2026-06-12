/-
Geometry/Construction/Lowering.lean — re-export shim.

The Construction → Scene Pos2 lowering moved to
`Figures.Construction.Lowering` so the constraint-translation
infrastructure lives in figures alongside the IR (`DSL`) and the
upcoming `@[constraint_handler]` registry. Consumers of giyf keep
using `Geometry.Construction.Lowering.X` through this shim; over time
import sites can migrate directly to `Figures.Construction.Lowering`
and this file can retire.
-/

import Figures.Construction.Lowering

namespace Geometry.Construction.Lowering

export Figures.Construction.Lowering
  (lower solvePositions lowerAuxiliary)

end Geometry.Construction.Lowering

namespace Geometry.Construction

export Figures.Construction (renderBare renderAuxBare)

end Geometry.Construction
