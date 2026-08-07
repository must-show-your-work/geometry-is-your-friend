/-
Geometry/Construction/Syntax.lean — re-export shim.

The surface syntax (`construction { … }`, `constructionStmt` category)
moved to `Figures.Construction.Syntax`. This file just imports it so
existing `import Geometry.Construction.Syntax` sites keep working.
-/

import Figures.Construction.Syntax
