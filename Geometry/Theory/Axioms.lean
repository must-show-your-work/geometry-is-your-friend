import Geometry.Theory.Primitives
import Geometry.Theory.Collinear
import Geometry.Theory.Constructors
import Geometry.Theory.Axioms.Incidence
import Geometry.Theory.Axioms.Betweenness
import Geometry.Tactics.NormalizeEq
import Geometry.Tactics.Obvious
import Geometry.Tactics.Clearly
import Geometry.Tactics.ByExhaustion

/-!
# Axioms barrel

Re-exports the split foundation, axioms, and tactic modules. Existing
import sites (`import Geometry.Theory.Axioms`) continue to work unchanged.

The actual content lives in:
- `Geometry.Theory.Primitives` — Point, Line, on, off/has/avoids, Between
- `Geometry.Theory.Collinear` — Collinear def + syntax
- `Geometry.Theory.Constructors` — segment/ray/extension/line + intersects
- `Geometry.Theory.Axioms.Incidence` — I.1, I.2, I.3 + Concurrent + Parallel
- `Geometry.Theory.Axioms.Betweenness` — B-1a/b, B-2, density, B-3, B-4i/ii
- `Geometry.Tactics.NormalizeEq` — `normalize_eq`
- `Geometry.Tactics.Obvious` — `obvious` + the `@[obvious]` simp set
- `Geometry.Tactics.Clearly` — `clearly`
- `Geometry.Tactics.ByExhaustion` — `by_exhaustion`
-/
