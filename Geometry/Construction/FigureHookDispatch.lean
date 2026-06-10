/-
Geometry/Construction/FigureHookDispatch.lean — install figure hooks.

The DSL path lives in `ProgressiveFigure`; the proof-state path lives
in `IncrementalProofFigure`. Each registers itself with a separate
Atlas hook (post-hoc vs per-step), so they coexist without a dispatcher
chain — this file just imports both so their `initialize` blocks fire.
-/

import Geometry.Construction.ProgressiveFigure
import Geometry.Construction.IncrementalProofFigure

namespace Geometry.Construction.FigureHookDispatch

end Geometry.Construction.FigureHookDispatch
