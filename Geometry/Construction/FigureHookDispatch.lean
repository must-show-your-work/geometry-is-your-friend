/-
Geometry/Construction/FigureHookDispatch.lean — composite figure hook.

Overrides Atlas's `figureProgressionHookRef` with one that:
1. Tries the DSL-authored path (`ProgressiveFigure.saveProgressiveFigures`)
2. Falls back to proof-state extraction
   (`IncrementalProofFigure.saveProofStateFigures`) when no
   `construction { … }` block exists for the target.

This file is the SOLE place both hook implementations meet — it isolates
the DSL-syntax leakage (the `line` keyword from `Theory.Constructors`)
that would otherwise break `ProgressiveFigure`'s field names if it
imported the proof-state module directly.

Initialize order: this file's `initialize` runs after
`ProgressiveFigure`'s (it imports it), so this overwrite wins.
-/

import Geometry.Construction.ProgressiveFigure
import Geometry.Construction.IncrementalProofFigure

namespace Geometry.Construction.FigureHookDispatch

open Lean Elab Tactic

initialize do
  Atlas.Refs.figureProgressionHookRef.set fun k n d s => do
    if ← saveProgressiveFigures k n d s then return
    IncrementalProofFigure.saveProofStateFigures s

end Geometry.Construction.FigureHookDispatch
