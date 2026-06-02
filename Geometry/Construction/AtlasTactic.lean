/-
Geometry/Construction/AtlasTactic.lean — `auxillary` tactic.

Pushes a Construction addendum into `auxillaryAddendaExt` keyed by the
current decl + source line. The actual figure widget is saved by the
progressive-figure hook (see `Geometry/Construction/ProgressiveFigure.lean`)
which runs after `evalTacticSeq`, walks the proof tree, and emits a
widget at every tactic line showing the cumulative figure for that
point in the proof.

  example := by
    …
    auxillary {
      construct rayPA := segment P A
    }
    …
-/

import Figures
import Geometry.Construction.DSL
import Geometry.Construction.Syntax
import Geometry.Construction.Lowering
import Geometry.Construction.AtlasField
import Geometry.Construction.ProgressiveFigure
import Atlas

namespace Geometry.Construction

open Lean Elab Tactic Meta

syntax (name := auxillaryTac) "auxillary" "{" constructionStmt* "}" : tactic

@[tactic auxillaryTac]
def elabAuxillary : Tactic := fun stx => do
  match stx with
  | `(tactic| auxillary { $stmts:constructionStmt* }) => do
    let some declName ← Term.getDeclName?
      | throwError "auxillary: no enclosing declaration"
    let some pos := stx.getPos? | return
    let line := (← getFileMap).toPosition pos |>.line
    let addendumStx ← `(construction { $stmts:constructionStmt* })
    let addendumExpr ← Term.elabTermAndSynthesize addendumStx none
    let addendum ← unsafe evalExpr DSL.Construction
      (mkConst ``DSL.Construction) addendumExpr
    pushAddendum declName line addendum
  | _ => throwUnsupportedSyntax

end Geometry.Construction
