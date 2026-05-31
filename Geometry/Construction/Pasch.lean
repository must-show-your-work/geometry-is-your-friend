/-
Geometry/Construction/Pasch.lean — Worked example: Pasch's theorem
(Ch3/Prop/Pasch.lean, atlas 3.0) encoded as a `Construction`.

Exists to exercise the IR shape. The eventual DSL → IR parser will
produce values like this one out of `figure := by …` blocks; until
then, this is a hand-encoded reference and a `#eval` round-trip
sanity check.
-/

import Geometry.Construction

namespace Geometry.Construction.Examples

open Geometry.Construction

/-- Pasch's theorem figure.

Base: distinct non-collinear points `A`, `B`, `C` plus a line `L` that
meets segment `AB` at a point `X` strictly between `A` and `B`. (The
theorem's conclusion — `L` also meets `AC` or `BC` — is not in the
figure; it's what the proof establishes.)

Extension: the sub-proof of `(segment A B : Line) ≠ (segment B C : Line)`
(pasch.lean:86) temporarily assumes `segment A B = segment B C` to derive
a contradiction. That assumption appears here as a proof-time extension
that the renderer would show as a degenerate config (C lands on AB). -/
def pasch : Construction := {
  base := [
    -- Free points and the cutting line.
    .exist "A" .point,
    .exist "B" .point,
    .exist "C" .point,
    .exist "L" .line,
    .exist "X" .point,

    -- Triangle hypotheses.
    .assert (.app "distinct" [.of "A", .of "B", .of "C"]),
    .assert (.app1 "¬" (.app "collinear" [.of "A", .of "B", .of "C"])),

    -- Sides — named so annotations / extensions can refer to them.
    .construct "segAB" (.app "segment" [.of "A", .of "B"]),
    .construct "segBC" (.app "segment" [.of "B", .of "C"]),
    .construct "segAC" (.app "segment" [.of "A", .of "C"]),

    -- X = L ∩ segAB, strictly between A and B.
    .assert (.app "incident" [.of "X", .of "L"]),
    .assert (.app "between" [.of "A", .of "X", .of "B"]),
  ]
  extensions := [
    -- pasch.lean:86 — assume segAB = segBC to render the degenerate
    -- configuration. The IR doesn't enforce that this contradicts
    -- `¬(collinear A B C)` above; downstream is on the hook.
    .assert (.app2 "="
              (.app "segment" [.of "A", .of "B"])
              (.app "segment" [.of "B", .of "C"])),
  ]
  annotations := [
    .label "A" "A",
    .label "B" "B",
    .label "C" "C",
    .label "X" "X",
    .label "L" "L",
    .highlight "L" .bold,
  ]
}

/-- Round-trip the IR back to source DSL form. `IO.println` so newlines
in the output render as actual line breaks in the InfoView, rather than
`\n` literals from `String`'s default `repr`. -/
#eval IO.println pasch.toSource

end Geometry.Construction.Examples
