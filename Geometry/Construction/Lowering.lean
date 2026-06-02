/-
Geometry/Construction/Lowering.lean — Construction → Scene Pos2.

First-cut lowering. Handles the patterns we need for "two points
determine a line" and the immediate next examples; the heavy
constraint-solving (positions discovered to satisfy quantitative
relations like `between A X B`) is stubbed and will land as a separate
pass when an example forces it.

Strategy:
- `exists … : Point` → allocate a position from a deterministic
  layout pool. Lines / circles / segments declared via `exists` get
  no position; they're expected to come in through `construct`.
- `construct name := expr` → dispatch on the expression head. Known
  shape constructors (`line_through`, `segment`, `circle`) emit the
  corresponding `Shape Pos2` referencing previously-allocated
  positions. Unknown constructors are recorded as Scene constraints
  (so they survive the lowering as metadata even when we can't
  realize them visually).
- `assert claim desc` → recorded verbatim into `Scene.constraints`.
  Asserts that constrain positions (e.g. `between`) currently shape
  no positions — solver land.

Labels for each named Point are emitted automatically. Names not
introduced via `exists Point` get no auto-label; if you want a label
for a constructed object you can add it explicitly later (e.g. via
an annotation pass).
-/

import Figures
import Figures.SVG
import Figures.Vec2
import Figures.Solver
import Geometry.Construction.DSL

namespace Geometry.Construction.Lowering

open Figures
open Geometry.Construction.DSL


/-! ## Layout pool

Deterministic position allocation for free `exists Point` declarations
on a 640×480 canvas. Pool index 0 sits at the bottom-left (~210°),
index 1 at the bottom-right (~330°), index 2 at the top (~90°), with
further indices evenly distributed. Names are alphabetized before
indexing into the pool — so the alphabetically-first point reads as
the bottom-left vertex, matching standard geometry-text conventions.
A solver pass would adjust these to satisfy quantitative asserts. -/

/-- Canonical anchor angles for the alphabetized point list. First
two slots form a horizontal AB pair at the bottom (210°, 330°), third
goes to the apex (90°), then auxiliary slots fan out across the
upper arc. Going beyond six points loops to the bottom; if Joe ever
constructs a figure with that many free points, refine then. -/
private def layoutAngle (i : Nat) : Float :=
  let deg : Float :=
    match i with
    | 0 => 210
    | 1 => 330
    | 2 => 90
    | 3 => 30
    | 4 => 150
    | _ => 270
  deg * 3.14159265358979 / 180

private def layoutPos (i : Nat) (cx cy r : Float) : Pos2 :=
  let θ := layoutAngle i
  (cx + r * θ.cos, cy - r * θ.sin)


/-! ## State

A small append-only state threaded through the statement walk. Maps
each declared name to its assigned `Pos2` (for points) plus an emitted
shape (for constructed objects). The sort tag lets us auto-label
points without needing to inspect the source statement later. -/

private structure Bindings where
  positions   : List (Name × Pos2)    := []
  sorts       : List (Name × Name)    := []
  shapes      : Array (Shape Pos2)    := #[]
  annotations : Array Annotation      := #[]
  constraints : Array Constraint      := #[]
  pointCount  : Nat                   := 0


/-! ## Statement dispatch -/

private def lookupArg (b : Bindings) : ConstraintExpr → Option Pos2
  | .name n => (b.positions.find? (fun p => p.1 == n)).map (·.2)
  | _       => none

private def addShape (b : Bindings) (s : Shape Pos2) : Bindings :=
  { b with shapes := b.shapes.push s }

private def addAnnotation (b : Bindings) (a : Annotation) : Bindings :=
  { b with annotations := b.annotations.push a }

private def addConstraint (b : Bindings) (c : Constraint) : Bindings :=
  { b with constraints := b.constraints.push c }

/-- Try to realize a `construct name := expr` as a shape. The optional
`style` overrides the shape's default style (used by `auxillary` to
render addendum shapes dashed). -/
private def applyConstruct (b : Bindings) (style : Style := .default)
    (name : Name) : ConstraintExpr → Bindings
  | .app "line_through" [a, b'] =>
    match lookupArg b a, lookupArg b b' with
    | some pa, some pb => addShape b (.line name pa pb style)
    | _, _ => addConstraint b ⟨.app "line_through" [a, b'], s!"construct {name} (unresolved)"⟩
  | .app "segment" [a, b'] =>
    match lookupArg b a, lookupArg b b' with
    | some pa, some pb => addShape b (.segment name pa pb style)
    | _, _ => addConstraint b ⟨.app "segment" [a, b'], s!"construct {name} (unresolved)"⟩
  | .app "ray" [a, b'] =>
    match lookupArg b a, lookupArg b b' with
    | some pa, some pb => addShape b (.ray name pa pb style)
    | _, _ => addConstraint b ⟨.app "ray" [a, b'], s!"construct {name} (unresolved)"⟩
  | .app "circle" [c, .num r] =>
    match lookupArg b c with
    | some pc => addShape b (.circle name pc r style)
    | none    => addConstraint b ⟨.app "circle" [c, .num r], s!"construct {name} (unresolved)"⟩
  | other =>
    addConstraint b ⟨other, s!"construct {name} (unknown shape)"⟩

/-- Collect every `exists … : Point` name in source order. -/
private def collectPointNames (stmts : Array Stmt) : Array Name :=
  stmts.foldl (init := #[]) fun acc s => match s with
    | .«exists» names "Point" => acc ++ names
    | _ => acc

/-- Phase 1: register the name. Points get a layout-pool position
indexed by their alphabetical rank in the full point-name list (so
the alphabetically-first point lands at bottom-left). Non-Point sorts
get a sort tag only. Shapes / labels for points are emitted in
phase 3 once positions are final. -/
private def applyExists (b : Bindings) (alphabetized : Array Name) (cx cy r : Float)
    (names : Array Name) (sort : Name) : Bindings :=
  names.foldl (init := b) fun acc n =>
    match sort with
    | "Point" =>
      let idx := alphabetized.findIdx? (· == n) |>.getD 0
      let pos := layoutPos idx cx cy r
      { acc with
        positions := (n, pos) :: acc.positions
        sorts := (n, sort) :: acc.sorts
        pointCount := acc.pointCount + 1
      }
    | _ =>
      { acc with sorts := (n, sort) :: acc.sorts }

/-- Phase 2: record the assert as Scene metadata. Position-affecting
asserts are handled by the solver (`buildWorld` collects projections);
this pass is pure metadata now. -/
private def applyAssert (b : Bindings) (claim : ConstraintExpr) (desc : String) : Bindings :=
  addConstraint b ⟨claim, desc⟩

/-- Every point name P such that `incident P L` / `on P L` appears
in the recorded constraints, in source order. Used by
`emitDeclaredShapes`: one anchor draws the line through the anchor +
a default direction; two or more anchors draws the line through the
first two anchors (uniquely determined). -/
private def lineAnchors (b : Bindings) (lineName : Name) : Array Pos2 :=
  b.constraints.filterMap fun c => match c.claim with
    | .app op [.name p, .name l] =>
      if (op == "incident" || op == "on") && l == lineName then
        lookupArg b (.name p)
      else none
    | _ => none

/-- Direction vector for the `idx`-th existentially-declared Line.
Cycles through four slopes so multiple lines sharing the same anchor
(e.g. two `assert incident X L`/`incident X M` on the same point) don't
draw on top of each other. -/
private def lineDir (idx : Nat) : Pos2 :=
  match idx % 4 with
  | 0 => (100, 100)
  | 1 => (100, -100)
  | 2 => (140, 30)
  | _ => (30, 140)

/-- Phase 3: emit shapes for each `exists`-declared name now that
positions are final.
- `Point`: emit `.point` + auto-label.
- `Line`: anchored by `incident P L` / `on P L` asserts.
  - 0 anchors → skip (nothing to draw).
  - 1 anchor → line through anchor with the cycled default direction,
    so multiple lines through the same anchor render at different slopes.
  - 2+ anchors → line through the first two anchors (uniquely
    determined by two points). The cycled direction is ignored. -/
private def emitDeclaredShapes (b : Bindings) : Bindings :=
  let (final, _) := b.sorts.foldr (init := (b, 0)) fun (n, sort) (acc, lineIdx) =>
    match sort with
    | "Point" =>
      match lookupArg acc (.name n) with
      | some pos =>
        let acc := addShape acc (.point n pos)
        (addAnnotation acc (.label n n), lineIdx)
      | none => (acc, lineIdx)
    | "Line" =>
      let anchors := lineAnchors acc n
      if anchors.size ≥ 2 then
        let p₁ := anchors[0]!
        let p₂ := anchors[1]!
        let acc := addShape acc (.line n p₁ p₂ .bold)
        (addAnnotation acc (.label n n), lineIdx + 1)
      else if anchors.size == 1 then
        let anchor := anchors[0]!
        let dir := lineDir lineIdx
        let p₁ : Pos2 := (anchor.x - dir.x, anchor.y - dir.y)
        let p₂ : Pos2 := (anchor.x + dir.x, anchor.y + dir.y)
        let acc := addShape acc (.line n p₁ p₂ .bold)
        (addAnnotation acc (.label n n), lineIdx + 1)
      else (acc, lineIdx)
    | _ => (acc, lineIdx)
  final


/-! ## Axis pair

Used by the solver to pin the figure's canonical orientation. We pick
the alphabetically-earliest pair of points that anchor a segment / line
/ ray construct — for Pasch (segments AB, BC, AC) this is (A, B); for
TwoPointsLine (line PQ) it is (P, Q). Both endpoints are pinned at
their warm-start positions so the resulting figure reads "A on the
left, B on the right, AB horizontal" without a post-pass rotation. -/

/-- Collect (name, name) pairs of points that anchor a segment or
line. Each pair is sorted internally so (A, B) and (B, A) collide. -/
private def axisCandidates (stmts : Array Stmt) : Array (Name × Name) :=
  let fromConstructs := stmts.filterMap fun
    | .construct _ (.app "segment" [.name a, .name b]) =>
      if a < b then some (a, b) else some (b, a)
    | .construct _ (.app "line_through" [.name a, .name b]) =>
      if a < b then some (a, b) else some (b, a)
    | .construct _ (.app "ray" [.name a, .name b]) =>
      if a < b then some (a, b) else some (b, a)
    | _ => none
  fromConstructs.qsort (fun (a₁, b₁) (a₂, b₂) =>
    if a₁ != a₂ then a₁ < a₂ else b₁ < b₂)



/-! ## Fit-to-canvas scaling

The layout pool places points on a circle of conservative radius. With
a wider canvas (1280×480), that leaves most of the canvas empty. After
rotation + centering, compute the bounding box of all shape positions
and scale uniformly around the canvas center so the figure fills most
of the available space (with a margin for labels). -/

private def pointPositions (shapes : Array (Shape Pos2)) : Array Pos2 :=
  shapes.filterMap fun
    | .point _ p _ => some p
    | _ => none

private def boundingBox (positions : Array Pos2) : Option (Pos2 × Pos2) :=
  if positions.isEmpty then none
  else
    let init := positions[0]!
    let bounds := positions.foldl (init := (init, init)) fun (mn, mx) p =>
      ((min mn.x p.x, min mn.y p.y), (max mx.x p.x, max mx.y p.y))
    some bounds

private def shapeScale (cx cy s : Float) : Shape Pos2 → Shape Pos2 :=
  let sc (p : Pos2) : Pos2 := (cx + (p.x - cx) * s, cy + (p.y - cy) * s)
  fun shape => match shape with
  | .point id p st       => .point id (sc p) st
  | .segment id a b st   => .segment id (sc a) (sc b) st
  | .ray id a b st       => .ray id (sc a) (sc b) st
  | .line id a b st      => .line id (sc a) (sc b) st
  | .circle id c r st    => .circle id (sc c) (r * s) st
  | .text id p t         => .text id (sc p) t

/-- Translate so the bbox center lands at the canvas center, then
scale uniformly so the bbox fits within 0.85 of the canvas dimensions.
A single combined pass — separating "center" and "scale" caused the
apex to clip when the centroid (average of point positions) differed
from the bbox geometric center (which is what fit-to-canvas reasons
about). -/
private def fitToCanvas (shapes : Array (Shape Pos2)) (canvasW canvasH : Float) : Array (Shape Pos2) :=
  match boundingBox (pointPositions shapes) with
  | none => shapes
  | some (mn, mx) =>
    let figW := mx.x - mn.x
    let figH := mx.y - mn.y
    if figW < 1e-9 && figH < 1e-9 then shapes
    else
      let canvasCx := canvasW / 2
      let canvasCy := canvasH / 2
      let bboxCx := (mn.x + mx.x) / 2
      let bboxCy := (mn.y + mx.y) / 2
      -- 0.70 = ~15% margin per side, leaves room for labels on the
      -- outside without the figure crowding the canvas edges.
      let scaleX := if figW < 1e-9 then 1 else canvasW * 0.70 / figW
      let scaleY := if figH < 1e-9 then 1 else canvasH * 0.70 / figH
      let s := min scaleX scaleY
      let transform (p : Pos2) : Pos2 :=
        (canvasCx + (p.x - bboxCx) * s, canvasCy + (p.y - bboxCy) * s)
      shapes.map fun shape => match shape with
      | .point id p st       => .point id (transform p) st
      | .segment id a b st   => .segment id (transform a) (transform b) st
      | .ray id a b st       => .ray id (transform a) (transform b) st
      | .line id a b st      => .line id (transform a) (transform b) st
      | .circle id c r st    => .circle id (transform c) (r * s) st
      | .text id p t         => .text id (transform p) t


/-! ## Top-level lowering

Four-phase walk:
1. `exists` declarations seed positions from the alphabetized layout
   pool (alphabetically-first name → bottom-left, etc.).
2. `assert` claims apply (some bias positions, e.g. `between`).
3. Shapes for declared names are emitted (`exists`-points and any
   line materialized via incidence).
4. `construct` statements emit further shapes referencing positions
   resolved by the prior phases.
Final pass translates everything so the point centroid sits at the
canvas center. -/

/-! ## Force-directed solver pass

Phase A wires the heuristic layout into the solver as a *warm start*:
points seeded by `applyExists` are loaded into a `World`, springs are
added for each edge-shaped construct (segment / line_through / ray),
random rest-length jitter breaks accidental symmetries (e.g. exact
equilateral triangles), and the solver runs to equilibrium. The
resulting positions overwrite `Bindings.positions`. Asserts and
shape emission downstream see the perturbed positions. -/

/-- Deterministic [lo, hi] jitter from a (seed, index) pair. Used to
randomize spring rest lengths and stiffnesses so output isn't
accidentally symmetric. Same construction → same seed → same jitter
→ identical positions across re-elabs. -/
private def jitterAt (seed : UInt64) (i : UInt64) (lo hi : Float) : Float :=
  let h := hash (seed, i)
  let m := (h % 10000).toFloat / 10000.0
  lo + m * (hi - lo)

/-- Edge constructs in stmts (segment / line_through / ray) → list of
endpoint-name pairs. Order preserved. -/
private def edgeConstructs (stmts : Array Stmt) : Array (Name × Name) :=
  stmts.filterMap fun
    | .construct _ (.app "segment" [.name a, .name b])      => some (a, b)
    | .construct _ (.app "line_through" [.name a, .name b]) => some (a, b)
    | .construct _ (.app "ray" [.name a, .name b])          => some (a, b)
    | _ => none

/-- All `between A X B` triples in stmts, projected through `nameToIdx`. -/
private def collectBetweens (stmts : Array Stmt) (nameToIdx : Name → Option Nat) :
    Array (Nat × Nat × Nat) :=
  stmts.filterMap fun
    | .assert (.app "between" [.name a, .name x, .name b]) _ => do
      let ia ← nameToIdx a
      let ix ← nameToIdx x
      let ib ← nameToIdx b
      some (ia, ix, ib)
    | _ => none

/-- Group `incident P L` / `on P L` asserts by the line name. Returns
a list of (lineName, [pointNames-in-source-order]). -/
private def incidenceGroups (stmts : Array Stmt) : List (Name × List Name) := Id.run do
  let mut groups : List (Name × List Name) := []
  for s in stmts do
    match s with
    | .assert (.app op [.name p, .name l]) _ =>
      if op == "incident" || op == "on" then
        groups := match groups.find? (·.1 == l) with
          | some _ =>
            groups.map fun (ln, ps) =>
              if ln == l then (ln, ps ++ [p]) else (ln, ps)
          | none => groups ++ [(l, [p])]
    | _ => pure ()
  return groups

/-- Collect projections from `assert` stmts.

- A `between A X B` whose middle particle X appears in only one
  `between` assert becomes `Projections.between`, snapping X onto
  segment AB interior.
- When two `between` asserts share the same middle X (e.g. `between
  A X B` and `between C X D`), they collapse into one
  `Projections.intersect2` that snaps X to the intersection of lines
  AB and CD.
- `collinear A B C ...` snaps the rest onto the line through the
  first two.
- Multi-incidence on the same Line (`incident P L`, `incident Q L`,
  `incident R L`, ...) collapses to one collinear projection over the
  incident points. The first two define the line; later ones get
  snapped onto it.
- Single-anchor `incident P L` doesn't yield a projection — the
  line's geometry is defined by the one point and the cycled default
  direction in `emitDeclaredShapes`.
- Pure metadata asserts (`distinct`, `¬`, ...) produce no
  projection. -/
private def buildProjections (stmts : Array Stmt) (nameToIdx : Name → Option Nat) :
    Array Solver.Projection := Id.run do
  let betweens := collectBetweens stmts nameToIdx
  let mut grouped : List (Nat × List (Nat × Nat)) := []
  for (a, x, b) in betweens do
    grouped := match grouped.find? (·.1 == x) with
      | some _ =>
        grouped.map fun (xi, abs) => if xi == x then (xi, (a, b) :: abs) else (xi, abs)
      | none => (x, [(a, b)]) :: grouped
  let mut projs : Array Solver.Projection := #[]
  for (x, abs) in grouped do
    match abs with
    | [(a, b)] =>
      projs := projs.push (Solver.Projections.between a x b)
    | (a1, b1) :: (a2, b2) :: _ =>
      projs := projs.push (Solver.Projections.intersect2 a1 b1 a2 b2 x)
    | [] => pure ()
  for s in stmts do
    match s with
    | .assert (.app "collinear" args) _ =>
      let ids := args.filterMap fun
        | .name n => nameToIdx n
        | _ => none
      if ids.length ≥ 2 then
        projs := projs.push (Solver.Projections.collinear ids)
    | _ => pure ()
  for (_, points) in incidenceGroups stmts do
    if points.length ≥ 3 then
      let ids := points.filterMap nameToIdx
      if ids.length ≥ 2 then
        projs := projs.push (Solver.Projections.collinear ids)
  return projs

/-- Build a `Solver.World` from the seeded `Bindings` plus the
construction stmts. Each Point becomes a Particle; each edge construct
adds a Spring with jittered rest length; each position-affecting
assert adds a Projection; soft preferences (horizon, apex-up, pair
repulsion, bounds cage) are registered as Forces. -/
private def buildWorld (b : Bindings) (stmts : Array Stmt) (seed : UInt64)
    (cx cy r : Float) : Solver.World :=
  let positionsArr := b.positions.toArray
  let nameToIdx (n : Name) : Option Nat :=
    positionsArr.findIdx? (fun p => p.1 == n)
  -- Pin both endpoints of the alphabetically-earliest axis pair at
  -- canonical horizontal positions: (cx − r·√3/2, cy + r/2) and
  -- (cx + r·√3/2, cy + r/2). Alphabetically-first endpoint goes left.
  -- Overriding the warm-start positions here (rather than reusing
  -- them) makes the horizon trivially right for axis pairs whose
  -- endpoints aren't (A, B) — e.g. when the axis is (A, E) the warm
  -- start would place them on a vertical, not horizontal, line.
  --
  -- Exception: when two `between` asserts share a middle particle
  -- (which collapses to an `intersect2` projection), the axis pair
  -- fights the intersection — A and B want to be at canonical
  -- positions but the projection wants X at AB ∩ CD, and the spring
  -- network can't reach a scissor configuration with A, B pinned.
  -- Skip pinning in that case and let springs find their own
  -- equilibrium.
  let hasMultiBetween : Bool := Id.run do
    let xs := (collectBetweens stmts nameToIdx).map (·.2.1)
    for x in xs do
      let c := xs.foldl (init := 0) fun acc y => if y == x then acc + 1 else acc
      if c ≥ 2 then return true
    return false
  let axisIds? : Option (Nat × Nat) :=
    if hasMultiBetween then none
    else do
      let pair ← (axisCandidates stmts)[0]?
      let ia ← nameToIdx pair.1
      let ib ← nameToIdx pair.2
      some (ia, ib)
  let axisLeft  : Pos2 := (cx - r * 0.866, cy + r * 0.5)
  let axisRight : Pos2 := (cx + r * 0.866, cy + r * 0.5)
  let particles : Array Solver.Particle :=
    positionsArr.mapIdx fun i np =>
      match axisIds? with
      | some (a, b) =>
        if i == a then
          { id := i, name := np.1, pos := axisLeft,  prev := axisLeft,  pinned := true }
        else if i == b then
          { id := i, name := np.1, pos := axisRight, prev := axisRight, pinned := true }
        else
          { id := i, name := np.1, pos := np.2, prev := np.2, pinned := false }
      | none =>
        { id := i, name := np.1, pos := np.2, prev := np.2, pinned := false }
  let edges := edgeConstructs stmts
  let constructSprings : Array Solver.Spring := edges.zipIdx.filterMap fun (e, idx) => do
    let ia ← nameToIdx e.1
    let ib ← nameToIdx e.2
    some {
      a := ia, b := ib,
      rest := r * jitterAt seed (idx.toUInt64) 0.5 1.5,
      stiffness := jitterAt seed (idx.toUInt64 * 2 + 1) 0.7 1.3
    }
  -- For each `between A X B`, also add springs A-X and X-B at half
  -- the baseline rest length so the endpoints A, B are pulled toward
  -- bracketing X. Important when X has an `intersect2` projection: X
  -- is held at the line intersection, and these springs pull A and B
  -- in along the lines so the visible segments actually pass through
  -- X rather than terminate before reaching it.
  let betweenSprings : Array Solver.Spring := Id.run do
    let mut ss : Array Solver.Spring := #[]
    let mut idx : UInt64 := 1000
    for (ia, ix, ib) in collectBetweens stmts nameToIdx do
      ss := ss.push {
        a := ia, b := ix,
        rest := r * 0.5 * jitterAt seed idx 0.8 1.2,
        stiffness := jitterAt seed (idx + 1) 0.7 1.3
      }
      ss := ss.push {
        a := ix, b := ib,
        rest := r * 0.5 * jitterAt seed (idx + 2) 0.8 1.2,
        stiffness := jitterAt seed (idx + 3) 0.7 1.3
      }
      idx := idx + 4
    return ss
  let springs := constructSprings ++ betweenSprings
  let projections := buildProjections stmts nameToIdx
  -- Soft preferences. The axis pair (alphabetically earliest segment-
  -- like construct) drives horizon + apex-up forces. `pairRepulsion`
  -- prevents collapse; `boundsCage` keeps the figure inside the
  -- working area so post-solver fit-to-canvas isn't ill-conditioned.
  let forces : Array Solver.Force := Id.run do
    let mut fs : Array Solver.Force := #[]
    fs := fs.push (Solver.Forces.pairRepulsion (strength := 0.05) (cutoff := r * 0.6))
    fs := fs.push (Solver.Forces.boundsCage cx cy (r * 1.1) (r * 1.1) 0.05)
    -- Axis pair is pinned, so `horizonHorizontal` would no-op. The
    -- `apexUp` force still applies to the non-axis particles, pushing
    -- any below-axis points toward the upper half.
    match axisIds? with
    | some (ia, ib) =>
      fs := fs.push (Solver.Forces.apexUp ia ib 0.5)
    | none => pure ()
    -- `¬ collinear A B C` (parsed as `.app "¬" [.app "collinear" ...]`)
    -- and `noncollinear A B C` both → soft inverse-area repulsion
    -- keeping the triangle from degenerating to a line. Activates
    -- only when |signed area| drops below `r * r * 0.02` (small
    -- fraction of a typical figure's footprint).
    let inner? : ConstraintExpr → Option (Name × Name × Name)
      | .app "noncollinear" [.name a, .name b, .name c] => some (a, b, c)
      | .app "¬" [.app "collinear" [.name a, .name b, .name c]] => some (a, b, c)
      | _ => none
    for s in stmts do
      match s with
      | .assert claim _ =>
        match inner? claim with
        | some (na, nb, nc) =>
          match nameToIdx na, nameToIdx nb, nameToIdx nc with
          | some ia, some ib, some ic =>
            fs := fs.push
              (Solver.Forces.noncollinear ia ib ic
                (strength := 0.2) (threshold := r * r * 0.02))
          | _, _, _ => pure ()
        | none => pure ()
      | _ => pure ()
    return fs
  { particles := particles, springs := springs,
    projections := projections, forces := forces }


/-- Write solved particle positions back into `Bindings.positions`.
Iterates particles in order; each particle's `name` is matched
against the bindings list. -/
private def mergeSolved (b : Bindings) (w : Solver.World) : Bindings :=
  let updated := b.positions.map fun (n, oldPos) =>
    match w.particles.find? (fun p => p.name == n) with
    | some p => (n, p.pos)
    | none   => (n, oldPos)
  { b with positions := updated }

/-- Seed for the construction's RNG. Hashes the printed form so any
AST change perturbs the seed. -/
private def constructionSeed (c : Construction) : UInt64 :=
  hash (printConstruction c)


/-! ## Label layout pass

After all shapes are emitted and fit-to-canvas has finalized positions,
each `.label` annotation gets a solved offset via the label sub-solver
(`Figures.Solver.Labels`). Each labeled anchor becomes a "ghost"
particle tethered to its anchor at the standoff distance; the ghosts
repel each other and the visible segments. The resulting offsets are
written back into the annotation list so the SVG backend uses them
directly instead of falling back to its center-radial heuristic. -/

private def shapeAnchorFor (canvasW canvasH : Float) (shapes : Array (Shape Pos2))
    (target : Name) : Option Pos2 :=
  shapes.findSome? fun
    | .point id pos _ =>
      if id == target then some pos else none
    | .segment id a b _ =>
      if id == target then some ((a.x + b.x) / 2, (a.y + b.y) / 2) else none
    | .ray id a b _ =>
      if id == target then
        let dx := b.x - a.x
        let dy := b.y - a.y
        some (b.x + dx * 0.25, b.y + dy * 0.25)
      else none
    | .line id _ _ _ =>
      -- Approximate the line anchor as roughly the upper-left margin
      -- — the same convention the SVG backend uses for line labels.
      if id == target then some (60, 60) else none
    | .circle id c _ _ =>
      if id == target then some c else none
    | .text id pos _ =>
      if id == target then some pos else none

/-- Extract the endpoints of every visible-segment shape (segments,
rays, lines) so the label solver can repel ghosts away from them.
Points and circles aren't repulsive. -/
private def visibleSegments (shapes : Array (Shape Pos2)) :
    Array Solver.Labels.VisibleSegment :=
  shapes.filterMap fun
    | .segment _ a b _ => some { a, b }
    | .ray _ a b _     => some { a, b }
    | .line _ a b _    => some { a, b }
    | _ => none

/-- Run the label sub-solver and rewrite each `.label` annotation
with its solved offset. Annotations whose target has no anchor in
the shapes list are preserved as-is. -/
private def solveLabels (canvasW canvasH : Float) (shapes : Array (Shape Pos2))
    (annotations : Array Annotation) : Array Annotation := Id.run do
  let segments := visibleSegments shapes
  -- Pair each label with (anchor, initial ghost position).
  -- Initial ghost = anchor + standoff in the canvas-center-outward
  -- direction (matching the SVG heuristic). The solver moves it from
  -- there to clear segments and other ghosts.
  let standoff : Float := 28
  let cx := canvasW / 2
  let cy := canvasH / 2
  let initial : Array (Option (Solver.Labels.Ghost × Nat)) :=
    annotations.mapIdx fun idx ann => match ann with
      | .label target _ _ =>
        match shapeAnchorFor canvasW canvasH shapes target with
        | none => none
        | some anchor =>
          let dx := anchor.x - cx
          let dy := anchor.y - cy
          let len := (dx * dx + dy * dy).sqrt
          let init : Pos2 :=
            if len < 1e-9 then (anchor.x, anchor.y - standoff)
            else (anchor.x + dx / len * standoff, anchor.y + dy / len * standoff)
          some ({ anchor, pos := init, prev := init }, idx)
      | _ => none
  let ghosts := initial.filterMap id |>.map (·.1)
  let idxMap := initial.filterMap id |>.map (·.2)
  if ghosts.isEmpty then return annotations
  let w₀ : Solver.Labels.World := { ghosts, segments }
  let solved := Solver.Labels.solve {} w₀
  -- Write each ghost's offset (pos − anchor) into the matching annotation.
  let mut anns := annotations
  for i in [0 : solved.ghosts.size] do
    let g := solved.ghosts[i]!
    let off : Pos2 := (g.pos.x - g.anchor.x, g.pos.y - g.anchor.y)
    let annIdx := idxMap[i]!
    anns := anns.modify annIdx fun
      | .label target text _ => .label target text (some off)
      | other => other
  return anns

/-- Override a bindings' positions from an externally-supplied list
(e.g. cache hit). Names not in `provided` keep their current
position; names in `provided` but not in `b.positions` are added. -/
private def applyCachedPositions (b : Bindings) (provided : Array (Name × Pos2)) :
    Bindings :=
  let lookupCached (n : Name) : Option Pos2 :=
    (provided.find? (fun p => p.1 == n)).map (·.2)
  let updated := b.positions.map fun (n, oldPos) =>
    match lookupCached n with
    | some p => (n, p)
    | none   => (n, oldPos)
  { b with positions := updated }

/-- Run the solver phase only: seed positions from the layout pool,
build the World, run `Solver.solve`, return the solved positions
keyed by name. This is the expensive step; `Geometry.Construction.Cache`
memoizes its output across re-elabs. -/
def solvePositions (c : Construction) (canvasW : Float := 1280)
    (canvasH : Float := 720) : Array (Name × Pos2) :=
  let cx := canvasW / 2
  let cy := canvasH / 2
  let r  := min cx cy * 0.75
  let alphabetized := (collectPointNames c.stmts).qsort (· < ·)
  let b₀ : Bindings := {}
  let b₁ := c.stmts.foldl (init := b₀) fun acc s => match s with
    | .«exists» names sort => applyExists acc alphabetized cx cy r names sort
    | _ => acc
  let seed := constructionSeed c
  let world := buildWorld b₁ c.stmts seed cx cy r
  let solved := Solver.solve {} world
  solved.particles.map fun p => (p.name, p.pos)

def lower (c : Construction) (canvasW : Float := 1280) (canvasH : Float := 720)
    (cachedPositions : Option (Array (Name × Pos2)) := none) : Scene Pos2 :=
  let cx := canvasW / 2
  let cy := canvasH / 2
  let r  := min cx cy * 0.75
  let alphabetized := (collectPointNames c.stmts).qsort (· < ·)
  let b₀ : Bindings := {}
  let b₁ := c.stmts.foldl (init := b₀) fun acc s => match s with
    | .«exists» names sort => applyExists acc alphabetized cx cy r names sort
    | _ => acc
  let b₁' := match cachedPositions with
    | some positions => applyCachedPositions b₁ positions
    | none =>
      let seed := constructionSeed c
      let world := buildWorld b₁ c.stmts seed cx cy r
      let solved := Solver.solve {} world
      mergeSolved b₁ solved
  let b₂ := c.stmts.foldl (init := b₁') fun acc s => match s with
    | .assert claim desc => applyAssert acc claim desc
    | _ => acc
  let b₃ := emitDeclaredShapes b₂
  let b₄ := c.stmts.foldl (init := b₃) fun acc s => match s with
    | .construct name expr => applyConstruct acc .default name expr
    | _ => acc
  let fitted := fitToCanvas b₄.shapes canvasW canvasH
  let labeled := solveLabels canvasW canvasH fitted b₄.annotations
  {
    shapes      := fitted
    annotations := labeled
    constraints := b₄.constraints
  }


/-- Lower a base construction plus an addendum, rendering addendum's
constructed shapes with `.dashed` style (visual "construction line"
convention — these are auxiliary, not part of the canonical figure).
Addendum's `exists`/`assert` stmts process normally and can move
positions / declare new points; only the `construct` lines get the
dashed override. -/
def lowerAuxiliary (base : Construction) (addendum : Construction)
    (canvasW : Float := 1280) (canvasH : Float := 720)
    (cachedPositions : Option (Array (Name × Pos2)) := none) : Scene Pos2 :=
  let cx := canvasW / 2
  let cy := canvasH / 2
  let r  := min cx cy * 0.75
  let combinedStmts := base.stmts ++ addendum.stmts
  let combined : Construction := { stmts := combinedStmts }
  let alphabetized := (collectPointNames combinedStmts).qsort (· < ·)
  let b₀ : Bindings := {}
  let b₁ := combinedStmts.foldl (init := b₀) fun acc s => match s with
    | .«exists» names sort => applyExists acc alphabetized cx cy r names sort
    | _ => acc
  let b₁' := match cachedPositions with
    | some positions => applyCachedPositions b₁ positions
    | none =>
      let seed := constructionSeed combined
      let world := buildWorld b₁ combinedStmts seed cx cy r
      let solved := Solver.solve {} world
      mergeSolved b₁ solved
  let b₂ := combinedStmts.foldl (init := b₁') fun acc s => match s with
    | .assert claim desc => applyAssert acc claim desc
    | _ => acc
  let b₃ := emitDeclaredShapes b₂
  let b₄ := base.stmts.foldl (init := b₃) fun acc s => match s with
    | .construct name expr => applyConstruct acc .default name expr
    | _ => acc
  let b₅ := addendum.stmts.foldl (init := b₄) fun acc s => match s with
    | .construct name expr => applyConstruct acc .dashed name expr
    | _ => acc
  let fitted := fitToCanvas b₅.shapes canvasW canvasH
  let labeled := solveLabels canvasW canvasH fitted b₅.annotations
  {
    shapes      := fitted
    annotations := labeled
    constraints := b₅.constraints
  }


end Geometry.Construction.Lowering


namespace Geometry.Construction

open Figures
open Geometry.Construction.DSL
open Geometry.Construction.Lowering

/-- DSL → SVG via the lowering pass. Lets atlas's `direct_rep` accept
a `Construction` literal directly (instance lookup picks this up by
type), without callers needing to invoke `lower` themselves. -/
instance : Renderable Construction String where
  render c := Renderable.render (lower c)

end Geometry.Construction
