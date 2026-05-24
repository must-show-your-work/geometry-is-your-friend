import Geometry.Tactics
import Geometry.Theory.Primitives
import Geometry.Theory.Constructors
import Geometry.Tactics.NormalizeEq
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Insert

/-!
# `obvious` tactic — v2 (stage-based cascade)

Each *stage* has a `preamble` (run once) and a list of `closers` (tried
one-by-one on the post-preamble state). A stage closes the goal iff some
closer succeeds. If preamble fails (e.g. `simp_all made no progress`),
closers still run against the *original* state — more permissive than
v1's strict `simp_all ; tauto`, which now also closes goals where the
simp_all step was unnecessary.

The structure makes "try a different closer after the same preamble" the
default operation: `simp_all only [obvious]` now runs once per `obvious`
call regardless of whether `done` or `tauto` ultimately closes.

## Tracing

`set_option trace.obvious true`:
- Success: `closed by <stage> → <closer> (preamble Xms, closer Yms)`
- Failure: per-stage breakdown with preamble + each closer's elapsed ms.
-/

initialize Lean.registerTraceClass `obvious

namespace Geometry.Theory

attribute [obvious]
  -- set
  Set.mem_setOf_eq Set.mem_union Set.mem_inter_iff Set.mem_singleton_iff
  -- finset
  Finset.mem_insert Finset.mem_singleton Finset.mem_erase Finset.notMem_empty
  -- propositional
  ne_eq true_or or_true false_or or_false or_self
  true_and and_true false_and and_false and_self
  not_true_eq_false not_false_eq_true not_or not_and not_not

attribute [obvious]
  Set.subset_def
  Set.subset_inter_iff

/-! ## Cascade structure -/

open Lean Lean.Elab.Tactic in
/-- A single stage: shared `preamble` runs once, then each `closer` is
    tried in turn against the saved post-preamble state. The `applies`
    predicate is a goal-shape gate — when it returns `false`, the stage
    is skipped entirely (preamble + closers). Default `applies` returns
    `true` (always-run); topic stages override it to check for distinctive
    constants in the goal + hypothesis types. -/
private structure ObviousStage where
  name : String
  applies : MVarId → TacticM Bool := fun _ => pure true
  preamble : TSyntax `tactic
  closers : Array (String × TSyntax `tactic)

open Lean Lean.Elab.Tactic in
/-- Run `tac` with explicit save/restore on failure. Returns `(succeeded?, ms)`.
    On failure the proof state is rolled back; on success state changes stand. -/
private def tryTimed (tac : TSyntax `tactic) : TacticM (Bool × Nat) := do
  let s ← saveState
  let startMs ← IO.monoMsNow
  let ok ← try evalTactic tac; pure true catch _ => s.restore; pure false
  let endMs ← IO.monoMsNow
  return (ok, endMs - startMs)

open Lean Lean.Meta Lean.Elab.Tactic in
/-- Does the main goal or any hypothesis mention the constant `c`?
    Walks `Expr`s with `Expr.find?`, single traversal each. Used by
    stage `applies` predicates to gate topic-specific stages on
    whether the topic's constant is in scope. -/
private def goalMentions (c : Name) (g : MVarId) : TacticM Bool := do
  g.withContext do
    let targetHas ← do
      let t ← g.getType
      pure (t.find? (·.isConstOf c)).isSome
    if targetHas then return true
    for ld in ← getLCtx do
      if ld.isImplementationDetail then continue
      if (ld.type.find? (·.isConstOf c)).isSome then return true
    return false

open Lean Lean.Elab.Tactic in
/-- The cascade stages, in priority order. Each stage represents a *class
    of intuition* — a kind of reasoning the author would take for granted.
    Long-term, stage selection will be driven by the theorem graph / goal
    shape; for now stages are tried in fixed order. -/
private def obviousStages : TacticM (Array ObviousStage) := do
  let simpAll ← `(tactic| simp_all (config := { maxSteps := 2000 }) only [obvious])
  let unfoldParallel ← `(tactic| simp only [obvious.parallel] at *)
  let unfoldIntersects ← `(tactic| simp only [obvious.intersects] at *)
  -- The Guards stage pulls in the *main* `obvious` set alongside the
  -- topic-specific one — Guards-form goals typically need both the
  -- Guards/Splits unfold AND propositional normalizations like
  -- Segment Commutativity (`{A,B} ↔ {B,A}`) and Betweenness Commutativity.
  -- The `simp only` here is non-recursive so it converges.
  let unfoldGuards ← `(tactic| simp only [obvious, obvious.guards] at *)
  let memDef ← `(tactic|
    simp only [Segment.mem_def, Ray.mem_def, Extension.mem_def, LineThrough.mem_def])
  let memDefAt ← `(tactic|
    simp only [Segment.mem_def, Ray.mem_def, Extension.mem_def, LineThrough.mem_def] at *)
  let finsetExt ← `(tactic|
    (ext; simp only [Finset.mem_insert, Finset.mem_singleton, Finset.mem_erase, ne_eq]))
  let doneT ← `(tactic| done)
  let assumptionT ← `(tactic| assumption)
  let decideT ← `(tactic| decide)
  let tautoT ← `(tactic| tauto)
  let aesopT ← `(tactic| aesop)
  -- Cheap closers tried before tauto: done (simp_all already closed),
  -- assumption (hypothesis match), decide (decidable-instance reduction).
  -- Each is fast-to-fail when inapplicable, so paying them per-stage is cheap.
  let cheapThenTauto := #[
    ("done", doneT), ("assumption", assumptionT),
    ("decide", decideT), ("tauto", tautoT)
  ]
  -- `aesop` after the cheap-then-tauto run, for stages where the goal
  -- shape demands eq-orientation / disjunct-reordering that tauto can't
  -- do on its own. Strictly opt-in per stage — aesop is expensive.
  let cheapTautoAesop := cheapThenTauto.push ("aesop", aesopT)
  return #[
    { name := "simp_all",
      preamble := simpAll,
      closers := cheapThenTauto },
    -- Topic stages use runtime `Name` lookup (`.mkStr3` constructor)
    -- instead of `` `` `` literals: the `Parallel` / `Intersects` defs live
    -- in modules that transitively depend on this one, so a `name literal`
    -- would create a circular import. The names are stable identifiers
    -- — if a def is ever moved, update here.
    { name := "unfold Parallel",
      applies := goalMentions (.mkStr3 "Geometry" "Theory" "Parallel"),
      preamble := unfoldParallel,
      closers := cheapThenTauto },
    { name := "unfold Intersects",
      applies := goalMentions (.mkStr3 "Geometry" "Theory" "Intersects"),
      preamble := unfoldIntersects,
      closers := cheapThenTauto },
    -- `Splits := ¬Guards`, so either constant indicates the topic.
    { name := "unfold Guards",
      applies := fun g => do
        if (← goalMentions (.mkStr3 "Geometry" "Theory" "Guards") g) then return true
        goalMentions (.mkStr3 "Geometry" "Theory" "Splits") g,
      preamble := unfoldGuards,
      closers := cheapTautoAesop },
    { name := "mem_def goal",
      preamble := memDef,
      closers := cheapThenTauto },
    { name := "mem_def at*",
      preamble := memDefAt,
      closers := cheapThenTauto },
    { name := "Finset ext",
      preamble := finsetExt,
      closers := cheapThenTauto }
  ]

open Lean Lean.Elab.Tactic in
elab "obvious" : tactic => do
  try evalTactic (← `(tactic| intros)) catch _ => pure ()
  try evalTactic (← `(tactic| normalize_eq)) catch _ => pure ()
  let stages ← obviousStages
  let original ← saveState
  let mut stageReports : Array (String × Bool × Nat × Array (String × Nat)) := #[]
  for stage in stages do
    original.restore
    -- Goal-shape gate: skip stages whose `applies` predicate rejects
    -- the current main goal. Default `applies` is always-true; topic
    -- stages override to check for distinctive constants in scope.
    let g ← getMainGoal
    if !(← stage.applies g) then
      if ← isTracingEnabledFor `obvious then
        addTrace `obvious m!"  {stage.name}: skipped (goal shape)"
      continue
    let (preOk, preMs) ← tryTimed stage.preamble
    -- Strict: if preamble fails, skip closers. Matches v1 semantics where
    -- `simp_all only [obvious]; tauto` only runs tauto if simp_all
    -- succeeds. Permissive (run closers anyway) blew up tauto search on
    -- goals where simp_all was the gatekeeping cheap check.
    if !preOk then
      stageReports := stageReports.push (stage.name, false, preMs, #[])
      continue
    let postPreamble ← saveState
    let mut closerReports : Array (String × Nat) := #[]
    let mut closed := false
    for (cName, cTac) in stage.closers do
      postPreamble.restore
      let (ok, cMs) ← tryTimed cTac
      if ok then
        if ← isTracingEnabledFor `obvious then
          addTrace `obvious
            m!"closed by {stage.name} → {cName} (preamble {preMs}ms, closer {cMs}ms)"
        closed := true
        break
      closerReports := closerReports.push (cName, cMs)
    if closed then return
    stageReports := stageReports.push (stage.name, true, preMs, closerReports)
  original.restore
  if ← isTracingEnabledFor `obvious then
    let rows := stageReports.toList.map fun (n, ok, preMs, closers) =>
      let preTag := if ok then m!"preamble {preMs}ms" else m!"preamble FAILED {preMs}ms"
      let cRows := closers.toList.map (fun (cn, cms) => m!"\n      {cn}: {cms}ms")
      m!"  {n}: {preTag}{MessageData.joinSep cRows m!""}"
    addTrace `obvious
      m!"all alternatives failed:\n{MessageData.joinSep rows m!"\n"}"
  throwError "obvious: no alternative closed the goal"

/-- Term-position form: `(obvious : T)` desugars to `(by obvious : T)`. -/
macro "obvious" : term => `(by obvious)

/-! ## Examples -/

section Examples
example (A B : Point) : A on segment A B := by obvious
example (A B : Point) : B on segment A B := by obvious
example (A B : Point) : A on segment A B := obvious
end Examples

end Geometry.Theory
