Hey Shae,

We briefly chatted on Mastodon about my excitement around Lean tactic metaprogramming, and you mentioned it would make a good blogpost, and I wanted to agree; but I kind of hate blogging. I've been doing this "LOG.md" thing for a bit; and I like that, but it doesn't _feel_ right for an explanatory blog; I use it more as a journal or engineering log or scratchpad. I've been trying to embrace my hyperlexia, and this is a good way to do it, but is does feel a little weird to write a blog-ish explainer/experience report in it.

I also just don't like the sort of anonymous audience of a blogpost; I know someone _might_ read it, but it feels itchy to write something someone only _might_ read. I spend a lot of time thinking about writing and writing about thinking and I _care_ about it a lot, I think my identity is in it a bit; so it feels bad if I don't know _someone_ will read it. With LOG.md, I know _I'll_ read it, so I don't mind writing, a blogpost, though? All those hits could be bots and crawlers; the comments LLM; just feels lousy to not _know_ someone has really read it, feels like I wasted my time.

But, as sometimes happens when my anxiety spikes about stuff, I had an idea. I may not be able to guarentee that an anonymous audience is nonempty, as a blogpost would require, but an open letter? I can guarantee at least _one_ person reads it, the recipient[1].

A long time ago in #haskell-cafe I posted my then-current phone number in hex because I, beind a college freshman, hadn't yet learned that obfuscation is not the same as encryption. You called my cell, I answered and was confused, then I realized the lesson. I remember chatting a bunch in those salad days on IRC, and I have the sense that you would appreciate this approach to blogging; I hope you don't mind being my test subject.

Anyway, the meat of the letter, tactic programming in Lean4.

-- Geometry

I've been working on this thing (`geometry_is_your_friend`) as a little project to learn Lean. It's formalizing Martin Greenberg's _Euclidean and Noneuclidean Geometry_. In geometry, one frequently deals with small collections of objects with simple (often pairwise) relations, `distinct` and `collinear` are the two big ones, and the former is especially annoying when you have more than a few distinct points; The number of hypotheses in a list of distinct points is `O(n^2)`, so it rapidly becomes very messy in a proof to bookkeep all those hypotheses, and proving a `distinct` goal is a _real_ bear. Lean offers good facilities for creating custom syntax, and so it was quite easy to create a custom proof term:

```lean
distinct A B C D ... := A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ A ≠ ... ∧ B ≠ C ∧ B ≠ ... ∧ C ≠ ... ∧ ...
```

which I can use like:

```lean
example (A B C D : Point) (h : distinct A B C D) : A ≠ B ∧ B ≠ C ∧ A ≠ D := by
  distinguish
```

That example also shows the tactic counterpart, `distinguish`; which tries to automatically close goals based on the `distinct` hypotheses it can find in the proofstate. The initial version was just the `distinct` term, and it barely worked, resulting in a lot of proofs like this one:

```lean
/-- p146. Given A-B-C and A-C-D:
  (a) Prove that A,B,C, and D are four distinct points (the proof requires an axiom)
-/
theorem Ex1.a : A - B - C ∧ A - C - D -> distinct A B C D := by
  intro ⟨ABC, ACD⟩
  have distinctABC := Betweenness.abc_imp_distinct ABC
  have distinctACD := Betweenness.abc_imp_distinct ACD
  simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self, and_true]
  have AneB : A ≠ B := by distinguish distinctABC A B
  have AneC : A ≠ C := by distinguish distinctABC A C
  have BneC : B ≠ C := by distinguish distinctABC B C
  have AneD : A ≠ D := by distinguish distinctACD A D
  have CneD : C ≠ D := by distinguish distinctACD C D
  refine ⟨⟨AneB, AneC, AneD⟩, ⟨BneC, ?_⟩, CneD⟩
  -- have BneD : B ≠ D := by distinguish distinctACD B D
  by_contra! BeqD
  rw [<- BeqD] at ACD
  exact Betweenness.absurdity_abc_acb ⟨ABC, ACD⟩
```

This uses an earlier version of `distinguish` which just automates a single proof of a single inequality fact; and that only after 

```lean
simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self, and_true]
```

has cluttered my proof. This is ugly, and so I dug into the guts of the tactic mode to figure it out. Eventually, I got it working, basically; it took a whole bunch of cajoling and I only understand like, 20% of it; but it works. I went through the _Lean Tactic Programming Guide_ and cannot speak highly enough of it as a significantly better introduction to the topic then this will be. The Lean tactic system is _really_ neat; and also a _mindfuck_ to understand. It's very easy to confuse yourself in terms of what level you're thinking at; and I spent a fair few hours confused because I hadn't realized I needed to convert from the `LocalDecl` to an actual `Expr` in order to reference a hypothesis inside the inequality proof.

Sorry, let me back up and give you an unauthorized nickel tour of the Lean proofstate. Again, read LTPG, it'll take an evening; put on some Punch Brothers and read it, it's what I did and I came out with enough unearned hubris to actually give it a shot, and it's worked pretty well.

-- Proofstate

A proof, as you know, is a program; and in particular it is a program of both values and types. Values have Types, and Types, in Lean, can depend on Values. This allows for essentially arbitrary formal mathematical statements after I'm sure quite a bit of underlying magic done by wizards with beards longer than mine. You can encode a statement using relatively natural mathematical syntax without having to resort to LaTeX by using some clever editor features and a bit of muscle memory which develops pretty quickly. So something like: 

```lean
example : distinct A B C D E -> A ≠ X -> A ≠ B ∧ (B ≠ C ∧ X ≠ A) ∧ (∀ P : Nat, P = 3 -> P > 1) ∧ (C ≠ D ∨ V = W) := by
```

gets entered like

```lean
example : distinct A B C D E -> A \ne X -> A \ne B \and (B \ne C \and X \ne A) \and (\forall P : Nat, P = 3 -> P > 1) \and (C \ne D \or V = W) := by 
```

and your preferred editor will do the right thing, assuming your plugins are in order.

This statement gets translated to a 'proofstate' like the following:

```lean
A B C D E X : α✝¹
V W : α✝
h : Distinct [A, B, C, D, E]
AneX : A ≠ X
⊢ A ≠ B ∧ (B ≠ C ∧ X ≠ A) ∧ (∀ (P : ℕ), P = 3 → P > 1) ∧ (C ≠ D ∨ V = W)
```

This is split into two parts, the `Context`, which contains all the facts you know, and the `Goal`, which comes after the `⊢` and is the term you have to construct out of your pieces, you can have multiple simultaneous goals; which just means you have multiple branches of a conjunction to prove. All this is the 'proofstate' of your theorem. When proving, you can either directly construct terms using the underlying dependently typed functional language, like in this part of a proof of prop 2.2:

```lean
-- This lemma was not suggested by the author, but is handy. The proof is not long and simply establishes the
-- 'Parallel' fact for each pair of lines. We need the unique point and the negative condition to build
-- these
have hABnotparBC : (AB ∦ BC) := Line.intersecting_lines_are_not_parallel hPonAB hPonBC
have hABnotparAC : (AB ∦ AC) := Line.intersecting_lines_are_not_parallel hPonAB hPonAC
have hBCnotparAC : (BC ∦ AC) := Line.intersecting_lines_are_not_parallel hPonBC hPonAC
```

where I construct a proof that a bunch of lines are not parallel to one another by directly invoking the function provided by the `Line.intersecting_lines_are_not_parallel` lemma.

> Aside: You can also see some custom syntax there for 'not parallel', this is very simple to achieve using the simplest notation-related tool in Lean, `notation`
>
> ```lean
> notation:20 L " ∥ " M => Parallel L M
> notation:20 L " ∦ " M => ¬(Parallel L M)
> ```

You can also use `tactic` mode to prove theorems, and this is what I wanted to do for the `distinct` term.

-- What distinct should do

In particular, I need three things:

1. notation for small collections of pairwise distinct values of some type; I suspect it'll almost always be points, but it could be useful for lines at some point too.
2. a way to automatically prove inequality goals using available hypotheses in the context
3. a way to destructure a distinct goal into a right-associated ("flat") conjunction of inequality goals

This would allow me to work with the `distinct` condition as a goal, known fact, and tool to prove these simple cases automatically by automatically looking at the lists of known-distinct items and trying to prove the goal without cluttering the proofstate (which is important for performance reasons).

-- How it works

Here's the lede I've kept buried, the proofstate is just a Monad, it's essentially a little virtual machine that tracks the hypotheses in the `LocalContext` as a bunch of `LocalDecls`, which can be easily turned into `Expr`s, which is the type of Lean Statements in the AST after elaboration; the Lean parser is a multilayer system, and `Expr` is the last step before running actual code[2]. This machine is exposed via the `TacticM` monad, which is essentially a DSL for manipulating proofstates. Proofstates themselves are just a collection of variables that get wired together; they come in three flavors of interest:

- FVars - Free variables, these are the `A B C D E X V W` above, but also `h` is an FVar, I prefer to think of it as 'FactVariable', which I think is mostly okay.
- BVars - Bound variables, these are the arguments to functions, so the `P` in the `(∀ (P : ℕ), P = 3 → P > 1)` above is a BVar
- MVars - Meta variables, or holes, these are associated with the current goal(s); each must get assigned a term of a matching type to be closed. This is needs to be proved.

The `TacticM` monad exposes a simple programming language to interact with these variables, and the `Qq` library and `Lean` namespace provide the API to manipulate it. I started[3] with the following to cover #1 above:

```lean
structure Distinct {α : Type*} (points : List α) : Prop where
  pairwise : List.Pairwise (· ≠ ·) points

namespace Distinct

-- ... snip ...

-- Custom syntax for distinct/distinguish
declare_syntax_cat distinct_binder
syntax ident+ " : " term : distinct_binder

syntax "distinct" ident+ : term
macro_rules
  | `(distinct $xs*) => `(Distinct [$xs,*])

end Distinct
```

this gets me to `distinct A B C D E` as a proof term, I can also write `Distinct [A,B,C,D,E]` but that's much more cumbersome. The syntax category is probably not necessary, but it feels nice to give everything it's own little home. Next I added a couple example statements to test with:

```lean

example : distinct A B C D E -> A ≠ X -> A ≠ B ∧ B ≠ C ∧ X ≠ A ∧ (∀ P : Nat, P = 2 -> P > 1) ∧ C ≠ D := by
  intro h AneX
  distinguish
  -- this part doesn't matter, the assertions are just to make sure the distiguish step doesn't oversolve
  exact AneX.symm
  intro P Peq2
  rw [Peq2]; trivial

example : distinct A B C D E -> A ≠ X -> A ≠ B ∧ (B ≠ C ∧ X ≠ A) ∧ (∀ P : Nat, P = 3 -> P > 1) ∧ (C ≠ D ∨ V = W) := by
  intro h AneX
  distinguish
  · exact AneX.symm
  · intro P Peq3; rw [Peq3]; trivial
  · have CneD : C ≠ D := by distinguish
    left; trivial

example (A B C D : Point) (h : distinct A B C D) : A ≠ B ∧ B ≠ C ∧ A ≠ D := by
  distinguish

example (h : distinct A B) : A ≠ B := by distinguish

```

This covers a few cases, the plan was to write a tactic that worked roughly like this:

1. Flatten and split the goal tree so that every part of the conjunction was it's own goal.
2. Make a list of all the goals that are just an inequality statement
3. Find all the hypotheses that are created by `distinct`
4. Use the hypotheses from #3 to try to prove every marked goal from #2
5. Leave the rest

It is certainly possible to do this in other ways, or to extend the traversal through disjunctions or quantifiers, but the 80% case is 'flatten things and prove a bunch of single inequalities' so I started there. The first step is splitting the goals, this went through a couple iterations, but landed at:

```lean
/-- Split conjunction goal into MVars and track which are inequalities -/
partial def splitAndTagGoals : TacticM (List MVarId × List Nat) := do
  let goal ← getMainGoal

  let rec splitAndExtract (g : MVarId) (idx : Nat) : TacticM (List MVarId × List (Nat × Bool)) := do
    let goalType ← g.getType
    have goalTypeProp : Q(Prop) := goalType

    match goalTypeProp with
    | ~q($a ∧ $b) => do
      -- Split conjunction
      setGoals [g]
      evalTactic (← `(tactic| constructor))
      let [leftGoal, rightGoal] ← getGoals | throwError "Expected two goals after constructor"

      -- Recursively process both sides
      let (leftMvars, leftTags) ← splitAndExtract leftGoal idx
      let rightIdx := idx + leftMvars.length
      let (rightMvars, rightTags) ← splitAndExtract rightGoal rightIdx

      return (leftMvars ++ rightMvars, leftTags ++ rightTags)

    | ~q(@Ne _ $a $b) =>
      -- Inequality - mark as such
      return ([g], [(idx, true)])

    | _ =>
      -- Other goal - not an inequality
      return ([g], [(idx, false)])

  let (mvars, tags) ← splitAndExtract goal 0
  let ineqIndices := tags.filterMap (fun (idx, isIneq) => if isIneq then some idx else none)

  return (mvars, ineqIndices)
```

There is a great deal of bookkeeping in this, but it's a pretty simple idea -- grab the goal (`getMainGoal`), then try to break it into its components using the `splitAndExtract` helper; it does this by simple pattern matching on the goal -- if it's a conjunction (`q($a ∧ $b)`, which is a quotation of the literal `A ∧ B` with match placeholder for the left and right sides of the conjunction), then recurse down each side, updating the index of the goal, if it's an inequality (`~q(@Ne _ $a $b)`), mark it as such, and otherwise mark it as a non-equality.

The other part of this function generates (via the `constructor` tactic in the first branch of the match) an `MVar` for each new goal; so the result is a list of `MVarId`s, one for each goal; and a second list which indexes the first to tell us where all the inequality goals are (`ineqIndices`).

Now we've successfully decomposed the goal from a single conjunction tree (that is, it's in some freely associated form, not uniformly right-associated) to a 'flat' (right-associatated) list of goals and an index of where the ones we can prove with distinct are.

One bit that took me a little while to wrap my head around, when you get the goal, it is an `MVarId`, but we need to deal with it's type as a syntactic element that represents a fixed proposition. A goal, ultimately, is just a slot that expects a construction assigned to it of the appropriate type; it doesn't carry any information directly with it, so in order to talk about it's type, we have to look it up with `goal.getType`, this gives us an `Expr`, which seems like what we need, because `Expr` is the representation of the syntax, but in fact we need to go one step further and work with the `Q`-quoted version of this `Expr`, which allows us to pick it apart without worrying about the constraints of the `Expr` type.

From the LTPG:

> -- The data structure that is used to represent Lean expressions is `Lean.Expr`.
> -- Due to the nature of dependent type theory, `Lean.Expr` is used to encode types, terms and proofs.
> -- Thus, `Lean.Expr` is also what is checked by the Lean kernel when checking proofs.
> -- ctrl-click on `Lean.Expr` below to see its definition in the library.
> #check Lean.Expr
> 
> -- Lean has a handy library `Qq` to help you build `Lean.Expr` terms with a convenient notation.
> open Qq
> 
> -- `Q(...)` is a type annotation of an expression, and
> -- `q(...)` is an expression

This took me a bit to grok, and I'm not sure it feels natural yet, but then again quotes and quasiquotes don't seem like the sort of thing you're ever supposed to feel comfortable with, so I suppose it's feeling the way it's supposed to. Another thing this function doesn't do is try to disambiguate situations which are not simple conjunctions; consider a proposition like:

```lean
distinct A B C D -> A ≠ B ∧ (C ≠ D ∨ V = W) 
```

In this example, it is easy to resolve, we know `A ≠ B := by distinguish` and `C ≠ D := by distinguish`, but the `splitAndTagGoals` above will treat the `(C ≠ D ∨ V = W)` disjunction as unassailable. Similarly a condition like:

```lean
distinct A B -> ∀ P : Prop, A ≠ B ∨ P
```

is obviously true regardless of the choice of `P`, but the current tool won't look inside the quantifier to reduce that to a proof of `∀ P : Prop, True`, even though it can conclude `A ≠ B` easily.

Limitations noted, now I have the broken up goal. Next, I need to gather up the tools I'll need; I don't want to try to use every availble fact-in-evidence, just the `distinct` properties that I know about; this is not the _best_ way to do things, as there might be ambient facts that could be used to prove the property, but hunting for them involves doing a lot more mangling of the proofstate, and things were already complicated enough. Here's the function:

```lean
/-- Finds all `Distinct` hypotheses in the local context -/
def findDistinctHypos : TacticM (List LocalDecl) := do
  let lctx ← getLCtx
  let mut distinctHypos : List LocalDecl := []
  for decl in lctx do
    if decl.isImplementationDetail then continue
    let declType ← instantiateMVars decl.type
    if declType.isAppOfArity ``Distinct 2 then
      distinctHypos := decl :: distinctHypos
  return distinctHypos
```

This produces a list of `LocalDecl`s that match the signature of the distinct structure. The `declType.isAppofArity` line is what does that, it's looking for a literal `Distinct` of arity 2; which I don't think is the _best_ way to find these things, but it is _a_ way and the first one that worked; I suspect there are better tools for this (probably pattern matching on the type), but for a simple structure like `Distinct`, it's easy enough to just search for it. It's of arity 2 because it has two parameters, the list of points (it's second parameter) is an explicit parameter, but the type of the values in that list is not constrained to _only_ points, and so there is an implicit type parameter.

Lean is pretty aggressive about making parts of the language implicit, this is a big step in making the language more ergonomic than other languages I've tried. Ergonomics rarely is the only reason I stop using a prover, but it's frequently the thing that makes it impossible to get over whatever other struggles I have. Lean does a very good job here of making it possible -- even easy -- to let context fill in details you don't want to care about but need to care about, probably my favorite part of the language.

The code itself is simple; it walks over each fact in the `LocalContext` and builds up a list; the `let mut` is a little bit of a lie, as I understand, it's hiding a `State`-monad-adjacent thing that lets you pretend the variable is mutable even in this pure-ish environment. This makes it pretty pleasant to write these little programs that query the proof-state; it's not too far away from a regular imperative language about as weildy as shell; not powerful, but powerful enough.

Once it finds a declaration of the correct type, it adds it to a list of hypotheses that we use in the following monster[4]

```lean
def runDistinct : TacticM Unit := withMainContext do
    let (allGoals, ineqIndices) ← splitAndTagGoals
    let distinctHypos ← findDistinctHypos
    let mut solvedIndices : List Nat := []

    for idx in ineqIndices do
      let goalMVar := allGoals[idx]!
      setGoals [goalMVar]

      for hypo in distinctHypos do
        -- 1. break into the fvars on either side
        let goalType ← goalMVar.getType
        have goalTypeProp : Q(Prop) := goalType
        if let ~q(@Ne $typ $lhs $rhs) := goalTypeProp then
          -- 2a. if the fvars are the same, then the two things are equal, reject
          if lhs.fvarId! != rhs.fvarId! then
            -- 3. now search the `points` of the `distinct` condition and we can conclude inequality based
            -- on the pairwise relationship
            if let some points ← Distinct.getPointsExpr hypo.toExpr then
              -- establish that both lhs and rhs are in the list of distinct variables
              let lhsIn := points.any (fun p => p.isFVar && p.fvarId! == lhs.fvarId!)
              let rhsIn := points.any (fun p => p.isFVar && p.fvarId! == rhs.fvarId!)
              if lhsIn && rhsIn then
                -- we can prove it, we have the technology
                let proofGoal ← mkFreshExprMVar goalType
                let proofMVar := proofGoal.mvarId!
                setGoals [proofMVar]
                let hypoName := mkIdent hypo.userName

                -- prove using aesop + simp, this is not ideal, it should be possible to construct a direct
                -- proof, but it's not low-effort, so FIXME some other time.
                evalTactic (← `(tactic| (
                  have h := ($hypoName).pairwise
                  simp only [List.Pairwise, List.mem_cons] at h
                  aesop
                )))

                -- Check if it was solved, then assign the goal if it is.
                if ← proofMVar.isAssigned then
                  let proof ← instantiateMVars proofGoal
                  goalMVar.assign proof
          else
            -- in this case, lhs is _literally the same variable reference_ as rhs, so we are trying to prove
            -- ¬(rfl A), which is just false, so the whole conjunction is false and we should replace the goal
            -- with false. I'm not doing that now, but it's doable, I think.
            throwError "lhs is identical to rhs, you're trying to prove A ≠ A, and that's no bueno"
        else
          logInfo m!"{goalType}"
          -- 2b. do nothing, this case is not possible because we're only inspecting inequalities.
          throwError "not possible"
      -- bookkeeping to make sure we set the goals correctly later.
      -- FIXME: I think this could probably be based on whether or not the mvar is assigned?
      if ← goalMVar.isAssigned then
        solvedIndices := idx :: solvedIndices

    -- Collect unsolved goals
    let mut unsolvedGoals : List MVarId := []
    for i in [:allGoals.length] do
      if !solvedIndices.contains i then
        unsolvedGoals := unsolvedGoals ++ [allGoals[i]!]

    setGoals unsolvedGoals
```

This integrates everything together along with a couple other helpers; but the strategy is really simple and mostly contained in the `-- 2a` branch, and within that, the main branch is the one that actually does the work. After the initial preamble which splits the goal, gathers the facts, and allocates a list for all the goals we automatically solve; I iterate over each inequality and try to close it with one of the available `distinct` hypotheses I gathered. I do this by first checking that the two sides are not 'literally' the same, that is, they are different `fVars`. Recall that an `fVar` represents a 'fact' variable, and in my case they'll usually represent named points, so right now I want to fail if any of the facts we're trying to prove is a simple falsehood of `A ≠ A`, as something like `simp` will already cover that case. Once we're in the branch, the process is simple -- if the respective `fVars` for the left and right sides of the inequality are present in the same list of distinct variables, we know there is a proof they are not equal, so I construct it using `simp` and `aesop`; two existing automated tactics that can resolve most simply proofs. The `simp` reduces the `distinct` goal to the relevant inequalities, and `aesop` is able to use that to close. I could, and probably should, directly construct the proof here; but doing so is a little messy and this works alright for most cases. Since the number of variables is relatively small, it's unlikely this will become a huge performance issue except in extreme cases.

> Aside: It's _really_ interesting how performance of the prover becomes a concern for the math side of things. Earlier, while working more directly on the geometry, I was
> pretty liberal using the `tauto` tactic; which more or less brute-forces it's way through a proof by trying to apply `simp`, `contradiction`, and any available hypothesis
> to the goal to try to resolve it. In small contexts with few active hypotheses, it's quick enough; but on one proof where I had two dozen or so active facts, it ground the 
> machine to a halt and my file would take tens of seconds to evaluate. Real nasty.
>
> The cool thing, though, is that good _programming_ practices seem to translate naturally to good _mathematical_ practices. Spending time refactoring really does translate 
> to better quality arguments that feel more elegant. I've long associated refactoring with the feeling of a good proof technique or clever mathematical argument, it's very
> validating to see it play out in code.


Once I've attempted the proof, I check to see if I actually managed to assign the variable (it always should, another benefit to a direct construction would be eliminating this branch), and then assign the goal to the MVar associated with the proof; closing the goal.

After that is just book keeping, marking the goals we solved and updating the proof state. Lean doesn't do that on it's own, so all of this bookkeeping has been to accomplish this step, the actual tactic is very simple, but updating the state is tricky.

-- Syntax and tooling

All of this gets us through the _code_ part of this, but there is a whole second step. At the beginning, I showed a bit of the `notation` created for `distinct`, in fact, there are three items of syntax I need; I have the tools, but they are not yet integrated, I could run a proof like:

```lean
example (A B C D : Point) (h : distinct A B C D) : A ≠ B ∧ B ≠ C ∧ A ≠ D := by
  run_tac runDistinct
```
but this is ugly, I prefer the `distinguish` keyword I set before. In fact, I need to be able to use this syntax in three contexts:

1. As a hypothesis in a theorem statement, e.g. `distinct A B C -> ...`
2. As a conclusion of a theorem statement, e.g., `... -> distinct A B C := by ...`
3. As a tool for intermediate proof steps, e.g., `have h := by distinguish`, or `separate at distinctABC` (where `distinctABC : distinct A B C`), or even `separate` to separate a goal of `distinct A B C ...` into a conjunction of inequalities. 

To do this, we must dive into the darkest magic of this whole thing, the `syntax` and `elab` APIs. The first two items are easy, they just construct the `Distinct` structure while eliding the need for brackets and commas (in the case of `distinct`, which I showed at the beginning):


```lean
-- Custom syntax for distinct/distinguish
declare_syntax_cat distinct_binder
syntax ident+ " : " term : distinct_binder

syntax "distinct" ident+ : term
macro_rules
  | `(distinct $xs*) => `(Distinct [$xs,*])
```

The `distinguish` tactic just runs the `runDistinct` function

```lean
syntax "distinguish" : tactic

macro_rules
  | `(tactic| distinguish) => `(tactic| run_tac runDistinct)
```

But the last item, `separate`, which deals with destructuring a `distinct` goal or fact into its constituent inequalities is... well it's a lot.

This is definitely the most hobbled-together, hasty and unkempt part of this whole thing, so strap in:

```lean
/-- Extract points from a List Expr at the meta level -/
partial def extractPoints (e : Expr) : List Expr :=
  if e.isAppOfArity ``List.cons 3 then
    let head := e.appFn!.appArg!
    let tail := e.appArg!
    head :: extractPoints tail
  else
    []

syntax "separate" (" at " ident)? : tactic
```

This quick helper just gets the list of Exprs inside a list, those exprs need to get pairwise connected into a conjunction of inequality statements. I also declare the syntax to accept `separate` and `separate at h`, where `h` is some fact in the context. Then I use the `elab_rules` to create a macro expansion. `elab_rules` is similar to `macro_rules`, but is much more powerful, quoting the [_Lean Metaprogramming Guide_](https://leanprover-community.github.io/lean4-metaprogramming-book/main/02_overview.html#assigning-meaning-macro-vs-elaboration)

> In principle, you can do with a macro (almost?) anything you can do with the elab function. Just write what you would have in the body of your elab as a syntax within macro. However, the rule of thumb here is to only use macros when the conversion is simple and truly feels elementary to the point of aliasing. As Henrik Böving puts it: "as soon as types or control flow is involved a macro is probably not reasonable anymore".

`separate` has types and control flow, so we're above a macro; and the only thing above a macro is elab. The rules break into two parts, the `at h` side is handled first, goal side (which is simpler) is second. The main difference is the first branch needs to name individual hypotheses it's adding to the local context, while the second just needs to introduce new goals. I suspect there is more refactoring here, but I'll explain it as it is; take a look at the whole thing:

```lean
elab_rules : tactic
  | `(tactic| separate $[at $h]?) => do
  match h with
    | some hId => do
      withMainContext do
        let hExpr ← elabTerm hId none
        let hType ← instantiateMVars (← inferType hExpr)
        let hType ← whnf hType
        if !hType.isAppOfArity ``Distinct 2 then
          throwError "separate: {hId} is not a `Distinct` hypothesis"
        let some points ← Distinct.getPointsExpr hExpr
          | throwError "separate: could not extract points from {hId}"

        for i in [:points.length] do
          for j in [i+1:points.length] do
            let pi := points[i]!
            let pj := points[j]!
            let ineqType ← mkAppM ``Ne #[pi, pj]
            let ineqStx ← PrettyPrinter.delab ineqType
            -- Build a name like `AneB` from the fvar usernames
            let iName := (← FVarId.getUserName pi.fvarId!).toString
            let jName := (← FVarId.getUserName pj.fvarId!).toString
            let hypName := mkIdent (Name.mkSimple (iName ++ "ne" ++ jName))
            evalTactic (← `(tactic|
              have $hypName : $ineqStx := by
                have hp := ($hId).pairwise
                simp only [List.pairwise_cons, List.mem_cons, List.mem_singleton,
                           List.not_mem_nil, List.Pairwise.nil] at hp
                aesop))

    | none => do
      withMainContext do
        let goal ← getMainGoal
        let goalType ← instantiateMVars (← goal.getType)
        let goalType ← whnf goalType
        if !goalType.isAppOfArity ``Distinct 2 then
          throwError "separate: goal is not of the form `Distinct [...]`"

        let listExpr := goalType.getArg! 1
        let points := extractPoints listExpr

        evalTactic (← `(tactic| apply Distinct.mk))

        for _ in [:points.length] do
          try evalTactic (← `(tactic| rw [List.pairwise_cons]))
          catch _ => pure ()

        evalTactic (← `(tactic| simp only [List.mem_cons, List.mem_singleton, List.Pairwise.nil,
                                            List.not_mem_nil, forall_eq_or_imp, forall_eq,
                                            forall_const, IsEmpty.forall_iff, forall_true_iff,
                                            and_true, true_and, and_assoc] at *))
        try evalTactic (← `(tactic| exact List.Pairwise.nil))
        catch _ => pure ()
```

then let's just look at the second half, as it's easy to explain:

```lean
      withMainContext do
        let goal ← getMainGoal
        let goalType ← instantiateMVars (← goal.getType)
        let goalType ← whnf goalType
        if !goalType.isAppOfArity ``Distinct 2 then
          throwError "separate: goal is not of the form `Distinct [...]`"

        let listExpr := goalType.getArg! 1
        let points := extractPoints listExpr

        evalTactic (← `(tactic| apply Distinct.mk))

        for _ in [:points.length] do
          try evalTactic (← `(tactic| rw [List.pairwise_cons]))
          catch _ => pure ()

        evalTactic (← `(tactic| simp only [List.mem_cons, List.mem_singleton, List.Pairwise.nil,
                                            List.not_mem_nil, forall_eq_or_imp, forall_eq,
                                            forall_const, IsEmpty.forall_iff, forall_true_iff,
                                            and_true, true_and, and_assoc] at *))
        try evalTactic (← `(tactic| exact List.Pairwise.nil))
        catch _ => pure ()
```

This is similar to the `runDistinct` function -- I grab the context, and look at the goal. I'm going to 'prove' this goal by reducing it from a 'prove this conjunction' to
'the conjunction is proved only if it's constituents are proved'. So I instantiate the MVar and inspect it's type, apply a `whnf` to ensure it's in a normal form, and then verify
it is indeed a `distinct` goal with the same arity method as `runDistinct`.

Next, I grab the list of points via the `extractPoints` helper, and walk over each one, rewriting with

```lean
@[simp] theorem pairwise_cons : Pairwise R (a::l) ↔ (∀ a', a' ∈ l → R a a') ∧ Pairwise R l :=
```

which says, "If an item is in a `List.Pairwise R`, then it has the relationship `R` with all other items in the pairwise relationship following it's position in the list" 

If this fails for any reason, the point is skipped and we won't be able to prove everything, but that case is actually impossible; because we know the list is only items in a pairwise relationship anyway. After that, there is a big `simp` line which does all the necessary rewriting to flatten the list of conjunctions and eliminate the tail cases where a `∧ True` gets injected to cover the final case. The last `try evalTactic` covers a case where there aren't enough elements in the distinct set, and in this case if the tactic fails we don't care, it's a convenience to not have loose, trivial goals floating around.

All that, ultimately, allows for this to work:

```lean
example : A ≠ B ∧ A ≠ C ∧ B ≠ C -> distinct A B C := by
  intro ⟨AneB, AneC, BneC⟩
  separate
  exact ⟨AneB, AneC, BneC⟩

example : D ≠ A ∧ D ≠ B ∧ D ≠ C -> distinct A B C -> distinct A B C D := by
  intro ⟨DneA, DneB, DneC⟩ distinctABC
  separate
  distinguish
  repeat tauto -- tauto covers the .symm

example : D ≠ A ∧ D ≠ B ∧ D ≠ C -> distinct A B C -> distinct A B C D := by
  intro ⟨DneA, DneB, DneC⟩ distinctABC
  separate at distinctABC
  separate
  repeat tauto -- tauto covers the .symm
```

-- Effect on the initial exercise

This was the original:

```lean
/-- p146. Given A-B-C and A-C-D:
  (a) Prove that A,B,C, and D are four distinct points (the proof requires an axiom)
-/
theorem Ex1.a : A - B - C ∧ A - C - D -> distinct A B C D := by
  intro ⟨ABC, ACD⟩
  have distinctABC := Betweenness.abc_imp_distinct ABC
  have distinctACD := Betweenness.abc_imp_distinct ACD
  simp only [ne_eq, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, IsEmpty.forall_iff, implies_true, List.Pairwise.nil, and_self, and_true]
  have AneB : A ≠ B := by distinguish distinctABC A B
  have AneC : A ≠ C := by distinguish distinctABC A C
  have BneC : B ≠ C := by distinguish distinctABC B C
  have AneD : A ≠ D := by distinguish distinctACD A D
  have CneD : C ≠ D := by distinguish distinctACD C D
  refine ⟨⟨AneB, AneC, AneD⟩, ⟨BneC, ?_⟩, CneD⟩
  -- have BneD : B ≠ D := by distinguish distinctACD B D
  by_contra! BeqD
  rw [<- BeqD] at ACD
  exact Betweenness.absurdity_abc_acb ⟨ABC, ACD⟩
```

To be honest, this isn't too bad, but it is a little bad; the `simp` line is ugly, the `have`s are a little unsightly, and I have to hand-hold the old tactic a lot to get it to work. This *should* be simple to conclude, and that's what `distinguish` is for, here it is after all that work:

```lean
/-- p146. Given A-B-C and A-C-D:
  (a) Prove that A,B,C, and D are four distinct points (the proof requires an axiom)
-/
theorem Ex1.a : A - B - C ∧ A - C - D -> distinct A B C D := by
  intro ⟨ABC, ACD⟩
  have distinctABC := Betweenness.abc_imp_distinct ABC
  have distinctACD := Betweenness.abc_imp_distinct ACD
  -- The majority of cases are handled by the custom tactics
  separate; distinguish
  -- The remaining case is to disprove BeqD under the betweenness hypotheses
  by_contra! BeqD
  rw [<- BeqD] at ACD
  exact Betweenness.absurdity_abc_acb ⟨ABC, ACD⟩
```

_Much_ nicer. I can grab a couple distinctness hypotheses using existing theorems about Betweenness of points. I then `separate` the main goal into a list of inequalities like:

```lean
A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D
```

most of which are dispatched by the `distinguish` command immediately following it. The only remaining case is that `B` and `D` are distinct, which is easy to prove by contradiction and a known absurdity.

-- What's left

There are a lot of improvements to make, I think; my use of the `elab` facilities are pretty naive, and I think a lot could be cleaned up if I had a better understanding of the API, but no progress without practice, and this really simplifies a lot of annoying bookkeeping. The fact that the syntax is so directly adjustable and easy to extend and tweak is really satisfying. I spent a lot of time writing Ruby, and the reason I liked it was really down to how easy it was to get the interpreter to read the way I wanted. Lean is that but with even more flexibility and a really powerful API for both extending the language and also manipulating the proof state. Since the language is so focused on the proof state anyway, being able to automate the interactions really feels like a superpower. Truly cool stuff.

I have some plans to add lemmas around how to extend the `distinct` condition, 'adding' a point to the condition requires a proof that the new item is distinct from all other items, which is a goal-state that should be automatable to create, but would certainly be a pain to do by hand. Removing items from a `distinct` condition is comparatively easy (it requires no real 'proof'), but proving a general theorem that doesn't regard the length of the list is a little tricky.

I also have another condition, `collinear`, that needs similar syntactic treatment, and probably some custom tactics as well.

There is also, of course, extending `distinguish` and `separate` to look past disjunctions and quantifiers to try to resolve goals.

One thing I didn't mention was the `delaborator`. I didn't talk about it mostly because I barely understand it, but it's similar to a prettyprinter, it helps display facts and goals in a 'nice' way. Right now the facts look like `Distinct [A, B, C]`, not `distinct A B C`, which is not _too_ confusing, but originally they looked like `distinctABC : List.Pairwise (· ≠ ·) [A, B, C]` which _was_ pretty weird, the delaborator is the thing that fixes that, I think; I haven't really dug in.

It'd also be nice to grab other known inequality-related facts and try to use those, or reassemble things back down to a single goal after splitting; these are quality-of-life things. It's often the case that you'll have a couple spare facts floating around that could resolve more goals, but `distinguish` will ignore them, or you'll have a fact like `h : (∀ P : Nat, P = 3 -> P > 1) ∧ (C ≠ D ∨ V = W)`, and if you end up with a pair of goals you have to resolve them across two lines with `exact h.left; exact h.right` instead of just `exact h`. Low frequency, but possible.

But overall, that's it, that's how it works, it's just a Monad, it's got a little scripting language in it, and now I've taken about ~2000 words more than the LTPG to explain the same things but worse, but it was fun to do it and that's what matters.

Thanks for nudging me towards writing about it.

/Joe

--- Footnotes


[1] Of course, this is equal parts real -- I do mean this as a direct letter to you; but also it's just going to be stuck in the repo and and anyone'll be able to read it, and I've written explanations of stuff I'm sure you already know well from experience with Haskell and the like, so it's still also kind of a blog post? Left as an exercise to the reader.

[2] It is, of course [more complicated than that](https://leanprover-community.github.io/lean4-metaprogramming-book/main/02_overview.html#manual-conversions-between-syntaxexprexecutable-code), you can bypass Expr, you can convert things back and forth, the parser is _extremely_ flexible.

[3] This is a lie, I started in a much less structured way that mostly involved me copying large chunks of Mathlib and hitting it with my face until it mostly worked. I cannot emphasize enough how far from comprehension some of this is to me; it's delightful.

[4] I am _positive_ there is a cleaner way to do this; I don't know what it is, but I'm sure that spending more time building up a better structure over the proof would help simplify the monster here, but the critical thing is this does work for most of what I need, and so the tyrrany of the local optimum is _definitely_ going to win.