# 25-FEB-2026

## 0028

I can't believe I didn't have this going already.

I'm trying to reorganize things a bit. I have a huge pile of general theory that I had to build up to formalize 3.2, and
I learned a bunch about the namespace system, and I have a rough idea of what I want to do, but I'm trying to think of
the best way to structure things.

My current setup has

```
Geometry/
    ChX/ -- directory per chapter
        Prop/
            PY.lean -- file per proposition and related correlaries. Currently contains a bunch of loose theory
        Ex/
            ExZ.lean -- file per exercise (if multipart, it's all here).
        Prop.lean
        Ex.lean
        README.md
    Theory/
        Concept/ -- A directory for each "Concept", e.g., Line, Betweenness, Collinearity, Intersection, etc
            ChX.lean -- A file for all the general theory needed for that chapter. May depend on previous chapters.
            ChX/ -- if there is a directory, ChX.lean should exist to bring in it's contents
    Syntax.lean -- any custom syntax I need at the topmost level, mostly empty
    Tactics.lean -- imports mathlib tactics
    Theory.lean -- imports everything, main entry point to the theory
Geometry.lean -- pulls in the chapter propositions and exercises via the `Prop.lean`
```

This mostly lets me interleave and get all the ordering right, but it's a bear to build the main import file
(Theory.lean) because the order of the tree is wrong, chapters should parent concepts, but then I have the opposite
problem in the directory structure -- I have to replicate the concept folders over and over.

I _really_ wish that lean just jammed everything into a database, workedout the dependencies, and complained when it
couldn't. Maybe the module system will fix this? I haven't really looked too much into it except for my initial attempt,
I'll have to investigate.

For now I suppose I can write a script to generate the theory file.

I added a flake.nix and set up python, so I suppose I'll use that. I saw the blueprint tool uses python to interact with
the lean code to generate the graphviz file, so maybe I can crib from them a bit.

Unrelated, it'd be very cool to build some kind of geogebra/lean connection (maybe using
[proofwidgets](https://github.com/leanprover-community/ProofWidgets4)?), not sure the feasibility (especially since I'm
not on vscode which I suspect is required, but haven't found an explicit statement thereof).


# 25-FEB-2026

## 2235

I got pretty much everything reorganized, it wasn't _too_ painful. I also rewrote a bunch of proofs in a much nicer way;
in particular `Line.line_trichotomy` is a really handy tool.

The debate now is whether I'm going to automate generating the Geometry.lean and Theory.lean files; and more generally
it'd be nice to have some scaffolding scripts for creating new chapters/etc in the correct structure. I had a `ChX`
chapter-template, but I wasn't sure what I was doing when I originally made it. The things I'd like some kind of
template/script for are:

1. Constructing the Geometry.lean, which includes all the actual chapters
2. Constructing the Theory.lean, which is where all the general theory and lemmas go
3. Constructing the `web` and `print` blueprint files via some introspection over all the theorems/lemmas in the
   codebase
4. Creating a new chapter/theory section according to whatever strictures I need.

I don't think I'm going to do this now, I'd like to get back to proving, but something to think on.

# 26-FEB-2026

## 2145

I'm making good headway on formalizing Greenberg's proof of 3.3; there was mostly just small stuff missing; my proof of
step (5) is close to done, but the proof is quite big as a result, and it's a conjuction of two similar but very
slightly different arguments that is going to be hard to `suffice` away.

I also ran into a new problem, speed. I made liberal use of `tauto` across this code base and it is starting to hurt.
It's mostly just laziness and a misunderstanding of cost; I've started taking it out where possible. I'll need to add
another script (or maybe a lint) to count these and chase them away. I'll also need to add a profile step to the CI. The
stats it produces are pretty basic, but it's more than enough to chase away performance blowups. The issue does seem
local to the proof (which makes sense, as it's essentially just hammering away using the available hypothesis, which
don't cut across proofs), it's interesting how proof complexity becomes a performance hazard; you lose a powerful tool
when the proof is too large. Even if you don't intend to keep the tauto, knowing that your environment has all the
equipment needed to finish the proof is quite useful, and if the proof is so complex that tauto takes forever, you are
essentially blinded by your own inefficiency.

Refactoring has always felt like an 'elegant' thing to do; and it's neat to see that mathematical parsimony, clever
argument, and smart lemma choices; things that feel themselves like elegance, are directly correlated with each other in
such a nice way.

I fucking love math.

Going to take a break from 3.3 and clean up tautos for a few commits.

# 27-FEB-2026

## 0041

Working with collinearity is a pain; I currently have it limited to a triple, so reasoning about larger bodies of
collinear points is a pain (I have to manually extract the induced line for each triple and manually correlate them). I
have a similar problem with `distinct`, which is for pairwise distinct things-with-equality.

I need to build some better tools for reasoning about these, because it makes proofs a pain to follow and is a common
place where I burn `tauto` time.

# 28-FEB-2026

## 2220

I'm getting into the weeds of API design here and I'm finding an increasing need to learn how to actually use the Elab
and stop cobbling together snippets and screwing around until I get it working. There's a cool project about
metaprogramming in Lean which is itself a lean project, so I might take a little time and go through that.

The main struggle right now is with coercing lean into an ergonomic API for talking about `distinct` points and
`collinear` points; in particular, I'd like to have theorems that are something like:

```
distinct A B C ... /\ D =/= ...
```

I decided I'd talk about this in a vlog, so if I ever post that anywhere I'll edit a link in here.


# 2-MAR-2026

## 2145

Got `distinguish` working, I need a lemma, though, to decompose a `distinct` term in the goal to it's relevant ineq
goals; and then I get to do more repairs on proofs to get them running again. The `distinguish` stuff was certainly a
trip to get working; it's simultaneously very easy and very hard to think about metaprogramming Lean. `collinear` is
going to be another headtrip, I think.

Skunks are out, though, so spring is coming soon; and spring means open windows, and open windows are good for math.

# 3-MAR-2026

## 2245

Prop 3.3 is done, but nasty; it's actually been done for a bit but I've been working on something else. A couple things,
actually.

First I got `separate` working so now `distinct` conditions are pretty easy to deal with. Ex 3.1 is much improved as a
result.

I started working on generating the blueprint; but there's a ways to go.

The proof of 3.3 is very long, and I have to replicate it pretty heavily to prove the other half of the condition; which
is pretty gnar. It's the same up to some renaming, but I am having trouble seeing what I could extract. I did do a bit
to allow `collinear` conditions to stand in directly for lines in all but the case where I'm trying to prove `A on cL`,
where `cL` is a collinear condition. The prover gets confused about what kind of membership it should use, which breaks
stuff.

I might try just winging it with the other half and see if I find a shorter approach, I have an advantage of not minding
tedious cases that maybe would scare off someone in a setting where case-reasoning is cheaper.

# 4-MAR-2026

## 0020

Some thoughts before guitar and bed.

I think I need some work around `concurrence`s, which are groups of concurrent lines.

A frequent headache is managing various appelates of the same line. A set of collinear points induces `O(n^2)` 'line
throughs' by picking pairs of their points. All of these lines are geometrically identical; but in the prover, they're a
big ol' pain in the ass. I've been thinking about this in the context of more automation for distinct / collinear, but
there are a couple properties of these things that are kind of interesting.

1. Any subset of a distinct/collinear/concurrent set is distinct/collinear/concurrent -- follows from the underlying pairwise equality/inequality
2. for a 'negative' property, like distinct, combining two distinct hypotheses is pretty difficult, it requires `M * N`
   proofs, where `M` and `N` are the numbers of points in the structure.
3. for positive properties, it's often possible to satisfy entry much more easily. Collinear points only need to prove
   they lie on at two induced lines; Concurrent lines only need to prove they're equal to any of the other lines in the
   set.
4. Concurrency and collinearity are related -- all those linethroughs are concurrent, and concurrent lines share the
   same underlying collinear set.

It's neat how being forced into hyperformality here makes it really clear to see some of the dualities -- theorems have
very similar proofs despite the type change, and even the underlying plumbing is really just considering the
relationships between points and sets of points.

In any case, the aim is to build some more structures, probably divide up the `theory` section more, I'm not super happy
with the way it's broken by chapter, I think it's maybe better to try to further divide up things; I believe there
should be a way to re-export from the various files; so that I don't have to import everything by hand; but to be honest
the module system (or import system, not really sure which is which) is a mystery.

# 5-MAR-2026

## 1316

Finished 3.3, there are some corrolaries to wind up, but the main bulk is done. The proof is _very_ long and pretty
nasty, so it probably needs an intermediate or ten to clean it up.

I started thinking about a couple tasks I want to do:

1. Alignment/Concurrence -- a generalization of the `collinear` condition to accept an arbitrary set of points,
   convertible from `collinear`, but covers all the line equality constraints automatically.
2. Separating `Theory` a bit more, creating namespaces for `Ray`, `Segment`, etc. Cleaning up naming, and ideally
   getting `aesop` tags set up?
3. A `construction` or `diagram` DSL for describing how to construct a diagram that can then be reasoned about; building
   up the types of propositions by a series of operations that guarantees we're not assuming invalid constructions in
   the type.
4. Getting `leanblueprint` 'working', which probably means replacing it. I have `scripts/DumpDecls.lean` which outputs
   some JSON, I don't like how manual the maintenance of LBP is, so something automated might just obviate the need for
   all the TeX stuff. Whither plantuml, graphviz, or otherwise.
5. Extending `Betweenness` to arbitrary length, inferring all the internal conditions; this notation would simplify the 
   density axiom a bit, and is pretty natural.

I think the plan is to prove the corollaries, merge, then figure out which way to extend; I definitely need to do some
more refactoring and cleaning, I think the blueprint stuff will help.

# 13-MAY-2026

## 1600

I spent a bit of time refactoring 3.3, extracted a helper, had a small think about how much to tweak the arguments
Greenberg made for Lean convenience. I went with a hybrid approach, some theorems will get refactored for my own sanity,
some will be kept all inline so it is clear which chunks of lean correspond to which statements. I think that will help
identify where Greenberg is making intuitive leaps that are worth examining closely, while still leaving me with tools
ready for proving other things.

I left this project for a bit while I worked on other things, but I'm going to come back to it now. I'm pleasantly
surprised at how well Lean has remained in my brain despite a couple months of hiatus.

# 18-MAY-2026

## 1454

Time to talk about Agents and LLMs and this codebase.

First things first, all the math is me. No agents involved in the primary proving of anything beyond the occasional
'remind me how this syntax works'. I want to be clear that humans are doing the math here, not agents.

Second, the `distinct` and `collinear` syntaxes, as well as most of the 'small' syntax tweaks (`obvious`,
`by_exhaustion`, etc) are mostly me, similar to the above, with the occasional 'add the six other cases following the
same pattern' level prompting. Edits, but small and proscribed.

Third, `atlas`, Atlas is almost entirely LLM-coded. I guided it through what I wanted the parser to do and what kind of
information I wanted to record. I also had it mechanically convert all the various callsites to use the system and
generate some 'pithy' names for things.

Now let's talk about why I think this is okay, as these tools are controversial in a way that feels hysterical.

### Pneumatic Nailers and Table Saws, Lathes and Agents

The Pneumatic Nailer, "Nailgun," was introduced in 1950. It was designed to speed up the construction of houses by
making floor and wall sheathing much simpler. Instead of manually hammering things, you'd use instead a bulky,
unreliable, expensive and power-hungry pneumatic nailer to do the work that a journeyman carpenter could do in about the
same amount of time as a journeyman carpenter could do it with a hammer and practice. You can imagine how large house
building companies would embrace this technology, even as their more seasoned workers hated using it. They were
dangerous, the broke a lot, they cheapened the trade and reduced the skill floor. Some punk kid on the jobsite could
pick up a nailgun on day one and be installing subfloor, where was the craftsmanship, where was the quality? Are we just
gonna _not build good houses anymore?_

No one thinks using a nailgun isn't homebuilding anymore. No one thinks that a nailgun-based home construction technique
builds a materially _worse_ home. They might argue homes are worse today than in the past, but as someone who has been
around old and new construction my whole life; it's always been about as bad as it's always been.

Table Saws probably were similar. No more need for proper form and structure; no need to practice technique. Just
measure twice, cut once, make sure you know how to avoid kickback.

I heard a story once about Norm Abrams, the host of _New Yankee Workshop_ and a personal hero. He got his first
on-screen job after having worked as a journeyman carpenter on a job for the producer of _This Old House_ before it came
on the air. In the late '70s, the use of power tools would've been common, but it wouldn't've necessarily been the only
kind of homebuilding, and while a radial-arm probably would've been the standard power saw on a jobsite, it is easy to
imagine such a thing leading some to wastefulness and carelessness. It's so _simple_ to make a cut, it's so _easy_ to
get it to the right size. Norm got the job because of his efficiency with the tools at hand, and the rest is TV history.

In my shop, I have a woodlathe. A lovely Grizzly that spins large hunks of frequently unstable wood by means of various
chucks and mounts and a big ass electric motor on the back. I can twirl a hunk of hickory at 2500RPM and stick a tool
into it. It is by far the most dangerous tool I own; it actively wants to kill me, it wants to see me dead, it wants it
to hurt the whole time. In the old days, a lathe would've been made of wood and rope, and powered by a 'spring pole' --
a green stick that would reciprocate the work back and forth in time with your foot movements. It was safer than my
lathe, slower too. I imagine the introduction of the electric, motor-driven lathe might've left spring-pole enthusiasts
worried about the craftsmanship, the reduction of the skill floor, the worsening of their trade.

But I can turn beautiful work on my lathe, even though it wants to kill me, even though it is more dangerous. To be
honest, I'm not sure I could produce the same quality of work on a springpole, even if I started with it. There are
limitations inherent in the tool. The reciprocation means different techniques are available and different constraints
are in place.

### Tools and Weapons

My path through LLMs has been pretty bouncy. I started with the same curiousity as everyone. I tried GPT4 and early
copilot-style autocomplete. I thought it was cool. I used it in `hazel` for a bit, but rapidly found, like most people,
that the code was poor quality and not much better than cut-pasting. I spent a lot of energy cleaning up that mess, and
Hazel is better for it, but almost none of that code remains[1]. As I learned more about the ethical... well let's just
go ahead an call it what it is instead of euphemizing it as an ethics problem. The big "AI" companies committed the
largest act of copyright infringement to have ever been done. It makes Napster look like shoplifting. It was simple
larceny. They stole petabytes of art, literature, and music; packaged it, and sold it as if it were theirs. Depriving
the original creator of the value of their labor. This is unconscionable and wrong in a way that I'm comfortable
thinking of as Sinful, with all the weight applied to it as I would have when I was an Evangelical Nationalist Scumbag.

It was simply evil behavior, performed by evil men (it is always men, it seems), and they should be shamed, pilloried,
and launched into the sun for having done it. These facts, and the existential threat to my job and career, the threat
to my family by dint of that, and all the myriad anxieties the "AI" tulip craze that was and is and will continue to
spiral until crashing -- as it inevitably will -- led me towards a sort of deep hatred for the technology. It wasn't
until I realized how I started talking about it that I understood the mistake I was making.

I started calling LLMs "the False Prophet," I thought of them with irrational anger and disgust. I transferred the shock
and horror and dissapointment with the actions of their creators with the tool itself. I was _mad_ about it. Then I got
tagged by my therapist, "It sounds like you're pretty heated, Joe. But don't you always say, 'it's a poor craftsman that
blames the tool?'"

Here's the reality we live in, folks, the deed is _done_. We can mourn the past, but not return to it. We are _here_
now, _alea iacta est_. The constant cry of 'WeLl NoOnE iS mAkInG yOu UsE iT!' falls on deaf ears the moment my families
livelihood is in peril. You are right, no one is _making_ me do it, just like how no one will _make_ food appear on the
table. There is no ability for me to respond against the crushing weight of the machine that has been so long built by
capitalists and bastards (sorry to repeat myself), so we can have no responsiblity other than to ask now, "What do we
fucking _do_ with the monster they made?" "Is it the monster's fault that Frankenstein made it?" "Should we kill it simply
because its creation was abominable to us?" "Isn't that cruelty too?" "Isn't that wrong?"

I don't mean to say we would be killing a literal, living thing, but I refuse the notion that a tool itself is ethical
or not. I suppose, if pressed, I'd have to say that the argument that has always seemed strongest to me about gun
control is the 'Guns don't kill people' argument. It's simply correct, guns _don't_ kill people, it's irrefutable in
some sense. Whether through intent, negligence, or mistake, it requires action on the part of _someone_ to make the tool
into a weapon and for that weapon to harm another[2].

I don't want LLMs to be weapons, but the only way to make them _not_ weapons is to find out how to _use them like
tools_. I can't assign ethical or moral value to the machine-what-is-made. I can only try to understand the effect of
its existence and how I can use it to find ways to be kind.

I have a lot of thoughts on how that might be done, but the first step is to learn how to use the tool in ways that feel
like I'm producing something that might actually benefit people sufficiently to justify the cost of the tool. I have
spent some months now unpacking and understanding this technology. I think it has broad, mostly unexplored uses, uses
that could legitimately benefit more than the cost. I think that there are ways to get these tools to produce good
output that can be genuinely useful and improve peoples lives. If you don't, cool, don't use the tools, but I will
accept criticism of my use in precisely one form, `&> /dev/null`.

[1] I caveat only because I truly don't remember which code was generated anymore, almost all of it has been touched at
this point though so it's probably gone.

[2] This not to say that it is a good enough argument to justify all the things people try to use this to justify, we
still need gun control for lots of good reasons, but it's complicated by the fact that this is, ultimately, a pretty
good fact the gun control advocate needs to reckon with.


### What is good code?

Once I started trying these tools I started to ask a new kind of question, not "Is this good code?", nor "Can I make
this produce good code?", but "What is good code?"

In mathematics, we focus on properties. We might say that a line has the property of being defined by two distinct
points; and conversely that two distinct points have the joint-property of defining a unique line; and so on. I started
to ask "What are the properties of 'good' code?"

I was easy to enumerate many _features_ of good code. It's well-factored, it's well-tested, the tests are resilient and
easy to understand and change. Really the whole codebase should be well documented and easy to understand and change. It
should be well-specified and it's edge cases well tested. I should be able to trust the code and when my expectations
about it's output fail I should be able to easily identify, isolate, reproduce and change the code to address the
failing.

There was a theme developing, it's not hard to see, good code is:

1. Easy to understand
2. Easy to change
3. Well specified and well tested.

None of those things constrain the _shape_ of the code, or its implementation, the only constrain what the code _does_
and what you can _do to it_. Does it matter how I answer those questions? If I can read a good codebase, let's take
`ripgrep` as an example, I can see structure present there, I can build up a mental model. I might have to spend a bunch
of time learning the machine's innerworkings, but the code is _good_, it is _well factored_ and _precise_, it minimizes
mental load as much as it can for being a complex tool with many precision engineered parts.

It is easy to understand (relative to your understanding of Rust and the techniques involved), it is easy to change
(because it is well-factored, and assuming you have a good existing understanding of the design of the system), and it
is well specified and tested. It is Good Code (tm).

If I think about the `Atlas` thing I just built, it is also easy to understand -- if I have a question about the
structure I can ask the LLM, I can get a line-by-line walkthrough if I want. It is _much_ more adept and API-aware than
me, and while it can often write code I don't immediately understand, there isn't any part of it I am _incapable_ of
understanding, and with sufficient curiousity I can learn the deep parts fo the system just as before.

Arguably, it's _easier_ to change than a handrolled implementation, I just have to precisely describe what I want. Often
that means giving it instructions about how to rewire the machine's internals (not the oft-assumed "write me a tool"
prompt, rather a "adjust how the syntax is parsed here to use this API in this way." It's certainly less typing than
before, and as someone who spends most of their waking life typing things into this infernal box, less typing is a
_massive_ win for my physical and mental health.

It's lean, well-specified here means 'comes with mathematical proof', but even in other languages you can pretty easily
build up a comprehensive test suite; optimize it; measure its coverage; mutant and fuzz test it -- the incremental cost
of testing your code is now nearly zero, the incremental cost of changing it is zero. The places where we have trouble
are in getting insight into the internal, abstract structure of the code. Before the bottleneck was _writing_ code, now
the bottleneck is _understanding_ code and its structure.

So, no matter the implementation, if I can answer those three questions in the affirmative, isn't whatever I have -- by
definition -- good code? It is not _pretty_ code -- I don't like the look of LLM-generated code more than most people,
but in the fully 'vibecoded' ecosystem, the reality is the codebases are perfectly cromulent, so long as I don't really
read the code too deeply. The skeptics among you clutch their keyboards and say "But how do you know it works?" To which
I reply, "My test suites are more thorough than anything I could write on my own, I have every possible path covered and
specified, I built tests which test my tests to ensure the tests are testing what they are supposed to test. I have
mutation testing, fuzz testing, property testing, unit and integration tests, I test in situ, I test end to end. Some of
this stuff is _literal, mathematical proof_ What more could you want to prove it to you? How much do you have? Why
should I trust _your_ software? Do you have formal proof it works?"

The refrain of "It's not good code" relies on a notion of 'good code' that is optimized not for what good code _is_, but
for what _good code is for a handwritten, human codebase_. The issue is that we have mistaken the _limitations of our
tools_ for the _indications of quality_. We are overgrown monkeys doing mathematics on specialially arranged rocks; we
have designed practices to accomodate for our weaknesses; but those practices are, themselves, no different than the
hours you'd spend hucking a hammer at a nail installing sheathing and subfloor; they're no different than the time spent
structuring your body to properly cast and return a handsaw. We have new tools now, we need new practices, and that
means new understanding of what good looks like in a new context.

I'm not saying every project is a vibe project. Indeed, this is an example of a project which is emphatically _not_ a
vibe project. Why? Because the point of this project is for me to engage the math and build something mostly by hand.
LLMs enter into it more like a orbital sander. Is hand sanding "better"? No, it's different, it leaves a different
finish, people may be able to spot the tell-tale circular pattern, but it's not _better_ to sand by hand, it's not
_worse_ to sand by machine. It's not _better_ for me to manually replace every `theorem <name> : <statement> := by
<proof>`, an LLM can do that work for me in much less effort (though not much less time, if I'm honest); it doesn't
detract from the product to automate away those sorts of changes, and indeed it allows them much better and richer
tooling later.

My point is simply: If you are reacting to these tools with anger at the loss of the old ways of doing things, I feel
you, but you don't get to uninvent the nailgun. You can't un-table the saw. The only question is 'do these things have
any use at all' and 'is the juice worth the squeeze'? At this pint, I think at this point, I can answer at least the
former, and I'm beginning to see the answer to the latter too.

## What's the use?

The uses of LLMs in this repo have been stated, but at a higher level, I use LLMs in the following ways to good effect:

### Mundanity

#### Pure, Shameless Vibecoding:

Ask for a thing, recieve a buggy, halfworking thing that mostly just looks the part. This is entirely for the purpose of
candy. A cardboard version of a product is a useful thing for me. I am not skilled in visualizing the final product. I
may be aphantasic[3], but in any case, being able to get a cardboard cutout of a thing to look at and talk about with
people is extremely useful.

[3] I don't know, I've never been not me, so I can't tell you whether I'm seeing more or less in my 'mind's eye', I can
say that I have always assumed that to be much more metaphor than other people I know

#### Data gathering and scutwork.

There is a large class of things for which I need the product of a process but have no interest in its performance / I
do not stand to gain a skill I want from practice there. This ranges from truly mundane questions like finding facts
about pricing or API shape, to researching bugs in my editor configs. I cannot express to you how little I care about my
dotfiles. I simply couldn't give a shit if they look nice or are wellmaintained. I want my editor to always do exactly
what I want, I don't care who maintains it or how, I don't care about it at all, it just has to always do exactly what I
expect and otherwise be a transparent thing. The most common cause of project abandonment for me is _not_ an overhard
problem, it is always the same thing. Some externality -- editor config, testing/hosting infra, etc -- gets in the way
of me continuing to work on the interesting part of the project. WLOG, let's call that class of work scutwork.

Scutwork is a necessary evil, with greater emphasis on the 'evil'. It is weapons-grade boredom, and the answer to this
has always been "Use this framework, set it up once, and try not to think about it." or "Just fucking do it."

Fuck every square millimeter of that. I don't want to maintain that shit, and frankly I don't know anyone who actually
does. If you are one such person. I think you're weird (complementary), and I do not aspire to be like you. I'm here to
do math, not convince Neovim to stop being so fucking stupid.

### Targeted Refactors / Draw the rest of the fucking Owl

Prop 3.3 in this repo has a case where LLMs helped greatly with the math. There is a common, underlying argument in that
setup for the Line Separation property (3.4), and I could see it, but extracting it from the haze of specific variables
was really, really hard. I could smell it, but I couldn't hunt it down. Excitingly, this intuition came first from the
code, and I aligned it with the intuition in the math. It was a delightful moment when I linked the two things together
and felt the intuition in the math spill onto the code and the real _power_ that Lean might offer was spread out. Then I
realized how _fucking awful_ it was going to be to extract that common argument, so I put down the project for 2 months
and dealt with my anger around LLMs.

Then I asked Claude to highlight the extractable argument after describing what I saw, it made a suggestion, I verified
it, did the proof, and then ported it back into the proof. From there it was much, much simpler to complete the other
branches of the proof complex, and thus 3.3 was closed.

In another project, I inherited a pile of 50 or so jenkins pipelines. I do not know groovy, but I can hack together
something that is almost valid groovy and expresses the intent accurately. I left the code littered with little todos
and then told Claude to paint inside the lines I left it. Twenty minutes later I had the rest of the fucking owl, and
all my pipelines ported. I genuinely would have taken days or weeks to do that alone.

I don't need or want to be a groovy expert. I don't need or want to spend hours meticulously adjusting incantations to
satisfy Lean. I want to spend my mental energy on the overall CI ecosystem. I want to spend my time in the Math. LLMs
let me be efficient with _what skills I'm reinforcing_ and _what I delegate to someone (or something) else_. If I had,
at my disposal, an army of grad-students and interns and junior engineers, it is the class of work I would send them off
to do not because I thought it would improve their ability to do their main jobs, but because I would not like to do
that work and I have an army at my behest. I did not have such an army before, now I do. Now if I acquire such an army,
I can send _them too_ on missions of _actual_ import to their _actual_ goals.

## How much juice?

LLMs, Agents, "AI", whatever you prefer to call it, it is not _useless_, it's not perfect, it's a machine that guesses,
and guesses are not useless things. You _can_ get these tools to produce good code (under both understandings), though
human-good code is much more difficult to achieve, it is possible to do so with sufficient prompting and oversight. In
this project already it has more or less covered a month or two of weekends worth of scutwork that, frankly, probably
would've killed this project.

Is this project valuable? It certainly is valuable to me. It feels good to work on this, I like that I found a way to do
_real_ math again, not the idle pining for a life not lived, not the silly doodles of differential equations in
meetings; but real, honest-to-goodness math.

Is it valuable to others? I don't know, I like to think Atlas will be a generally useful thing, and maybe someone,
someday will ready the body of GIYF or tour through the Atlas site and learn something useful. I don't know that what
I'm doing is _"Good"_. I'm not sure that _Good_ is even a meaningful concept so much as a pleasant fiction -- a lie to
children -- that we tell to make ourselves feel better about a reality that is fully indifferent to us at all levels,
times, and spaces we inhabit. I can't tell you to like this work, I can't tell you to accept it, or even to not hate it.
If my use of agents bothers you, I have empathy for you, but for me -- their use lets me do the things I want to do in
life, and none of us asked to be here, or be thrust into all this. For me, I'm going to use the tools available to me in
the most responsible and efficient way I can. I promise I won't act carelessly and wastefully in their use, and I won't
treat them with the kind of flippancy that many do. If that is insufficient for you, I'll give you the same response I
put in a recent commit removing the anti-LLM canary.

"I do not care."


# 24-MAY-2026

## 1219

I've been doing a series of largely mechanical refactorings and restructurings. The main thrust of which is a typed
heirarchy for line-parts (which is not _exactly_ what I wanted, but is a significant improvement over the prior state).
As well as trying to capture what Greenberg considers 'obvious' in a tactic (creatively named `obvious` as well), which
I'm hoping will leverage `atlas` at some point to do a phased 'intuit like Greenberg' automated theorem proof attempt.
The aim isn't necessarily to replace every place Greenberg calls a 'clearly X holds' or 'obviously Y is true' with this,
but most of the cases where he does, the result is really trivial and should be inferred without argument. _Sometimes_
(as in Pasch's 'A and B are clearly not on L') the argument isn't necessarily so obvious, though, and these are
interesting places where Greenberg's intuition might've been making 'leaps of faith' which should have been justified
more thoroughly. In the end I hope to capture all the little intuitive, subconscious arguments that Greenberg used and
develop something like a 'If Greenberg were arguing here, he would consider this subtextually true / true without
argument' as a sort of research artifact.

The process of getting there has been an interesting application of LLMs in this space.

In particular, the process has been one of "Let's build up a structure that ties into the existing mathlib machinery to
represent lineparts." This involved fighting with Coe and the elaborator and some other syntax fighting. I estimate it
would've taken a few weeks of solid effort to get done, Claude finished in a day. That's an honest-to-goodness savings
on work I really didn't want to do. Most of it was weedy, mechanical shit of wiring up and rewriting after each
iteration to get the corpus compiling. I'm barely 20% through the book and have about 4KLOC of lean, most of which are
lemmas-in-anger, so being able to mechanically replace a component like that was a very legitimate value add.

I don't think, however, it would've come up with the structure on it's own. It was struggling to understand _why_ I
cared about making these parts flow together; and frequently suggested some flavor of "We're at the limits of what Lean
can do." until I reminded it of some other extension we could try. We did eventually hit the limit (there is an
irreducible type ascription necessary in some few cases of intra-type equality comparisons), but it was only after
blowing past a few others that the machine thought existed.

Once the apparatus was built and installed, the really interesting step happened. The `obvious` tactic was able to close
out entire lemmas that were proved before, resulting in a significant reduction in the total surface area of nontrivial
theorems. If a proof is just `:= obvious`, then every `ref` to that theorem can be replaced by `obvious` to drop one
layer of indirection. So I instructed the machine to do the following:

1. Go to each lemma, replace it by `obvious` and see if it closes, if it does, mark it for inlining.
2. Go to each marked lemma and inline it, replacing all of it's occurences with a `obvious`. If the inline fails, raise a flag

No flags were raised, and a bunch of lemmas (about a dozen) dropped away. Crucially, though, some of them _didn't_ and
in fact, _couldn't_, these were the core underlying 'obvious' facts that Greenberg takes without proof, but are
necessary in formalization. I landed on something very neat, by 'shaking the tree' to try to refactor proofs to use more
of Greenbergs intuition. I got proofs back that were closer to the book, but also got proofs that were irreducible and
unstated by the author, meaning they represent some fundamental component of his intuition. They were required by
`obvious` to close the other goals.

It also led me down this other interesting path adjacent to but distinct from other automatic theorem prover tactics.
Consider the humble `tauto`, which has this problem:

> Given an arbitrary type with universal and existential quantifiers, a proofstate full of hypotheses of arbitrary
> shape (also with various quantification) and a corpus of theorems about as wide as `@[simp]`'ll get you, resolve the
> goal.

There is no context on what kinds of theorems there are, no insight into the relevant corpus of math, no ability to
filter or prune anything. It's a really hard problem, and people have come up with extremely clever ways to optimize it,
but math isn't a 'prove any theorem' game, it's a 'prove _this_ theorem' game. When proving, one has the _context_ to
rely on. I know I'm proving theorems in synthetic geometry here, I don't need to consider calculus or number theory
(yet). I can limit my scope much more aggressively if I look at the proof goal and see it involves intersections, I can
make more complicated, geometry-local arguments that wouldn't necessarily translate wholesale to other fields. In a
sense, the progress in the unconstrained world is stymied _by_ the lack of constraint. It is much harder to do math if
you don't specialize.

So `obvious` is sort of a start towards a specialized "geometry" tactic, but it's even more specific than that, it's
_Greenberg_ that I'm modelling here. It's a _specific_ intuition (as captured by the book and my formalization of it,
which means it is not without some bias), and I think that's pretty cool. I can imagine building up a little library for
designing these bespoke tactics per book. Then when the time comes to prove something new I can throw a corpus and it's
corresponding intuition at it for the low cost of translating it to the language that tactic understands.

I'm sure the idea isn't novel, but it is fun, and blends nicely with the `atlas` thing I've worked on. I should be able
to incorporate some ranking/searching directly in the graph, which means I can have the structure inform how best to use
the structure (a theorem with a high pagerank after a specific filter is applied might be a good way to search corpii
efficiently).
