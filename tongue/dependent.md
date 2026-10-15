# dependent tung design

audience: agents. purpose: how the checker realiseth the language: the
dependent core, elaboration, inductive families, pattern compilation, instance
search, and the logical boundary. each section stateth its algorithm,
rejection cases, and limits. [`language.md`](language.md) owneth what a
program author writeth and observeth, and this document linketh to it rather
than restating it. [`todo.md`](../todo.md) tracketh remaining work.

## implemented core

`Tung.Dependent` provideth a checked dependent lambda calculus, following
[lambda pi](https://www.andres-loeh.de/LambdaPi/) for products and the
[lean inductive rules](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/)
for generated eliminators. its api is `infer`, `check`, `define`,
`validate`, and `normalise`; `defineInductive` checketh rigid declarations and
`inferInductive` first generaliseth valid universe constraints, with
`defineInductives` and `inferInductives` for mutual groups. applications keep
their visibility: inserting omitted source arguments belongeth to elaboration,
and runtime erasure is separate.

### terms and conversion

- one `Term` representeth universes, dependent products, annotated lambdas,
  applications, local bindings, and globals. locals use de bruijn indices and
  semantic neutrals stable levels.
- conversion useth beta reduction, local substitution, transparent
  definitions, function eta, and exact universe equality; there is no
  cumulative subtyping.
- evaluation is glued. a transparent global applied to arguments stayeth
  folded and unfoldeth only when forced. public results are forced at the
  head, except an application's argument, which only instantiateth the
  codomain and stayeth folded, so checking `t greatness` computeth no closed
  `t`. conversion accepteth identical folded terms, universe arguments
  included, and otherwise compareth both normal forms. folding changeth no
  equality. motives keep definitions folded.
- display quotation unfoldeth a definition only to reach a constructor,
  literal, record, or variable, and showeth a stuck elimination equal to an
  enclosing definition applied to the eliminated child as that application.
- public normalisation checketh its input first; raw NBE is private.
- only checked, closed declarations enter the environment. transparent globals
  are ordered and cannot reference themselves; there is no general recursion.
  inductive families, constructors, and eliminators are checked and inserted
  together. named assumptions and trusted host constants extend the axiom-free
  fragment under the [logical boundary](#logical-boundary); host constants
  enter only through the [catalogue](#deeds-and-host-bindings).

### universes

- `Sort u : Sort (u + 1)`, and a product of domain `Sort u` and codomain
  `Sort v` inhabiteth `Sort (max u v)`.
- levels are never written. each surface `*` and global universe argument
  getteth a fresh level hole; direct hole equations are solved, and remaining
  holes become universe parameters qualified by their constraints. a program
  needing a relation inference cannot find is rejected.
- maximum constraints keep their alternatives: inference never guesseth a
  branch. generalisation discardeth tautologies by the same canonical atom
  comparison as insertion.
- each global application instantiateth and checketh its exported constraints.
  a declaration's obligations share prepared assumption clauses and atoms. a
  conclusion clause holdeth when every alternative of one assumption clause
  hath a weaker counterpart in it; otherwise the exact solver refuteth its
  negation, keeping disjunctions and both directions of equality.
- the exact solver useth difference constraints with negative-cycle detection.
  a new edge restarteth bellman-ford from the current feasible assignment. it
  accepteth an assignment satisfying every remaining clause before branching,
  rejecteth a maximum clause whose every alternative contradicteth the fixed
  graph, and skippeth clauses the assignment satisfieth. maximum constraints
  may still need exponential search.
- inconsistent constraints are rejected before normalisation proceedeth. the
  checker keepeth the constraint set's atoms and simplified clauses, a
  satisfying assignment, and the edges it was built on. a new constraint the
  assignment satisfieth is accepted at once. a violated one first extendeth
  that solution with its own edges and searcheth the disjunctive clauses from
  there; only when that faileth is the whole set solved again, from the last
  assignment, so no satisfiable set is rejected.
- the kernel rechecketh generalised terms with rigid parameters and proveth
  every generated obligation from the declared assumptions.

### logical boundary

the pure core is a fragment of predicative intensional dependent type theory
with universe polymorphism, strictly positive inductive families, and closed
records. `Sort 0` is an ordinary data universe, not an impredicative `Prop`,
and inference never permitteth `Sort u : Sort u`. recursion goeth through
checked eliminators; runtime deed loops do not reduce in conversion.

`sorry: [@α: *, α]` can inhabit an empty type, so the language with
unrestricted `sorry` is inconsistent as a proof system, and a runtime failure
doth not repair that. checking accepteth terms under it;
[checking](language.md#checking) stateth how `--check` reporteth it and
`--no-sorry` rejecteth it. a host binding is trusted as a program and not
reported by `--check`. an `orsetting` is a named axiom, a constant with a
checked type and no body: a consistent proof may rely on the orsettings it
lists, never on `sorry`.

proof auditing traverseth checked types and bodies across imports, including
selected dictionaries, host models, and inductive metadata and computation
rules. elaboration keepeth resolved input references before normalisation can
erase them; insertion storeth them, imports and cached interfaces preserve
them, and rejected speculative trials discard them with their state. the audit
reporteth reachable orsettings, `sorry`, and host constants as a conservative
syntactic closure: a referenced dictionary keepeth all fields and a referenced
family its whole checked group, input references included. unused imports are
excluded, and no extra normalisation or name search decideth dependencies.
[proof checking](language.md#proof-checking) stateth selection and policy.

the report is relative to the checked kernel and host catalogue, not a proof
of their correctness. a modelled host operation stayeth a trust dependency,
since its native implementation's agreement with the model is trusted; the
[lean axiom boundary](https://lean-lang.org/doc/reference/latest/Axioms/#consistency)
draweth the same line. consistency of terms without `sorry` requireth correct
kernel rules, universe entailment, inductive generation, conversion, and host
operations. host data schemas are checked at binding boundaries. interfaces
are trusted compiler output reused under source, import, and build keys;
loading checketh their format and reference metadata without rerunning the
kernel. regression tests exercise these rules but are no machine-checked proof
of consistency or subject reduction.

## implemented source

`compileSnapshot`, `compileImports`, `inferSourceExpression`, and
`normaliseSourceExpression` are the library api. annotations and bodies share
one expression parser and lexical namespace, and every completed definition
and expression is rechecked by the kernel before insertion or public
normalisation.

### names and scheduling

- module definitions resolve to `SymbolId` in dependency order, so source
  order doth not matter. unknown names are errors.
- a declaration that useth a flock member, or an imported name whose checked
  type requireth a flock through an `@:` slot, waiteth for the module's bizens
  of that flock, unless such a bizen needeth the declaration by name. a local
  name's requirement is not counted: each use is ordered by name, and the
  caller's own requirement often meeteth it.
- types, flocks, constructors, members, and lets share one namespace; a module
  declaring a top-level name twice, as a flock and its member, is rejected with
  `top-level name repeateth`.
- primitive names from the [language reference](language.md#declarations-and-types)
  are visible everywhere, and an imported or local name of the same spelling
  shadoweth them. `=` and `eftbend` come from the ordinary module `is.tung`.
- local bindings are sequential and shadow visible names. binder annotations
  and local initialisers see only earlier bindings.
- a let whose body hath a free reference to its own name is recursive, unless
  a binding of that name is already visible, as an import, an outer local, or
  an active enclosing recursive binding, which the reference then denoteth. a
  header, lambda, product, case variable, or local let may rebind the spelling
  without making the let recursive. a recursive let needeth an annotation, and
  an ascribed body `let f ≔ (body: type)` counteth as one.

### binders, holes, and checking order

- bracket binders scope over later domains and results; bare and `_` slots add
  binder depth without a name. named header slots and `@:` requirements lower
  to lambdas and precede bare slots. a header slot may bind a pattern,
  `a both b: α ∏ β`: the lambda bindeth a hidden local the body matcheth. a
  bracket whose last slot bindeth, as `let f: [x:] ≔ x`, leaveth its result
  to inference.
- `fall slots, result ^ body` elaborateth as `({binders ^ body} : [slots, result])`.
- `{}` is the case function on an empty family and `match x {}` matcheth one.
  before a match decideth that no constructor fiteth, instance goals with known
  flock arguments are solved, so an impossible case seeth the selected
  dictionary compute.
- `{x ^ body}` needeth constraints or a function annotation; a typed binder,
  `{x:* ^ x}`, can infer its function type. unannotated domains are inferred
  only when constraints determine them and never introduce unwritten
  parameters.
- applications, `(expression:type)`, and `(let … yield expression)` use one
  expression form for types and values. `<{f, a, b, c}` and `>{f, a, b, c}`
  associate binary applications left and right and have no list
  representation.
- supplied `@` arguments may be types or values; the checked product spine
  consumeth implicit and explicit arguments in declaration order.
- omitted arguments become typed contextual holes solved by arguments and
  expected types. unused holes are errors, never defaults. no let is
  generalised over its holes: an open hole or waiting bizen requirement after
  elaboration and instance search is an error asking for polymorphic
  parameters or an annotation.
- arguments are checked in order, except a case function `{rows}` whose input
  type is still a hole: a hole standeth for it, later arguments are checked,
  and then the case function is checked against the fixed type. so
  `{ empty ^ 𝟘, _ ‥ _ ^ 𝟙 } throughbear p only` learneth its input type from
  `p`. a lambda whose body matcheth inside a larger expression is not
  postponed and needeth a binder annotation.
- an expected implicit product introduceth its binders before any expression
  that doth not bind them itself, as in agda, so a polymorphic name meeteth a
  polymorphic type. a polymorphic value checked against any other type, even
  an unknown one, is specialised.
- an ascription with holes first learneth from the expected type. a header
  binding its own implicit slots, as a local `[@α:, a:, f:] ≔ …`, is unified
  with the expected type first; when they agree the body is checked against the
  expected type, so untyped slots have known types, and otherwise against the
  written type, then specialised.
- argument visibility and runtime relevance are separate: types are erased,
  while implicit values and dictionaries may remain at runtime.

### inference boundary

term inference useth a typed higher-order pattern fragment. a hole applied to
distinct rigid locals is solved by abstraction, after local definitions are
substituted; occurs and scope checks reject cyclic or escaping solutions.

- a candidate is checked before assignment. one whose check would leave a
  pending equation, as a dictionary projection before search fixeth the
  dictionary, or whose check faileth while it or its hole's type still holdeth
  unsolved holes, is undone and its equation stayeth pending. it is retried
  only after a blocking hole is solved; a failure with no unsolved hole is
  reported.
- a solution may mention another hole applied to locals the solved hole cannot
  see, as `?t = ?f x` where `?t` lacketh `x`. if that hole is applied only to
  locals and its type doth not depend on the hidden ones, it is pruned to a
  fresh hole over the inputs it may keep and the solution is quoted again,
  giving `?t = ?f′`.
- a hole is solved by the unforced other side, replaced by its folded
  quotation, so a bizen's parent dictionary stayeth `#instance_n`. because
  folded solutions name constants the elaborator never instantiated,
  generalisation addeth the instantiated universe constraints of every constant
  in the final term. two applications of one constant are compared by folded
  arguments before unfolding.
- a numeric literal meeting a constructor application exposeth its outer
  constructor in either orientation: `2` against `?n heir` solveth `?n` as
  `1`, and integers use `overnaught` and `heir_undernaught` likewise. fields
  stay literals and literal comparison stayeth constant-time. induction and
  index matching share this view.
- nonpattern equations wait and are retried after each new assignment. when
  instance search or a pattern column can make no other progress, one equation
  between an applied hole and a rigid application is split by first-order
  approximation, as in agda and lean: `?f a = g b` becometh `?f = g` and
  `a = b`. it may miss a higher-order solution, so it is never tried earlier.
  while an annotation is settled, two applied holes `?f a = ?g b` split too.
  general higher-order unification is unsupported; remaining equations need
  annotations or explicit `@` arguments.
- every term hole must vanish before the kernel check; universe holes may
  still generalise under valid constraints.

## inductive declarations and proofs

```tung
ilk ℕ: * {
  naught: ℕ,
  heir: [ℕ, ℕ]
}

let eftbuild: [x: ℕ, ℕ] ≔
  {_: ℕ ^ ℕ} unbuild ℕ naught {n, ih ^ ih heir} x

ilk sameness: [α: *, x: α, α, *] {
  refl: α sameness x x
}

let throughbear: [@α: *, @x: α, @y: α, soothing: α sameness x y,
  family: [α, *], worth: x family, y family] ≔
  {z, _ ^ z family} unbuild sameness @α @x worth y soothing
```

### families

- `ilk name:signature { … }` declareth a family whose constructors share the
  ordinary namespace. the eliminator is not a name: `unbuild name` denoteth it,
  resolving `name` as a family; a name resolving to anything but an ilk or
  flock is rejected.
- the named prefix of the outer bracket declareth uniform parameters; later
  bare slots and a nested result product declare indices. a header slot is a
  parameter only while every constructor's result passeth it unchanged, so the
  slots after it are indices, as in `ilk tag: [a: *, *] { integer: [ℤ, ℤ tag] }`.
  only parameters scope over constructor annotations. inherited constructor
  and eliminator parameters are implicit whatever their visibility in the
  family.
- every constructor stateth its type, as in a GADT, and returneth a saturated
  application of its family with unchanged parameters. fields must fit the
  family's universe.
- a recursive field is a group family, or a function ending in one whose
  inputs mention no group family, as `[ξ, φ freer α]`; it must occur strictly
  positively, after aliases are normalised. recursive occurrences supply every
  parameter and index, with shared parameters unchanged. negative occurrences
  and group families inside their own arguments are rejected.
- `unbuild name` taketh the implicit parameters, a motive over the indices and
  value, one method per constructor in order, the indices, and the value. each
  recursive field is followed by its hypothesis; for a function field `k` it
  is `[inputs, motive (inputs k)]`.
- induction computeth on constructors and stayeth neutral on variables.
  arbitrary recursive lets remain errors; source patterns compile to
  eliminators.
- the identity family above giveth intensional equality and path induction:
  `throughbear` computeth to its value on `refl`. there is no equality
  reflection or proof irrelevance.

### mutual groups

- a dependency cycle of `ilk` declarations alone formeth a group, ordered by
  source position; no keyword is needed. a cycle through any other
  declaration is rejected, so lets and imports stay acyclic.
- signatures are checked before the families enter the environment and cannot
  depend on group members. names and constructors are inserted atomically
  once the whole group checketh.
- members share one parameter telescope: counts and visibility agree, domains
  are definitionally equal after renaming, and result universes are equal.
  index telescopes may differ. signatures and constructors are generalised
  jointly over the group's canonical universe vector, and the group exporteth
  its shared constraints.
- the group's `unbuild name` taketh the shared implicit parameters, one motive
  per family in group order, every constructor method in group then written
  order, and the requested family's indices and value. a field's hypothesis
  useth the motive of its own family. each motive hath its own result
  universe, so the universe vector is the shared parameters then one per
  motive.

### nested containers

- a field may apply an already checked, unindexed inductive container to
  group families, as `rose list` or `(rose list) list`, after aliases are
  normalised. specialisation arguments depend only on shared uniform
  parameters, never on fields or function inputs; group parameters stay
  unchanged; each specialisation's result universe equaleth the group's.
  abstract container heads and indexed containers are rejected.
- nested induction is a native kernel extension certified by translation.
  original constructor signatures, phantom parameters included, are checked
  first. a finite worklist cloneth each specialised container's families and
  constructors under the shared telescope, and the ordinary mutual checker
  certifieth the translated group, so a negative container parameter faileth
  strict positivity. positive function fields keep pointwise hypotheses, and
  later dependent fields must check under the uniform translation; no
  container operation is rewritten.
- restoration putteth back the original container applications. private,
  checked transparent aliases label the specialised targets, adding no nominal
  type or conversion rule; public field types, constructors, and container
  operations stay ordinary, and temporary constructors are discarded. restored
  signatures, alias bodies, and computation rules are rechecked with the new
  recursors opaque; the positivity certificate, not the rule types, justifieth
  termination.
- a nested `unbuild` taketh root motives, then specialised container motives,
  then all methods in that target order. roots follow source order; targets
  follow first occurrence in normalised constructor signatures, with ordinary
  container peers added together, and the worklist closeth over their fields.
  repeated specialisations share a target, and each target dispatcheth its own
  constructor rules. ordinary matching supplieth trivial motives and methods
  for auxiliary targets.
- every induction rule is one checked core term per constructor over shared
  parameters, motives, methods, and fields; the normaliser and runner evaluate
  those terms and never rebuild hypotheses from metadata. recursive field
  metadata nameth its target, since a container head alone cannot identify its
  specialisation.

## pattern matching and recursion

[`match.tung`](../byspel/match.tung) showeth case functions, `match`, nested
patterns, and structural recursion.

### rows

- `{p, q ^ body, …}` is a case function with one column per pattern; one row
  of plain binders is an ordinary lambda. a row whose binder nameth a
  constructor is a pattern row. leading implicit binders stay lambda binders
  and only the explicit ones form the row, so a header slot named by a
  constructor, as `eftbend:a = b`, matcheth its input.
- a case function needeth an expected type. a `match` without one inferreth a
  single result type for every row.
- every row hath one pattern per column, also inside recursive definitions.
  written rows are validated, and constructor arguments checked and aligned,
  before recursive clause collection projecteth columns or patterns are
  intersected.
- a name is bound once per written row. a name repeated in a lambda row or a
  let bracket becometh a pattern, so a constructor such as `eftbend` may
  repeat, while a repeated variable is rejected.
- rows are tried in order. a missing constructor case and an unreachable row
  are errors.
- a pattern is `_`, a variable, a literal, or a constructor applied to
  sub-patterns in application order, as `n heir` or `head ‥ tail`. explicit
  sub-patterns fill explicit fields in order, `@p` filleth implicit fields, and
  omitted implicit fields are wildcards.
- a name whose visible binding is not a constructor bindeth a variable, so a
  local shadoweth a same-spelled constructor; qualification still reacheth
  it. a name two imports show is rejected only when one is a constructor.
- `ℕ` is an inductive family with constructors `0` and `heir`. a natural
  literal pattern `k` is `k` applications of `heir` to `0`, and literals stay
  the representation: kernel and runner read a literal as its constructor and
  build literals from `heir`. `ℤ` hath `overnaught: [ℕ, ℤ]` and
  `heir_undernaught: [ℕ, ℤ]`, `n heir_undernaught` being `-(n + 1)`, so `+3`
  is `3 overnaught` and `-4` is `3 heir_undernaught`. integer, string,
  unicode, and float literal patterns compile to the primitive `literal_case:
[@α: *, @β, x: α, k: α, yes: β, no: β, β]`, which chooseth once `x` and `k`
  are literals.

### scrutinees

- `match a, b { rows }` matcheth scrutinees in order. one that evaluateth to a
  neutral local is matched in place. one that evaluateth to a stuck
  computation, as `a ≤ a`, becometh a new input: each occurrence of its normal
  form in the expected type, up to universe levels, is replaced by it, so each
  row's goal nameth the row's constructor, as agda's `with` doth. instance
  goals with known class arguments are solved first, so a dictionary inside
  the scrutinee is compared. the match is then applied to the scrutinee.
- when no occurrence is found, the replaced type is ill-typed, or reinstating
  the scrutinee doth not restore the expected type, and for constructor and
  literal scrutinees, the scrutinee is bound first as a transparent local.
- abstracting a known descendant computation also abstracteth each applicable
  enclosing recursion's record: the fresh value `z` and records of types `R z`
  form a checked telescope applied to the original computation and records,
  so row goals and descendant evidence name the same value. a fresh neutral
  gaineth no evidence by its type alone.
- repeated occurrences of one neutral local share a column; their patterns are
  intersected, constructor fields included, distinct names keep bindings to
  the same values, and contradictory patterns make the row unreachable while
  keeping its position for redundancy checking. equal non-local expressions do
  not share columns.

### splitting

- the compiler splitteth the first column whose first row hath a constructor,
  applying the family's eliminator with a motive abstracting the split local
  from the expected type, so the result may depend on the matched value.
- a field fixed by an index split carrieth its known constructor shape and is
  decomposed, unless an enclosing recursion carrieth a memo record for it;
  such records stay on the eliminator path so every applicable record keepeth
  its descendants' evidence.
- a variable matched against a constructor case denoteth the rebuilt value.
  ordinary scrutinees still need coverage of their whole type, even when the
  expression is a known constructor.
- a match on one family of a mutual group supplieth its motive and methods to
  the joint eliminator, with constant motives `[goal, goal]` and identity
  methods for peers. peer hypotheses cannot justify a direct recursive call;
  course-of-values recursion supplieth joint record motives instead.
- an unindexed family reverteth the inputs whose types mention the matched
  value, so in `{yea, known ^ …}` against `[b: 𝟚, (x p) = b, …]` the yea
  branch seeth `known: (x p) = yea`.

### indexed matching

- an indexed family is matched when each index of the scrutinee's type is a
  distinct local. the motive abstracteth indices with the value, and each input
  whose type mentioneth them is reverted and rebound by name in each branch at
  that branch's indices.
- an index may be a constructor over distinct locals, as `n s` in
  `α vec (n s)` or `b ‥ empty` in `(a ‥ empty) = (b ‥ empty)`. the split then
  unifieth it with each constructor's index by large elimination, without the
  identity type: the motive matcheth fresh indices against the written ones
  and replaceth each written variable by the matching part. a constructor with
  a clashing constructor at some position is impossible: its method is
  trivial, its rows may be omitted, and a row naming it is redundant. `{}` is
  accepted when every constructor is impossible, so `[yea = nay, 𝟘] ≔ {}`
  holdeth.
- splitting an earlier index reverteth every later bound input whose domain
  dependeth on it, transitively in telescope order, and rebindeth them at the
  refined domains. named index inputs use their refined values' types. the
  trivial type is `[reverted goal, reverted goal]`, in the goal's universe.
- a constructor's result index may constrain its own fields: matching `cons`
  at `n heir` against index `2` forceth `n` to `1`, so the tail hath type
  `α vec 1`. the planner intersecteth shape requirements on each field without
  assigning locals or holes; each constrained field is split by its ordinary
  eliminator before later dependent fields and hypotheses are bound, and the
  method type computeth at the rebuilt field. written patterns see that value
  and index-variable names bind its parts. incompatible requirements reduce
  the motive to the trivial type, so their rows are unreachable.
- families destructured inside an index pattern must be unindexed. an
  undecidable index constructor, as a stuck call, is rejected, as is an index
  variable written twice or also among the parameters: unifying `a = a` would
  need axiom K, which tung leaveth unprovable.
- reverting an input also moveth its direct-child evidence and hypothesis
  level to the new binders, and applieth the substitution to accumulated row
  bindings, refined indices, carried descendant entries, and their records.
  visible local definitions mentioning a reverted input are rebuilt as checked
  lets, keeping names and shadowing; captured context slots are not
  overwritten. an indexed split carrying course-of-values records reverteth
  dependent inputs before binding its refined records; an unindexed one needeth
  no reversion.

### recursion

inside a recursive definition, a `match` on a named input rebindeth that name
to each step's value, and repeated named scrutinees intersect as ordinary
matches do. the compiler first trieth direct induction on each explicit input
of an inductive family, then course-of-values recursion on the same inputs,
indexed families and groups included. inputs the first row matcheth against a
constructor or literal come first, then the rest in order, so the case tree
splitteth where the first row sayeth: `{m, 0 ^ m, …}` maketh `x ∸ 0` reduce
to `x`. the first candidate whose branches and calls check is selected;
failed candidates restore inference state. calls resolve lexically and compare
normalised argument values with induction evidence, so aliases of descendants
are accepted and a shadowing variable is judged by its own value.

- implicit inputs before the structural input, and explicit inputs its type
  dependeth on, are fixed: calls pass fixed explicit inputs unchanged and
  supply no implicit arguments. implicit inputs after it are rejected.
- every other explicit input is rebound by the motive, so a call may pass any
  value for it, as an accumulator.
- a call supplieth the structural input, fixed explicit inputs, and explicit
  index leaf inputs, and may leave a trailing suffix of quantified inputs
  unapplied, yielding the checked hypothesis function at that descendant.
- `child f others` becometh the eliminator's hypothesis for `child` applied to
  `others`; a function child may be applied first, so `(x k) f others` useth
  the hypothesis of `k` at `x`. no fixpoint entereth the kernel.
- the runner useth call-by-need for arguments and fields, eliminator methods
  and hypotheses included: only the chosen method computeth, and a hypothesis
  computeth when first inspected.
- the passed value must be a proper descendant; the matched value or a rebuilt
  copy is rejected. the bare recursive name cannot be a value, and mutually
  recursive lets are rejected; explicit joint induction through `unbuild`
  remaineth.
- nested recursive definitions keep enclosing evidence. a local binder
  shadoweth a recursive name ordinarily; calls to an unshadowed enclosing
  function use its own evidence, and nested matches keep every applicable
  enclosing record.

indexed recursion: a recursive let may match an indexed value whose indices
are variables or constructor shapes over them. every variable leaf is a
distinct input bound before the structural input and unused by uniform
parameters; it is no pattern column, must be matched by a variable, and is
rebound in each branch to the matching index part. one motive builder
abstracteth the value and quantifieth other inputs for every candidate. the
result may depend on indices or the value. before using a child's hypothesis,
every actual child index is matched against the declaration's whole index
shape: explicit leaf arguments must equal their parts, and implicit leaf inputs
still need the shape to match. so a fixed `α vec 2` function cannot recurse on
its `α vec 1` tail, and one on `α vec (n heir)` may recurse on a tail of index
`k` only after a split establisheth `k = m heir`.
[`index_recursion.tung`](../byspel/index_recursion.tung) showeth fixed
indices, dependent results, and leaf inputs.

course-of-values recursion: a call on a deeper descendant, as
`(n heir) heir ^ ((n heir) fibonacci) + (n fibonacci)`, useth records like
lean's `brecOn`. joint large elimination buildeth a `below` type for every
target, specialised containers included, holding each recursive field's
`r{below, now}` record; the structural family's `now` is the result motive
and every other target's the empty record. each target's motive bindeth its
own index telescope, and each child's record useth the child's actual indices
then its value. joint induction buildeth the records; no kernel rule is added.

- a function field's record is pointwise: it keepeth the field's dependent
  input telescope and plicities, ending in the applied child's record. a known
  application prefix must match in full before the rest is applied. aliases
  keep evidence by normalised value; an unrelated or shadowing function gaineth
  none. this worketh through nested containers and mutual peers.
  [`function_recursion.tung`](../byspel/function_recursion.tung) showeth
  dependent function fields and partial calls.
- a nested split of a descendant generaliseth over its record, so deeper
  records name their fields' records. ordinary container matches keep their
  eliminators, and each record's target label selecteth the specialised
  constructor metadata, so a `rose list` head is a recursive rose although the
  list eliminator hath no hypothesis for it. a helper quantified over an
  ordinary container gaineth no evidence for its input.
- a call projecteth `now` from the record of the value it passeth, compared
  after normalisation; the record's target must be the structural family, so a
  peer's empty `now` cannot justify a call. the child's index shape must match
  as for direct induction. outside that shape a root record's `now` is the
  inhabited `[goal, goal]`, which never justifieth a call, while its `below`
  still keepeth descendants that may re-enter the shape.
  [`index_memo.tung`](../byspel/index_memo.tung) showeth indexed descendants
  and re-entry.

## fields and kernel records

[fields](language.md#fields) owneth the syntax; [`fields.tung`](../byspel/fields.tung)
useth plain, parameterised, chained, and dependent fields.

- after an unindexed one-constructor ilk is checked, each named explicit field
  becometh a hidden global `ilk.field`, the same checked core projection as a
  flock member, with implicit header parameters. earlier fields in its type
  become projections of the same value; constructor-local implicit fields keep
  their positions. `.` cannot occur in a source name, so only `value.field`
  reacheth it.
- `value.field` inferreth the value, readeth the ilk from its type's head, and
  applieth that accessor, solving parameters by unification; other values have
  no fields.
- types, goals, and audits display named projections recovered from the
  receiver's checked type, changing neither conversion nor checking.
- source hath no record syntax. the kernel keepeth closed records only for the
  `below` and `now` memos, and a family cannot occur inside a record field of
  its own constructor.

## modules

`ModuleId` and `SymbolId` keep nominal identity through aliases and
re-exports, so two imports of one identity do not conflict. interning
permitteth pointer comparison, with structural equality as fallback;
correctness never dependeth on sharing.
[development.md](development.md#projects-and-imports) owneth scheduling,
interfaces, and caching; the [language reference](language.md#files-and-modules)
owneth visibility and lookup.

## flocks and bizens

[flocks, bizens, and laws](language.md#flocks-bizens-and-laws) owneth the
syntax; [`flocks.tung`](../byspel/flocks.tung) showeth these rules.

### flocks

- a flock parameter is `name:type` without `@`; unnamed slots other than
  `@:parent` are rejected, and a flock needeth a member or a parent.
- a flock is a one-constructor family `name` over its parameters. its
  constructor `name_make` holdeth one implicit field per parent dictionary,
  then one explicit field per member in order; its eliminator is
  `unbuild name`.
- each member becometh a global accessor
  `member:[@parameters, @dictionary:(parameters name), type]`, a core
  projection `Field index dictionary` built from and checked against the
  constructor. it reduceth only on a constructor application and is otherwise
  a neutral `NField`, compared structurally. members are ordinary globals and
  cannot repeat another name.
- each parent becometh an inherited instance `name_parent_i` projecting the
  parent dictionary.
- member types use the ordinary elaborator; a law is a member whose type
  requireth an equality proof, as `[x:α, (x keep) = x]`, with no separate
  syntax tree. earlier members in its type refer to earlier fields, and
  patterns use an ordinary `match`. laws trigger no rewriting; their
  accessors supply proofs through a requirement.
- a constructor application checketh each law against its field type with the
  actual preceding fields, parent dictionaries included, substituted. `sorry`
  is accepted as for any term and reported for the bizen.
- `show flock` publisheth the family, constructor, eliminator, accessors, and
  parent instances, and carrieth the instance registry to importers.

### requirements and bizens

- `@:type` is an anonymous implicit slot of any product; when its type applieth
  a flock, an omitted argument is found by search. its names must already be
  in scope, and in a header it lowereth to a lambda before bare slots.
- a bizen's type is implicit slots ending in a flock application, or the
  application alone; explicit slots are rejected.
- `bizen:type { let member ≔ body … }` lowereth members to local bindings and
  a dictionary constructor application. each member and law is supplied once;
  missing, repeated, and unknown members are rejected.
- flock order fixeth checking and scope. expected field types supply omitted
  annotations, and written ones are ascriptions that must agree. later fields
  see earlier values, type fields included.
- a member's own right-hand side nameth its global accessor; earlier members
  are lexical bindings, with no global-then-sibling retry. a call for another
  carrier may qualify the accessor. recursive methods use recursive helpers.
- parent dictionaries are implicit fields. search findeth requirements or
  registered instances by class identity before supplied ancestor members build
  a missing parent inline under the same rules; an existing parent keepeth
  precedence even when another flock hath same-spelled members.
- the head fixeth constructor parameters before members are checked, so case
  functions receive expected types. the dictionary is registered only after
  its whole term checketh; there is no kernel rule.
- a bizen is a global `#instance_n`, unnameable in source. every bizen is
  registered whether or not its flock is shown, and importers see it wherever
  the flock is visible.

### instance search

- an omitted implicit argument whose type applieth a flock is a goal, solved
  after the declaration's unification and before the kernel check. a supplied
  `@` argument bypasseth search.
- an annotation is closed, so its goals are settled before the body: goals
  with known input heads are solved, and stuck equations are split by
  first-order approximation, against a rigid application and then between two
  applied holes. a body thus matcheth against computing members, as in
  `((l sift p) sift p) = (l sift p)`. fallback bizens wait for the whole
  declaration.
- a goal waiteth while any input parameter's head is unknown, as rocq's `!`
  mode; `* out` parameters are outputs search findeth, as lean's `outParam`.
  a waiting goal may still be solved by local requirements and their parents.
  when nothing else progresseth, a stuck equation is split (see the
  [inference boundary](#inference-boundary)), its parts at once again, so
  `?φ ?a x = ∏ α x` reacheth `?φ = ∏`. last come the flock's fallback bizens,
  as lean's default instances; a goal still unknown asketh for an annotation.
- search trieth local dictionaries, innermost first, then registered bizens,
  then inherited instances; a later tier runneth only when no earlier candidate
  matcheth, so a direct bizen outranketh a parent path. inherited paths are
  not ranked by length, and the first successful one is chosen without
  comparing parent dictionaries.
- registered bizens go by priority, higher first, then latest first, as lean
  doth; the first match with its requirements solved winneth, so overlap is
  never ambiguous. equivalent instance patterns are rejected at registration.
  failure reporteth the goal, local requirements, and a rejected candidate's
  reason when known.
- a candidate's requirements are solved recursively to depth 16, and a goal
  repeating an ancestor faileth. a requirement with unknown inputs is first
  fixed by the one unifying local requirement of its flock, as a parent
  projection from `ρ module μ` to `μ group_+` findeth its ring. otherwise it
  waiteth only under the outermost goal's candidate; nested, the candidate
  faileth, since waiting would commit search to an unchecked path.
- instance patterns and cycle keys compare global identities without universe
  instantiations; sort arguments stay significant and the kernel still
  checketh universes.
- candidates are filtered first: a bizen whose flock arguments start with
  another family cannot match, and an inherited instance is tried only when
  its child flock hath a local requirement or bizen with those heads.
- the compiler defineth no bizens; every bizen, each fallback included, is
  library or program code.

## ordinary lists

[`list_family.tung`](../byspel/list_family.tung) useth one
universe-polymorphic list at value and type levels. lists may index families
and compare by ordinary conversion; no native type-level list, element-kind
rule, or implicit import is needed. concatenation recurseth on its left input,
so `xs · ∅` stayeth neutral while `xs` is unknown and right identity needeth
induction; conversion addeth no rewrite for it and inferreth no splits.

## deeds and host bindings

[`deed_loop.tung`](../byspel/deed_loop.tung) showeth host bindings, bounded
repetition, and a deed loop; [`host_tales.tung`](../byspel/host_tales.tung)
bindeth pure operations and [`host_deeds.tung`](../byspel/host_deeds.tung)
useth files, tasks, and strings.

normalisation and execution share one catalogue, `hostBindings` in
`Tung.Primitive`, and one failure convention: a fallible operation returneth
`maybe` or `string ∑ α`. bookhoard declareth every key, with its signature, in
`_fremmed.tung` and the `deed/` modules.

`let name:type ≔ 'key' fremmed`, at top level, bindeth one trusted host
constant. the kernel checketh the required annotation, then
`Tung.Dependent.Host` matcheth its normalised type against the catalogued
signature: implicit type inputs, explicit inputs the result doth not depend
on, and the result; universe levels are not compared. the program chooseth
every name.

- each key is bound at most once. unknown keys, different types, local
  bindings, and missing annotations are rejected.
- primitive types match by name. a host data type, such as `𝟙`, `𝟚`,
  `maybe`, `∏`, `∑`, `list`, `wordbook`, `_process_outcome`, `_request`, or
  `_response`, matcheth only the `ilk` of that name in its bookhoard file, as
  `ilk/maybe.tung`; a lookalike elsewhere differeth.
- the catalogue fixeth each data family's parameters, constructor identities,
  and field types, including families used by fields. a canonical path alone
  justifieth nothing; empty, renamed, indexed, or retyped replacements are
  rejected.
- `deed` and `task` are opaque primitive families of kind `[*, *]` at each
  universe, without constructors or eliminators; `ilk/task.tung` re-exporteth
  the native task, and an ordinary `ilk task` cannot stand for it.
- primitive value types live in the base universe without universe
  parameters. a literal inhabiteth its kind's primitive type: `'x'` string,
  `42` ℕ, `+42` and `-7` ℤ, `1.5` float, `` `a `` unicode. integers always
  carry a sign; unsigned digits are naturals. equal literals convert, and
  floats compare by bit pattern, so a NaN literal equaleth itself.
- a pure operation computeth during checking when every input is a literal or
  a list of literals, so `+2 + +2` converteth with `+4`. otherwise a binding
  with a model unfoldeth it, glued so goals show the name, and one without
  stayeth neutral. results are built at the catalogued type, so a comparison
  yieldeth `yea` or `nay` and a partial operation `none` or `x some`.
  `pureOperation` in `Tung.Primitive` defineth these once for kernel and
  runner, and normalisation keepeth the actual result family's universe and
  type arguments, nested ones included.
- the model is the body after `fremmed`, checked as a let of the binding's
  name against its checked type, so a self-call is structural recursion, and
  stored as the hidden global `model name`, shown as `name`. that type's
  universe parameters stay rigid, so the model shareth them even with several
  universe-polymorphic families, as `(ℕ ∏ ℕ) maybe`. the model must be
  transparent with the binding's universe parameters and normalised type, and
  only pure operations may have one. bookhoard tests compare each model with
  its native operation on generated literals; the kernel trusteth that
  agreement as it trusteth the native operation.
- deed constants never reduce in checking: `x deed_sheer deed_bind f` doth not
  convert with `x f`.
- a `fast` declaration is a kernel `Fixpoint`, which conversion never
  unfoldeth, so normalisation terminateth. its signature is elaborated and
  generalised first; the body is checked against it with the declaration's
  name bound to the signature's rigid universe parameters, as a host model
  nameth its binding. universe parameters that instance search addeth after
  those are passed on unchanged by every self-call. the kernel rechecketh the
  body with the fixpoint in scope, then counteth the inputs before the deed in
  the normalised ilk and rejecteth an ilk that endeth otherwise. it is sound
  because the standard model readeth every deed type, and so every function
  into one, as a one-element set. fast declarations are the only unbounded
  execution; bounded repetition useth induction.
- the standard model readeth primitive types as their runtime sets, pure
  operations as their total definitions, and deed types as one-element sets,
  given the checked schemas and catalogued operations. it addeth no inhabitant
  of `𝟘`, `sorry` excepted; no constant extracteth `α` from `α deed`, and
  positivity rejecteth a family hidden in a deed argument.
- evaluation eraseth types and universe levels; [deeds](language.md#deeds) and
  [running](language.md#running) state the runner's rules.

## proof construction

`is.tung` defineth identity as an ordinary indexed family; `throughbear`,
`leibnitz`, and `throughgo` prove substitution and composition without kernel
rules. `inlook` passeth a matched value and its branch equation to a case
function; a constant result family may need a written motive. function
extensionality is the orsetting `fall_umfang`.

well-founded recursion is library code in
[`ilk/grounded.tung`](../bookhoard/ilk/grounded.tung):
`wellgrounded_selfcall` recurseth structurally on groundedness evidence, and
`wellgrounded_selfcall_by` taketh a result motive `[α, *]` and a measure
`[α, μ]`, its callback requiring a proof that the new measure is smaller.
identity elimination keepeth computed measures usable after a match without
axiom K. dependent inputs may be packed in a one-constructor type, or stay
curried in the motive when the measure ignoreth them.
[`wellgrounded.tung`](../byspel/wellgrounded.tung) showeth it; no
measured-recursion rule is added.

the [bookhoard guide](../bookhoard/reference.md#law-proofs) owneth library
proof coverage, [proof checking](language.md#proof-checking) its output, and
the [logical boundary](#logical-boundary) its trust.
