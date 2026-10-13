# dependent tung design

audience: agents. purpose: how the checker realiseth the language: the dependent
core, elaboration, pattern compilation, instance search, and logical boundary.
each section stateth its algorithm, rejection cases, and limits.
[`language.md`](language.md) owneth what a program author writeth and observeth:
syntax, names, libraries, the runner, and command-line output. this document
linketh to it rather than restating those rules. [`todo.md`](../todo.md)
tracketh remaining work.

## implemented core

`Tung.Dependent` provideth a checked dependent lambda calculus.
`Tung.Dependent.Source` elaborateth source programs as described below.

- one `Term` representeth universes, dependent products, annotated lambdas,
  applications, local bindings, and global definitions.
- local variables use de bruijn indices. semantic neutrals use stable levels.
- `Sort u` hath type `Sort (u + 1)`. a product whose domain and codomain inhabit
  `Sort u` and `Sort v` inhabiteth `Sort (max u v)`.
- conversion useth beta reduction, local substitution, transparent definitions,
  eta conversion for functions, and exact universe equality. there is no
  cumulative subtyping.
- evaluation is glued: a transparent global applied to its arguments stayeth
  folded, with its unfolding computed only when a value is forced. every
  public evaluation result is forced at its head, except an application's
  argument, whose worth only instantiateth the codomain and stayeth folded;
  so checking `t greatness` doth not compute a closed `t`. conversion accepteth
  identical folded terms by reflexivity, retaining all universe arguments.
  other comparisons unfold both normal forms. folding changeth no equality.
  motives keep definitions folded without forcing their bodies;
  display quotation unfoldeth a
  definition only when that reacheth a constructor, literal, record, or
  variable; a stuck elimination equal to an enclosing definition applied to
  the eliminated child is shown as that application.
- universe levels are never written. source hath no level syntax, and every
  universe constraint is inferred; a program that needeth a level relation
  inference cannot find is rejected.
- inference solveth direct universe-hole equations. remaining holes become
  universe parameters qualified by their constraints. maximum constraints
  retain their alternatives; inference never guesseth one branch.
  generalisation discardeth tautological constraints with the same canonical
  atom comparison as constraint insertion.
- each global application instantiateth and checketh exported universe
  constraints. a declaration's obligations share the prepared assumption
  clauses and atom set. each conclusion clause is proved when every alternative
  of one assumption clause hath a weaker counterpart in it. uncovered clauses
  use the exact solver on their negation. this preserveth disjunctions and both
  directions of equality. the exact solver useth difference constraints and
  negative-cycle detection. adding an
  edge starteth bellman-ford from the existing feasible assignment rather than
  resetting every distance to zero.
  before branching, it accepteth an assignment that satisfieth every remaining
  clause. it rejecteth a maximum clause when every alternative contradicteth
  the current fixed graph. a clause satisfied by the current assignment
  needeth no further graph pass. every surviving alternative remaineth
  available; maximum constraints can still require exponential search.
- the kernel rechecketh generalised terms with rigid parameters and proveth every
  generated universe obligation from the declared assumptions.
- inconsistent universe constraints are rejected before normalisation proceeds.
  the checker keepeth an assignment that satisfieth the constraints so far; a new
  constraint that it satisfieth is accepted at once, and only one that it
  violateth re-solveth the whole set.
  public normalisation first checketh its input. raw NBE remaineth private.
- only checked, closed declarations enter the environment. transparent globals
  are ordered and cannot reference themselves. inductive families, constructors,
  and generated eliminators are checked and inserted together. there is no
  general recursion. named assumptions and trusted host constants extend the
  axiom-free fragment under the [logical boundary](#logical-boundary); host
  constants enter only through the catalogue described under
  [deeds and host bindings](#deeds-and-host-bindings).

the api exposeth `infer`, `check`, `define`, `validate`, and `normalise`.
`defineInductive` checketh rigid declarations; `inferInductive` generaliseth valid
universe constraints before the same check. `defineInductives` and
`inferInductives` check mutual groups through the same builder.
explicit and implicit applications retain their visibility; insertion of
omitted source arguments belongeth to elaboration. runtime erasure is separate.

the dependent-product rules follow
[lambda pi](https://www.andres-loeh.de/LambdaPi/). inductive declarations use
generated dependent eliminators, following the
[lean inductive rules](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/).

### logical boundary

the pure core is a fragment of predicative intensional dependent type theory,
with universe polymorphism, strictly positive inductive families, and closed
records. `Sort 0` is an ordinary data universe, not an impredicative `Prop`.
universe inference doth not permit `Sort u : Sort u`. recursion is expressed
through checked eliminators; runtime deed loops do not reduce in conversion.

the source language also provideth `sorry: [@α: *, α]`. this assumption can
inhabit an empty type, so the language with unrestricted `sorry` is logically
inconsistent as a proof system. a runtime failure doth not repair that logical
fact. type checking accepteth terms under this assumption; the
[runtime boundary](language.md#runtime-boundary) defineth how `--check`
reporteth it and how `--no-sorry` rejecteth it. a host binding is trusted as a
program; ordinary `--check` doth not report it. an `orsetting` declaration is a
named axiom, a constant with a checked type and no body: a consistent proof may
rely on the `orsetting` assumptions it lists, but not on `sorry`.

theorem-specific checking traverseth checked types and bodies across imports,
including selected dictionaries, host models, and inductive metadata and
computation rules. elaboration also retaineth resolved input references before
normalisation can erase them. declaration insertion storeth these references,
and imports and cached interfaces preserve them. rejected speculative trials
discard their references with their inference state.

the audit reporteth reachable named axioms, `sorry`, and host
constants. this is a conservative syntactic closure: a referenced dictionary
retaineth all its fields, and a referenced inductive family retaineth its whole
checked group, including the group's input references. unused imported
declarations are excluded. no extra normalisation or source-name search
decideth dependencies.

the report describeth assumptions relative to the checked kernel and host
catalogue; it is not a separate proof of their correctness. a modelled host
operation remaineth a trust dependency, since agreement between its native
implementation and its model is trusted. the
[language rules](language.md#proof-checking) specify selection and axiom policy.
the [lean axiom boundary](https://lean-lang.org/doc/reference/latest/Axioms/#consistency)
describeth the same distinction between checking a term and justifying its
assumptions.

the intended consistency argument for terms without `sorry` requireth correct
kernel rules, universe entailment, inductive generation, conversion, and
trusted host operations. host data schemas are checked at binding boundaries.
interfaces are trusted compiler output reused under source, import, and build
keys; loading checketh the format and reference metadata, without repeating
kernel checking. regression tests exercise these rules; they are not a
machine-checked proof of consistency or subject reduction.

## implemented source

- annotations and bodies use one expression parser and lexical namespace.
- module definitions resolve to `SymbolId` in dependency order, so source
  order doth not matter. a declaration that useth a flock member waiteth for
  the module's bizens of that flock, except one that itself needeth the
  declaration by name. local bindings
  are sequential and shadow visible names. unknown names are errors. types, flocks, constructors, flock
  members, and lets share one namespace: a module that declareth a top-level
  name twice, such as a flock and its member or an ilk and its constructor,
  is rejected with `top-level name repeateth`.
- a let whose body hath a free reference to its own name is recursive, unless
  a binding of that name is already visible, such as an import or an outer
  local, including an active enclosing recursive binding; then the reference
  denoteth that binding. a header, lambda, product,
  case variable, or local let may bind the same spelling without making the
  enclosing let recursive. binder annotations and local initialisers see
  only earlier bindings. a recursive let needeth an annotation; an ascribed
  body, `let f ≔ (body: type)`, counteth as one.
- no let is generalised over its holes. after elaboration and instance
  search, an open term hole or a waiting bizen requirement is an error
  asking for the polymorphic parameters or an annotation.
- each surface `*` and each global universe argument receiveth a fresh level
  hole. definitions generalise valid universe constraints.
- bracket binders scope over later domains and results. bare and `_` slots
  increase binder depth without introducing a name.
- named header slots and `@:` requirements lower to lambdas. they precede
  bare slots. a header slot may also bind a pattern, `a both b: α ∏ β`; the
  lambda bindeth a hidden local and the body matcheth it. a bracket whose last
  slot bindeth, as in `let f: [x:] ≔ x`, leaveth its result to inference.
- `{}` is the case function on an empty family, and `match x {}` matcheth a
  value of one. before a match decideth that no constructor fiteth, instance
  goals whose flock arguments are known are solved, so an impossible case
  seeth the selected dictionary's operations compute.
- primitive names from the
  [language reference](language.md#declarations-and-types) are visible in every
  module. an imported or local name of the same spelling shadoweth them.
  `=` and `eftbend` come from the ordinary library module `is.tung`.
  anonymous `{x ^ body}` lambdas need constraints or a function annotation.
  typed binders such as `{x:* ^ x}` can infer their function type.
- applications, `(expression:type)`, and `(let ... yield expression)` use the
  same expressions for types and values.
- `<{f, a, b, c}` and `>{f, a, b, c}` associate ordinary binary applications
  to the left and right. they have no dedicated list representation.
- supplied `@` arguments may be types or values. the checked product spine
  consumeth implicit and explicit arguments in declaration order.
- omitted arguments become typed contextual holes. arguments and expected
  types determine their solutions. unused holes are errors, never defaults.
- arguments are checked in order, except a case function `{rows}` whose
  input type is still a hole. a hole standeth for it, the later arguments are
  checked, and the case function is then checked against its fixed type and
  fills that hole. so `{ empty ^ 𝟘, _ ‥ _ ^ 𝟙 } throughbear p only` learneth its
  input type from `p`. a lambda whose body matcheth inside a larger
  expression is not postponed and needeth a binder annotation.
- an expected implicit product introduceth its binders before any expression
  that doth not bind them itself, as in agda, so a polymorphic name meeteth a
  polymorphic type. a polymorphic value checked against any other type,
  including an unknown one, is specialised.
- an ascription with holes first learneth from the expected type, then checketh
  its body. a header that bindeth its own implicit slots, as a local function's
  `[@α:, a:, f:] ≔ …`, is unified with the expected type first; when they
  agree, the body is checked against the expected type, so slots written
  without types have known types. otherwise the body is checked against the
  written type and then specialised.
- unannotated lambda domains can be inferred when constraints determine them.
  unresolved domains never introduce unwritten polymorphic parameters.
- every completed definition and expression is rechecked by the core kernel
  before insertion or public normalisation.
- argument visibility and runtime relevance are separate. types are erased;
  implicit values and dictionaries may remain at runtime.

- `fall slots, result ^ body` elaborateth exactly as
  `({binders ^ body} : [slots, result])`
  ([syntax](language.md#let-declarations)).

`compileSnapshot`, `compileImports`, `inferSourceExpression`, and
`normaliseSourceExpression` are the library api.

### inductive declarations and proofs

```tung
ilk ℕ: * {
  naught: ℕ,
  heir: [ℕ, ℕ]
}

let rebuild: [x: ℕ, ℕ] ≔
  {_: ℕ ^ ℕ} unbuild ℕ naught {n, ih ^ ih heir} x

ilk sameness: [α: *, x: α, α, *] {
  refl: α sameness x x
}

let throughbear: [@α: *, @x: α, @y: α, proof: α sameness x y,
  family: [α, *], worth: x family, y family] ≔
  {z, _ ^ z family} unbuild sameness @α @x worth y proof
```

- `ilk name:signature { ... }` declareth one family. constructors share the
  ordinary namespace. the generated eliminator is not a name: `unbuild name`
  denoteth it, with `name` resolved as a family. a name that resolveth to
  anything but an ilk or flock is rejected.
- a dependency cycle containing only `ilk` declarations formeth one mutual
  group, ordered by the families' source positions. no grouping keyword is
  needed. a cycle containing any other declaration is rejected; this rule
  doth not permit mutually recursive lets or import cycles. a group's
  signatures are checked before its families enter the environment, so a
  signature cannot depend on a group member. names and constructors are
  inserted atomically only after the complete group checketh.
- the named prefix of the outer bracket declareth uniform parameters. later
  bare slots and a nested result product declare indices. only uniform
  parameters scope over constructor annotations. inherited constructor and
  eliminator parameters are implicit, regardless of family argument visibility.
- mutual families share one parameter telescope: parameter counts and
  visibility agree, and domains are definitionally equal after renaming
  bound parameter names. their result universes are equal. their own index
  telescopes may differ. signatures and constructors are generalised jointly;
  every peer occurrence useth the group's canonical universe vector, and
  the whole group exporteth its shared constraints.
- every constructor stateth its type, as in a GADT; a constructor without one is
  rejected. constructors require a saturated result of their family with
  unchanged parameters. constructor fields must fit within the family's
  universe.
- a recursive field is any family in the group or a function ending in one,
  such as `[ξ, φ freer α]`, whose inputs mention no group family: each occurreth
  strictly positively. normalisation exposeth aliases before checking
  occurrences. recursive occurrences must supply every parameter and index;
  shared parameters stay unchanged. negative occurrences and group families
  inside their own arguments are rejected. nested occurrences use the
  checked specialisation described below.
- `unbuild name` taketh the implicit parameters, a motive, one method per
  constructor in declaration order, the indices, and the value. the motive
  taketh the indices and value and returneth a type. each recursive field is
  followed by its induction hypothesis in that constructor's method; for a
  function field `k` the hypothesis is `[inputs, motive (inputs k)]`.
- in a mutual group, `unbuild name` instead taketh the shared implicit
  parameters, one motive per family in group order, and all constructor
  methods in group order and then written constructor order. the requested
  family's own indices and value follow. each recursive field's hypothesis
  useth the motive of that field's family. each motive hath its own result
  universe, so every group eliminator's universe vector containeth the
  shared declaration parameters followed by one universe per motive.
- a nested field may apply an already checked, unindexed inductive container
  to group families, as `rose list` or `(rose list) list`. transparent aliases
  are normalised first. specialisation arguments depend only on shared uniform
  parameters; they cannot mention constructor fields or function inputs.
  group-family parameters remain unchanged. each specialised container's
  result universe equaleth the group's result universe. abstract container
  heads and indexed containers are rejected.
- nested induction is a native kernel extension certified by translation.
  original constructor signatures are checked before specialisation, including
  phantom parameters. a finite worklist cloneth each specialised container's
  ordinary family peers and constructors under the shared parameter telescope.
  the ordinary mutual checker certifieth the entire translated group, so a
  negative container parameter faileth the same strict-positivity rule. positive
  function fields retain their pointwise hypotheses. later dependent fields
  must type-check under that uniform translation; there is no rewrite for a
  particular container operation.
- restoration replaceth temporary family and constructor applications by their
  original container applications. private, checked transparent aliases label
  the specialised elimination targets; they introduce no nominal type or new
  conversion rule. public field types, constructor identities, and container
  operations remain ordinary. temporary constructor definitions are discarded.
  restored signatures, alias bodies, and every computation-rule right side are
  independently rechecked with the new recursors opaque. typing the rules alone
  would not justify termination: the mutual positivity certificate is required.
- a nested `unbuild` taketh the root motives first, then the specialised
  container motives, then all methods in that same target order. roots follow
  source order. targets follow first occurrence in normalised constructor
  signatures, with ordinary container peers added together; the worklist then
  closeth over their fields in order. repeated specialisations share one target.
  each target dispatcheth its own constructor rules, even when several targets
  use the same original container constructors. ordinary matching supplieth
  trivial motives and methods for these auxiliary targets.
- native and nested induction use one checked core term per constructor rule,
  scoped over shared parameters, motives, methods, and actual fields. the type
  normaliser and erased runner evaluate these same terms; neither reconstructeth
  recursive hypotheses from metadata. recursive field metadata nameth its
  target explicitly, because an ordinary container head alone cannot identify
  its specialisation.
- induction computeth on constructors and remaineth neutral on variables.
  recursion thus descendeth through constructor children. arbitrary recursive
  `let` definitions remain errors. source patterns compile to the eliminators
  described below.
- the identity family above provideth intensional equality and path induction.
  `throughbear` computeth to its supplied value on `refl`. there is no equality
  reflection or proof irrelevance. `sorry` remaineth the assumption described
  under the [logical boundary](#logical-boundary).

### pattern matching and recursion

[`match.tung`](../byspel/match.tung) showeth case
functions, `match`, nested patterns, and structural recursion.

- `{p, q ^ body, ...}` is a case function with one column per pattern. one
  row of plain binders remaineth an ordinary lambda. a row whose binder nameth
  a constructor is a pattern row. leading implicit binders stay named lambda
  binders; only the explicit binders after them form the row, so a header slot
  named by a constructor, as `eftbend:a = b`, matcheth its input.
- `match a, b { rows }` matcheth scrutinees in order. a scrutinee that
  evaluateth to a neutral local is matched in place. a scrutinee that
  evaluateth to a stuck computation, such as `a ≤ a`, becometh a new input:
  each occurrence of its normal form in the expected type, up to universe
  levels, is replaced by that input, so each row's goal mentioneth the row's
  constructor, as agda's `with` doth. instance goals whose class argument is
  known are solved first, so a dictionary inside the scrutinee is compared.
  the match is then applied to the scrutinee. when no occurrence is found, the
  replaced type is ill-typed, or reinstating the scrutinee doth not give back
  the expected type, and for constructor and literal scrutinees, the
  scrutinee is bound first as a transparent local. repeated occurrences of the same neutral local share one column.
  their patterns are intersected, including constructor fields. distinct
  pattern names retain bindings to the same values. contradictory patterns
  make the written row unreachable; its original position is retained for
  redundancy checking. arbitrary equal non-local expressions do not share
  columns.
- abstracting a known descendant computation also abstracteth each applicable
  enclosing recursion's record. the fresh value `z` and records of types
  `R z` form a checked telescope, applied to the original computation and
  its records. dependent row goals and descendant evidence therefore refer
  to the same value; a fresh neutral doth not acquire evidence by its type alone.
- every row hath the same number of patterns. a match hath one pattern per
  scrutinee, including inside a recursive definition. written rows are
  validated before recursive clause collection projecteth their columns.
  every constructor's written arguments are checked and aligned before
  intersection. a name cannot be bound twice in one written row. a name
  repeated in a lambda row or in one let bracket becometh a pattern, so a
  constructor such as `eftbend` may repeat, while a repeated variable is
  rejected by this rule.
- rows are tried in order.
- a name in a pattern that two imports show is rejected only when one of
  them is a constructor; otherwise it bindeth a variable.
- a pattern is `_`, a variable, a literal, or a constructor applied to
  sub-patterns in ordinary application order, such as `n heir` or
  `head ‥ tail`. `ℕ` is an inductive family with constructors `0` and
  `heir` and eliminator `unbuild ℕ`; a natural literal pattern `k` is `k`
  applications of `heir` to `0`, and literals stay the representation: the
  kernel and the runner read a literal as its constructor and build a literal
  from `heir`. `ℤ` is likewise an inductive family with constructors
  `overnaught: [ℕ, ℤ]` and `heir_undernaught: [ℕ, ℤ]`, where
  `n heir_undernaught` is `-(n + 1)`, so each integer hath one form; the
  kernel and runner read `+3` as `3 overnaught` and `-4` as
  `3 heir_undernaught`, and build a literal from either constructor. an
  integer, string, unicode, or float literal pattern
  compileth to the primitive `literal_case` of type
  `[@α: *, @β, x: α, k: α, yes: β, no: β, β]`, which chooseth `yes` or `no`
  once `x` and `k` are literals.
  explicit sub-patterns fill explicit fields in order; `@p` fills implicit
  fields; omitted implicit fields are wildcards. a name whose visible
  binding is not a constructor bindeth a variable, so a local value shadoweth
  a constructor of the same spelling; a qualified name still reacheth it.
- a case function needeth an expected type; an unannotated case function is
  rejected. a `match` without one inferreth a single result type for every
  row.
- the compiler splitteth the first column whose first row hath a constructor.
  each split applieth the family's eliminator. its motive abstracteth the split
  local from the expected type, so the result type may depend on the matched
  value. a field determined by an index split carrieth its known constructor
  shape and is decomposed into its fields, unless an enclosing recursion
  carrieth a memo record for it. such records stay on the eliminator path, where every
  applicable record retaineth its descendants' evidence. a variable matched
  against a constructor case denoteth the rebuilt constructor value.
  ordinary scrutinees still require coverage of their whole input type, even
  when the supplied expression is a known constructor.
- a match on one mutual family supplieth its chosen motive and methods to
  the joint eliminator. peer families receive constant inhabited motives
  `[goal, goal]` and identity methods. these peer hypotheses cannot justify a
  direct recursive call on a value of the chosen family. course-of-values
  recursion instead supplieth the joint record motives described below.
- a missing constructor case and a row that no input can reach are errors.
- an indexed family is matched when each index of the scrutinee's type is a
  distinct local variable. the motive abstracteth the indices with the value, and
  each input whose type mentioneth them is reverted into the motive and rebound
  under its name in each branch, at the type that branch's indices give it.
- an index may also be a constructor applied to distinct local variables,
  as `n s` in `α vec (n s)` or `b ‥ empty` in `(a ‥ empty) = (b ‥ empty)`.
  the split then unifieth it with each constructor's index by large
  elimination, without the identity type: the motive matcheth fresh indices
  against the written ones and giveth the goal with each written variable
  replaced by the matching part of the constructor's index. a constructor
  whose index hath a different constructor at some position is impossible:
  its method is trivial, its rows may be omitted, and a row naming it is
  redundant. `{}` is accepted when every constructor is impossible, so
  `[yea = nay, 𝟘] ≔ {}` holdeth.
- splitting an earlier index also reverteth every later bound input whose
  domain dependeth on it, transitively and in telescope order. those inputs
  are rebound at each constructor's refined domains before matching
  continueth. named index inputs use their refined values' types. the trivial
  type is `[reverted goal, reverted goal]`, so impossible methods inhabit the
  same universe as the goal with its reverted inputs.
- a constructor's result index may constrain its own fields. matching
  `cons` at `n heir` against a value of index `2` forceth `n` to `1`, and a
  later tail field hath type `α vec 1`. the index planner intersecteth
  constructor-shape requirements on each field without assigning local
  variables or inference holes. each constrained field is split by its ordinary
  eliminator before its later dependent fields and induction hypothesis are
  bound. the remaining method type then computeth at the rebuilt field, so
  dependent domains refine by computation. written field patterns see that
  rebuilt value, and written index-variable names bind its matching parts.
  incompatible field requirements still need these eliminations to compute
  their motive to the trivial type; their rows are unreachable.
- every family destructured inside an index pattern must have no indices of
  its own. an index whose constructor cannot be decided, such as a stuck
  function call, is rejected, as is a written index variable that appeareth
  twice or in the family's parameters: unifying `a = a` would need axiom K,
  which tung leaveth unprovable.
- a recursive let may match an indexed value whose indices are variables or
  constructor shapes over variables. every variable leaf must be a distinct
  input bound before the structural input and unused by uniform parameters.
  a leaf input is not a pattern column: it must be matched by a variable,
  and each branch rebindeth its name to the matching part of the constructor's
  index. one motive builder abstracteth the value and quantifieth other
  inputs for every recursive candidate. bare variable indices need no
  eliminations; constructor shapes use the same large elimination as ordinary
  indexed matching. the result may depend on the indices or matched value.
- before using a recursive child's hypothesis, the compiler matcheth every
  actual child index against the declaration's whole index shape. explicit
  leaf arguments must equal their corresponding matched parts; implicit
  leaf inputs still require the whole shape to match. a fixed `α vec 2` function
  cannot call itself on its `α vec 1` tail. a function on `α vec (n heir)`
  may call itself on a tail of index `k` only after a split establisheth
  `k = m heir`; a stuck variable doth not promise that later split.
  [`index_recursion.tung`](../byspel/index_recursion.tung)
  showeth fixed indices, dependent results, and explicit leaf inputs.
- reverting a dependent input also moveth its direct-child evidence and
  induction-hypothesis level to the new binders. accumulated row bindings'
  values and types receive the same substitution, including refined indices.
  visible local definitions that mention a reverted input are rebuilt as
  checked lets under the substitution, preserving their names and lexical
  shadowing. captured context slots are not overwritten. carried descendant
  entries and their record locals receive the same substitution.
- a family without indices reverteth the inputs
  whose types mention the matched value in the same way, so in
  `{yea, known ^ ...}` against `[b: 𝟚, (x p) = b, ...]` the yea branch seeth
  `known: (x p) = yea`. an indexed split that carrieth course-of-values
  records reverteth dependent inputs before binding its refined records.
  an unindexed split with carried records needeth no dependent-input reversion.
  a header slot is a parameter only while every
  constructor's written result passeth it unchanged; the slots after it are
  indices, as in `ilk tag: [a: *, *] { integer: [ℤ, ℤ tag] }`.

a `let` whose body freely nameth itself is recursive. it needeth an annotation.
inside a recursive definition, a `match` on a named input rebindeth that name
to the value matched at each step. repeated named scrutinees use the same
pattern intersection as ordinary matches.

the compiler first trieth direct induction on each explicit input of an
inductive family, subject to the indexed-input rules above. the inputs that
the first row matcheth against a constructor or literal come first, then the
rest in input order, so the case tree splitteth where the first row sayeth:
`{m, 0 ^ m, …}` maketh `x ∸ 0` reduce to `x` for any `x`. if none succeedeth,
it trieth course-of-values recursion on those inputs in the same order, including indexed families and groups. the first candidate
whose branches and recursive calls check is selected. failed candidates restore
inference state. recursive calls use ordinary lexical resolution and compare
normalised argument values with induction evidence; aliases of descendants
are accepted, and a shadowing variable is checked by its own value.

- implicit inputs before the structural input, and explicit inputs its type
  dependeth on, are fixed. recursive calls must pass fixed explicit inputs
  unchanged and cannot supply implicit arguments.
- implicit inputs after the chosen structural input are rejected. a recursive
  call must supply its structural input, fixed explicit inputs, and explicit
  index leaf inputs. it may leave a trailing suffix of quantified inputs
  unapplied; the result is the corresponding checked hypothesis function,
  specialised to that descendant.
- every other explicit input is rebound by the motive. recursive calls may
  pass any value for it, as an accumulator doth.
- a call `child f others` becometh the eliminator's induction hypothesis for
  `child`, applied to the other inputs. a function child may be applied first:
  `(x k) f others` useth the hypothesis of `k` at `x`. no fixpoint entereth the
  kernel. the runner useth call-by-need for all arguments and fields, including
  eliminator methods and recursive hypotheses. an eliminator computeth only
  the chosen method, and a hypothesis computeth when first inspected. arms that
  each recurse do not compute every arm's call.
- a call on a deeper descendant, such as the row
  `(n heir) heir ^ ((n heir) fibonacci) + (n fibonacci)`, useth
  course-of-values recursion like lean's
  `brecOn`. joint large elimination buildeth a `below` type for every target
  in the group, including specialised containers. its record holdeth each
  recursive field's own `r{below, now}` record. the chosen
  structural family's `now` type is the result motive; every other target's
  `now` type is the empty record type. each target's motive bindeth its own
  index telescope, including dependent domains and implicit indices. each
  child's record useth that child's actual indices, followed by its value.
  joint induction then buildeth those records. no new kernel rule is needed.
- a function field's record is pointwise: it retaineth the field's checked
  dependent input telescope and plicities, ending in the record of the
  applied child. a known application prefix must match in full before its
  remaining arguments are applied to the record. aliases retain evidence
  by their normalised values; an unrelated or shadowing function doth not
  acquire it. this worketh through nested containers and mutual peers too.
  [`function_recursion.tung`](../byspel/function_recursion.tung)
  showeth dependent function fields and partially applied recursive calls.
- a nested split of a descendant generaliseth over its record, so each deeper
  constructor's record nameth its fields' records. ordinary container matches
  retain their ordinary eliminators. each carried record's target label
  selecteth the specialised constructor metadata for its child projections:
  a `rose list` head is a recursive rose even though the ordinary list
  eliminator hath no hypothesis for that head. this alloweth recursive calls
  through nested containers or mutual peers back to the structural family.
  a helper quantified over an ordinary container doth not inherit evidence
  for its arbitrary input: matching a `rose list` alone cannot establish that
  its head descendeth from an enclosing rose.
- a call projecteth `now` from the record of the value it passeth, compared
  after normalisation. the record's target must be the chosen structural
  family. a container or mutual peer cannot justify a call merely because
  its empty `now` type happeneth to fit the required result type. the child's
  entire index shape must also match the source declaration, and explicit
  leaf inputs must equal the matching parts, as with direct induction.
  outside that shape, a root record's `now` is the inhabited `[goal, goal]`.
  its `below` still retaineth descendants, which may re-enter the shape;
  the trivial `now` never justifieth an off-domain call.
  [`index_memo.tung`](../byspel/index_memo.tung)
  showeth indexed descendants, dependent results, and domain re-entry.
- the passed value must be a proper descendant: the matched value itself, or
  a rebuilt copy of it, is rejected.
- nested recursive definitions retain enclosing definitions' induction
  evidence. a local binder shadoweth a recursive name ordinarily. calls to
  an unshadowed enclosing function still use its own evidence. nested
  matches preserve every applicable enclosing course-of-values record, so
  descendant checks for one function do not replace another function's checks.
- the bare recursive name cannot be used as a value or passed to another
  function. a checked descendant application may yield a function by leaving
  trailing quantified inputs unapplied. mutually recursive lets remain
  rejected. explicit joint induction through `unbuild` remaineth available.

### fields and kernel records

[fields](language.md#fields) owneth the syntax;
[`fields.tung`](../byspel/fields.tung) useth plain,
parameterised, chained, and dependent fields.

- after an ilk with one constructor and no indices is checked, each named
  explicit field becometh a hidden global `ilk.field`, using the same checked
  core projection as flock members. its header parameters are implicit.
  earlier fields in its type become projections from the same value;
  constructor-local implicit fields retain their positions and dependencies.
  `.` cannot occur in a source name, so only `value.field` reacheth it.
- `value.field` inferreth the value, readeth its ilk from the type's head, and
  applieth that ilk's accessor, solving its parameters by unification. a
  value whose type is not such an ilk hath no fields.
- types, goals, and proof audits recover named projections from the receiver's
  checked type. this display step changeth neither conversion nor proof checking.
- source hath no record syntax. the kernel keepeth closed records only for
  course-of-values memos: the pattern compiler buildeth `below` and `now`
  records internally. a family cannot occur inside a record field of its own
  constructor.

### modules

`ModuleId` and `SymbolId` preserve nominal identity through aliases and
re-exports. two imports of one identity do not conflict. identity interning
permiteth pointer comparisons, with structural equality and ordering as
fallbacks; correctness never dependeth on sharing.

[development.md](development.md#projects-and-imports) owneth module scheduling,
checked interfaces, and cache invalidation. the
[language reference](language.md#files-and-modules) owneth visibility and lookup.

### flocks and bizens

[`flocks.tung`](../byspel/flocks.tung) showeth these
rules in checked source.

[flocks, bizens, and laws](language.md#flocks-bizens-and-laws) owneth the
syntax. elaboration:

- a flock parameter is `name:type` without `@`; other unnamed slots than
  `@:parent` are rejected, and a flock needeth a member or a parent.
- a flock elaborateth to a one-constructor family `name` over its parameters.
  the constructor `name_make` holdeth one implicit field per parent dictionary,
  then one explicit field per member in declaration order. the eliminator is
  `unbuild name`.
- each member becometh a global accessor
  `member:[@parameters, @dictionary:(parameters name), type]` that selecteth its
  field through a checked core projection. a member name is therefore an ordinary global;
  it cannot repeat another name in the module.
- each parent becometh an inherited instance `name_parent_i` of the parent
  flock. it projecteth the parent dictionary from a dictionary of this flock.
- all member types use the ordinary expression parser and elaborator.
  a law is a member whose type requireth an equality proof, such as
  `[x:α, (x keep) = x]`; no separate law syntax tree or lowering is needed.
  earlier members in its type refer to the constructor's earlier fields.
  patterns use an ordinary `match` in the type. laws trigger no automatic
  rewriting. a law accessor provideth reusable proofs through a flock
  requirement, and an explicitly constructed dictionary must supply them.
- accessors are core primitive projections `Field index dictionary`, built
  from the checked constructor and checked by the kernel. a projection reduceth
  only on a constructor application; on a neutral dictionary it stayeth a
  neutral `NField`, compared structurally.
- an ordinary constructor application checketh each law against its field
  type, with the actual preceding fields substituted. a law about a method
  therefore concerneth the supplied method, including in a parent dictionary.
  `sorry` is accepted as for any term and is reported for the bizen.
- `show flock` publisheth the family, constructor, eliminator, accessors, and
  parent instances, and carrieth the flock's instance registry to importers.

requirements:

- `@:type` is an anonymous implicit slot of any product. when its type
  applieth a flock, an omitted argument is found by instance search. every
  name in the requirement must already be in scope. in a declaration header,
  requirements and named slots lower to lambda binders and must precede bare
  slots.

bizens:

- a bizen's type is a product of implicit slots ending in a flock
  application, or the application alone; explicit slots are rejected.
- `bizen:type { let member ≔ body ... }` lowereth named members to ordinary
  local bindings and a dictionary constructor application. each member and law
  is supplied once; missing, repeated, and unknown members are rejected.
- the flock declaration order determineth field checking and scope, regardless
  of source member order. expected field types supply omitted annotations;
  written annotations are ordinary ascriptions and must agree. later fields
  see earlier values, including type fields and methods used by laws.
- a member's own right-hand side nameth its global accessor. earlier members
  are lexical bindings; there is no speculative global-then-sibling retry.
  a call intended for another carrier may qualify the global accessor.
  recursive methods use ordinary recursive helpers.
- parent dictionaries are ordinary implicit fields. search findeth requirements
  or registered instances by class identity before supplied ancestor members
  construct a missing parent inline. inline construction useth the same lowering
  and checking rules. an existing parent dictionary retaineth precedence, even
  when another imported flock hath same-spelled members.
- the head fixeth constructor parameters before members are checked, so case
  functions receive their expected types. the dictionary is registered only
  after its complete ordinary term is checked; there is no special kernel rule.
- a bizen is a global definition named `#instance_n` in its module. it cannot be
  named in source. every bizen is registered, whether or not its flock is
  shown, and importers see it wherever the flock is visible.

instance search:

- an omitted implicit argument whose type applieth a flock becometh an instance
  goal. goals are solved after the declaration's ordinary unification and
  before the kernel check, so their types are as specific as the program maketh
  them. a supplied `@` argument bypasseth search.
- a declaration's annotation is closed, so its goals are settled before its
  body is checked: goals whose input parameters have known heads are solved, and stuck
  equations of the annotation are split by first-order approximation, first
  against a rigid application and then between two applied holes. a body
  therefore matcheth against a goal whose members can compute, as in
  `((l sift p) sift p) = (l sift p)`. fallback bizens still wait for
  the whole declaration.
- a goal waiteth while the head of any input parameter of its flock is
  unknown, as rocq's `!` mode doth; parameters written `* out` are outputs
  that search findeth, as lean's `outParam`. meanwhile a waiting goal may be
  solved by local requirements and the parents they project. when nothing else
  can progress, a stuck equation is split (see
  [inference boundary](#inference-boundary)); the parts of a split are split
  again at once, so `?φ ?a x = ∏ α x` reacheth `?φ = ∏`. last, the flock's
  fallback bizens (`bizen fallback: …`) are tried, as lean's default
  instances. a goal still unknown after that is an error asking for an
  annotation.
- search trieth local dictionaries first, innermost first. then it trieth
  registered bizens, then inherited instances. a later tier is tried only when
  no candidate of an earlier tier matcheth, so a direct bizen outranketh a
  parent path.
- registered bizens are tried in order of priority, higher first, then the
  latest declared first, as lean doth. the first candidate that matcheth, with its requirements
  solved, is chosen, so overlapping bizens are never ambiguous. no
  match reporteth the goal, available local requirements, and a rejected
  candidate's reason when available. registration rejecteth equivalent
  instance patterns. inherited search selecteth the first successful path; it
  neither compareth parent dictionaries nor proveth them equal.
- a candidate's own requirements are solved recursively, to a depth of 16.
  a goal that repeateth one of its ancestors faileth. a requirement whose
  inputs are still unknown is first fixed by the one local requirement of its
  flock that unifieth with it, as a parent projection from `ρ module μ` to
  `μ group_+` findeth its ring. otherwise it waiteth as a goal of the
  declaration only when it belongeth to the outermost goal's candidate; in a
  nested search the candidate faileth, since a waiting requirement there
  would commit the search to a path it can never check.
  instance patterns and cycle keys compare global identities without their
  universe instantiations. sort arguments remain significant, and the kernel
  still validateth universe constraints.
- candidates are filtered before unification: a bizen whose flock
  arguments start with another family cannot match, and an inherited instance
  is tried only when its child flock hath a local requirement or a bizen with
  those heads.
- inherited paths are not ranked by length. the compiler defineth no bizens
  of its own; every bizen, including each fallback, is bookhoard or program
  code.

### inference boundary

term inference useth a typed higher-order pattern fragment. a hole applied to
distinct rigid local variables can be solved by abstraction. local definitions
are substituted before its telescope is captured. occurs and scope checks
reject cyclic or escaping solutions. candidate solutions are checked before
assignment. a candidate whose check would leave a pending equation, such as
a dictionary projection before instance search fixeth the dictionary, is not
assigned: its check is undone and its equation stayeth pending. a candidate
whose check faileth while it or its hole's type still containeth unsolved
holes is treated the same way, since a solution may give an application its
function type. the same candidate is checked again only after one of the
blocking holes is solved; a failure with no unsolved hole is reported.

a solution may mention another hole applied to locals that the solved hole
cannot see, as `?t = ?f x` when `?t` hath no `x`. if that hole is applied
only to local variables and its type doth not depend on the hidden ones, it is
pruned: it is solved by a fresh hole over the inputs it may keep, and the
solution is quoted again, so `?t = ?f x` becometh `?t = ?f′` with `?f′`
over the inputs `?t` can see.

a hole is solved by the unforced other side and replaced by its folded
quotation, which keepeth definitions by name: a bizen's parent dictionary
stayeth `#instance_n` rather than its constructor with every proof inlined.
because a folded solution nameth constants the elaborator never instantiated,
generalisation addeth the instantiated universe constraints of every constant
in the final term. unification compareth two applications of one constant by
their folded arguments before unfolding either.

when a numeric literal meeteth a constructor application, unification exposeth
the literal's outer constructor and compareth its fields in either orientation.
thus `2` against `?n heir` solveth `?n` as `1`; signed integers use the same
view of `overnaught` and `heir_undernaught`. fields stay literals, and exact
literal comparisons remain constant-time. induction and index matching share
this constructor view; no numeric index equation hath a separate rule.

nonpattern equations remain pending and are retried only after a new
assignment. when
instance search or a pattern column can make no other progress, one pending
equation between an applied hole and a rigid application is split by
first-order approximation, as in agda and lean: `?f a = g b` becometh
`?f = g` and `a = b`. this may miss a non-first-order solution, so it is
never tried earlier. while a declaration's annotation is settled, the same
split also applieth between two applied holes, `?f a = ?g b`. general higher-order unification
remaineth unsupported.
dictionary search is described under [flocks and bizens](#flocks-and-bizens). unresolved equations require annotations or explicit `@`
arguments. every term hole must disappear before the kernel check. universe
holes may still generalise under valid constraints.

### ordinary lists

[`list_family.tung`](../byspel/list_family.tung) useth one
universe-polymorphic list at value and type levels. lists may index inductive
families; their operations compare by ordinary conversion. no native type-level
list, element-kind rule, or implicit library import is needed.

list concatenation recurseth on the left input. `xs · ∅` remaineth neutral
while `xs` is unknown; right identity requireth induction. conversion neither
addeth a rewrite for it nor inferreth arbitrary concatenation splits.

### deeds and host bindings

[`deed_loop.tung`](../byspel/deed_loop.tung) showeth host
bindings, bounded repetition, and a deed loop.

normalisation and execution share one host catalogue, `hostBindings` in `Tung.Primitive`, and
one failure convention: a fallible operation returneth a `maybe` or a
`string ∑ α`, as in the ordinary language. bookhoard declareth every key in
`_fremmed.tung` and the `deed/` modules, with its signature, as described in
[language.md](language.md#runtime-boundary).

a top-level `let name:type ≔ 'key' fremmed` bindeth one trusted host constant.
the annotation is required and checked by the kernel. `Tung.Dependent.Host`
then matcheth its normalised type against the key's catalogued signature:
implicit type inputs, explicit inputs whose results do not depend on them,
and the result. universe levels are not compared. the program chooseth every
name.

- primitive types match by name. a host data type, such as `𝟙`, `𝟚`,
  `maybe`, `∏`, `∑`, `list`, `wordbook`, `_process_result`,
  `_request`, or `_response`, matcheth only the `ilk` of that name declared in
  its bookhoard file, such as `ilk/maybe.tung`. a lookalike declared
  elsewhere is a different type.
- `deed` and `task` are opaque primitive families of kind `[*, *]` at each
  universe. `ilk/task.tung` re-exporteth the native task family. neither family
  hath a constructor or eliminator; an ordinary `ilk task` cannot stand for
  a runtime task handle, even at the canonical library path.
- the host catalogue also fixeth each data family's type parameters,
  constructor identities, and field types. binding a host operation requireth
  those schemas, including data families used by constructor fields. a
  canonical path alone doth not justify a host constant. empty, renamed,
  indexed, or differently typed replacements are rejected.
- each key may be bound once. unknown keys, different types, local
  bindings, and bindings without annotations are rejected.
- primitive value types live in the base universe and have no universe
  parameters. a literal inhabiteth the primitive type of its kind: `'x'` string,
  `42` ℕ, `+42` and `-7` ℤ, `1.5` float, and `` `a `` unicode. an integer
  literal always hath a sign; unsigned digits are a natural. equal literals
  convert; floats compare by bit pattern, so a NaN literal equaleth itself.
- a pure host operation computeth during checking when every input is a
  literal, or a list of literals, so `+2 + +2` converteth with `+4` and a type
  may depend on an integer comparison. on other inputs a binding with a model
  unfoldeth the model, glued so goals still show its name; another stayeth
  neutral. the model is the binding's body after `fremmed`, elaborated as a
  let named by the binding, so a self-call is structural recursion, and
  stored as the hidden global `model name`, which goals print as `name`. the
  host check still requireth the model to be transparent, with the binding's
  universe parameters and normalised type, and only a pure operation may
  have one.
  bookhoard's tests check that each model agreeth with its native operation on
  generated literals; the kernel trusteth that agreement as it trusteth the
  native operation.
  results are built at the catalogued type, so a comparison yieldeth `yea` or
  `nay` and a partial operation yieldeth `none` or `x some`. `pureOperation`
  in `Tung.Primitive` defineth these operations once for the kernel and
  erased runner.
  normalisation preserveth the actual result family's universe arguments and
  type parameters, including nested results; it never replaceth them with zero.
- deed constants never reduce during checking. `x deed_sheer deed_bind f` is
  not convertible with `x f`, and `deed_steadfast` never unfoldeth. pure
  normalisation therefore stayeth terminating.
- `deed_steadfast` is the only source of unbounded execution. it is restricted to
  deed results, so an infinite loop is an action, never a pure value.
  bounded repetition useth ordinary induction.
- the standard model readeth each primitive type as its runtime set, each pure
  host operation as its total definition, and each deed type as a
  one-element set, assuming the checked data schemas and catalogued operations.
  this interpretation doth not add an inhabitant of `𝟘`; `sorry` is the
  explicit exception. no constant extracteth an `α` from an `α deed`.
  positivity rejecteth a family hidden inside a deed argument.
- evaluation eraseth types and universe levels; the runner's rules are in
  [deeds](language.md#deeds) and the
  [runtime boundary](language.md#runtime-boundary).
- [`host_tales.tung`](../byspel/host_tales.tung)
  bindeth pure operations, and
  [`host_deeds.tung`](../byspel/host_deeds.tung) useth files,
  tasks, and strings.

### proof construction

`is.tung` defineth identity as an ordinary indexed family. `throughbear`,
`leibnitz`, and `throughgo` prove substitution and composition without extra
kernel rules. `inlook` passeth a matched value and its branch equation to an
ordinary case function. a constant result family may require a written motive.
function extensionality remaineth the named axiom `fall_umtake`.

well-founded recursion is ordinary library code in
[`ilk/accessible.tung`](../bookhoard/ilk/accessible.tung).
`wellgrounded_selfcall` recurseth structurally on accessibility evidence.
`wellgrounded_selfcall_by` taketh an explicit result motive `[α, *]` and a
measure `[α, μ]`; its recursive callback requireth a proof that the new measure
is smaller. identity elimination keepeth computed measures usable after a
match, without axiom K. dependent inputs may be packed in a single-constructor
type, or remain curried in the motive when the measure doth not depend on them.
[`wellgrounded.tung`](../byspel/wellgrounded.tung) showeth
this construction. the parser and kernel add no measured-recursion rule.

the [bookhoard reference](../bookhoard/reference.md#law-proofs) owneth library
proof coverage and assumptions. [proof checking](language.md#proof-checking)
owneth cli and editor output; the [logical boundary](#logical-boundary)
owneth their trust requirements.
