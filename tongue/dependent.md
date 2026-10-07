# dependent tung design

audience: agents. purpose: how the checker realiseth the language: the dependent
core, elaboration, pattern compilation, instance search, the logical boundary,
and the settled [design decisions](#design-decisions). each section stateth its
algorithm, rejection cases, and limits.
[`language.md`](language.md) owneth what a program author writeth and observeth:
syntax, names, libraries, the runner, and command-line output. this document
linketh to it rather than restating those rules.
[`tutorial.tung`](tutorial.tung) is the maintainer's draft of the
target syntax, not a checked example. [`todo.md`](../todo.md) tracketh
remaining work.

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
  cumulative subtyping in this initial core.
- evaluation is glued: a transparent global applied to its arguments stayeth
  folded, with its unfolding computed only when a value is forced. every
  public evaluation result is forced at its head, and quotation for
  conversion unfoldeth everything, so folding never changeth which terms are
  equal. motives keep definitions folded, and display quotation unfoldeth a
  definition only when that reacheth a constructor, literal, record, or
  variable; a stuck elimination equal to an enclosing definition applied to
  the eliminated child is shown as that application.
- inference solveth direct universe-hole equations. remaining holes become
  universe parameters qualified by their constraints. maximum constraints
  retain their alternatives; inference never guesseth one branch.
  generalisation discardeth tautological constraints with the same canonical
  atom comparison as constraint insertion.
- each global application instantiateth and checketh exported universe
  constraints. the exact solver useth difference constraints and negative-cycle
  detection. maximum alternatives can require exponential search.
- the kernel rechecketh generalised terms with rigid parameters and proveth every
  generated universe obligation from the declared assumptions.
- inconsistent universe constraints are rejected before normalisation proceeds.
  the checker keepeth an assignment that satisfieth the constraints so far; a new
  constraint that it satisfieth is accepted at once, and only one that it
  violateth re-solveth the whole set.
  public normalisation first checketh its input. raw NBE remaineth private.
- only checked, closed declarations enter the environment. transparent globals
  are ordered and cannot reference themselves. inductive families, constructors,
  and generated eliminators are checked and inserted together. there are no
  axioms or general recursion in the pure core. trusted host constants enter only
  through the catalogue described under
  [deeds and host bindings](#deeds-and-host-bindings).

the api exposeth `infer`, `check`, `define`, `validate`, and `normalise`.
`defineInductive` checketh rigid declarations; `inferInductive` generaliseth valid
universe constraints before the same check.
explicit and implicit applications retain their visibility; insertion of
omitted source arguments belongth to elaboration. runtime erasure is separate.

the implementation followeth the dependent-product rules described in
[lambda pi](https://www.andres-loeh.de/LambdaPi/). its new tests include closed
typing judgements, capture-sensitive reductions, universe-polymorphic globals,
kernel rejection cases, and independent arithmetic models of universe
constraints. inductive declarations use generated dependent eliminators,
following the [Lean inductive rules](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/).

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
program and is not reported. an `orsetting` declaration is a named axiom, a constant
with a checked type and no body: a consistent proof may rely on the `orsetting`
assumptions it lists, but not on `sorry`.
the [lean axiom boundary](https://lean-lang.org/doc/reference/latest/Axioms/#consistency)
describeth the same distinction between checking a term and justifying its
assumptions.

the intended consistency argument for terms without `sorry` requireth correct
kernel rules, universe entailment, inductive generation, conversion, and
trusted host operations. host data schemas and compatible cached definitions
are checked at their entry boundaries. regression tests exercise these rules;
they are not a machine-checked proof of consistency or subject reduction.

## implemented source

```tung
let identity-type ≔ [α: *, x: α, α]
let sameness: identity-type ≔ {α ^ {x ^ x}}
let alias: [α: *, *] ≔ α
let result: * ≔ * alias
let choose: [α: *, @x: α, α] ≔ x
let chosen ≔ * choose @*
let implicit-identity: [@α: *, x: α, α] ≔ x
let inferred ≔ * implicit-identity
```

- annotations and bodies use one expression parser and lexical namespace.
- module definitions resolve to `SymbolId` in dependency order. local bindings
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
  value of one.
- `ℕ`, `0`, `heir`, `ℤ`, `overnaught`, `heir_undernaught`, `float`,
  `unicode`, `text`, `deed`, `task`, `=`, and `eftbend` are
  primitive and visible in every module. an imported or local name of the same spelling shadoweth
  them.
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
  fills that hole. so `{ empty ^ 𝟘, _ ‥ _ ^ 𝟙 } transport p only` learneth its
  input type from `p`. a lambda whose body matcheth inside a larger
  expression is not postponed and needeth a binder annotation.
- an expected implicit product introduceth its binders before any expression
  that doth not bind them itself, as in agda, so a polymorphic name meeteth a
  polymorphic type. a polymorphic value checked against any other type,
  including an unknown one, is specialised.
- an ascription with holes first learneth from the expected type, then checketh
  its body.
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
  zero: ℕ,
  heir: [ℕ, ℕ]
}

let rebuild: [x: ℕ, ℕ] ≔
  {_: ℕ ^ ℕ} unbuild ℕ zero {n, ih ^ ih heir} x

ilk sameness: [α: *, x: α, α, *] {
  refl: α sameness x x
}

let transport: [@α: *, @x: α, @y: α, proof: α sameness x y,
  family: [α, *], worth: x family, y family] ≔
  {z, _ ^ z family} unbuild sameness @α @x worth y proof
```

- `ilk name:signature { ... }` declareth one family. constructors share the
  ordinary namespace. the generated eliminator is not a name: `unbuild name`
  denoteth it, with `name` resolved as a family. a name that resolveth to
  anything but an ilk or flock is rejected.
- the named prefix of the outer bracket declareth uniform parameters. later
  bare slots and a nested result product declare indices. only uniform
  parameters scope over constructor annotations. inherited constructor and
  eliminator parameters are implicit, regardless of family argument visibility.
- every constructor stateth its type, as in a GADT; a constructor without one is
  rejected. constructors require a saturated result of their family with
  unchanged parameters. constructor fields must fit within the family's
  universe.
- a recursive field is the family itself or a function ending in it, such as
  `[ξ, φ freer α]`, whose inputs do not mention the family: the family occurreth
  strictly positively. normalisation exposeth aliases before checking
  occurrences. negative, nested, and mutual recursion are rejected.
- `unbuild name` taketh the implicit parameters, a motive, one method per
  constructor in declaration order, the indices, and the value. the motive
  taketh the indices and value and returneth a type. each recursive field is
  followed by its induction hypothesis in that constructor's method; for a
  function field `k` the hypothesis is `[inputs, motive (inputs k)]`.
- induction computeth on constructors and remaineth neutral on variables.
  recursion thus descendeth through constructor children. arbitrary recursive
  `let` definitions remain errors. source patterns compile to the eliminators
  described below.
- the identity family above provideth intensional equality and path induction.
  `transport` computeth to its supplied value on `refl`. there is no equality
  reflection or proof irrelevance. `sorry` remaineth the assumption described
  under the [logical boundary](#logical-boundary).

### pattern matching and recursion

[`examples/dependent_match.tung`](examples/dependent_match.tung) showeth case
functions, `match`, nested patterns, and structural recursion.

```tung
let not: [bool, bool] ≔ { no ^ yes, yes ^ no }

let plus: [x: nat, y: nat, nat] ≔ match x {
  zero ^ y,
  n heir ^ (n plus y) heir
}

let reverse_onto: [@α: *, list: α list, done: α list, α list] ≔ match list {
  ∅ ^ done,
  head ‥ tail ^ tail reverse_onto (head ‥ done)
}
```

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
- every row hath the same number of patterns. a match hath one pattern per
  scrutinee, including inside a recursive definition. written rows are
  validated before recursive clause collection projecteth their columns.
  every constructor's written arguments are checked and aligned before
  intersection. a name cannot be bound twice in one written row.
- rows are tried in order.
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
  integer, text, unicode, or float literal pattern
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
  value. a variable matched against a constructor case denoteth the rebuilt
  constructor value.
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
  `[yea = nay, 𝟘] ≔ {}` holdeth. an index whose constructor cannot be
  decided, such as a function call, is rejected, as is an index variable
  that appeareth twice or in the family's parameters: unifying `a = a` would
  need axiom K, which tung leaveth unprovable.
- a recursive let may match an indexed value when each index is a distinct
  input bound before it and unused by the family's parameters. the motive
  abstracteth those index inputs with the value, so the result type may
  mention them. an index input is not a column: it must be matched by a
  variable, and each branch rebindeth its name to the constructor's index.
  a recursive call omitteth no input; an explicit index argument is unified
  with the child's own index, and the hypothesis already standeth there.
  course-of-values recursion, and recursion on a value whose indices are
  constructors, still reject indexed families.
- a family without indices revertth the inputs
  whose types mention the matched value in the same way, so in
  `{yea, known ^ ...}` against `[b: 𝟚, (x p) = b, ...]` the yea branch seeth
  `known: (x p) = yea`. a split that also carrieth course-of-values
  recursion records revertth nothing. a header slot is a parameter only while every
  constructor's written result passeth it unchanged; the slots after it are
  indices, as in `ilk tag: [a: *, *] { integer: [ℤ, ℤ tag] }`.

a `let` whose body freely nameth itself is recursive. it needeth an annotation.
inside a recursive definition, a `match` on a named input rebindeth that name
to the value matched at each step. repeated named scrutinees use the same
pattern intersection as ordinary matches.

the compiler first trieth direct induction on each explicit input of an
unindexed family, in input order. if none succeedeth, it trieth course-of-values
recursion on the same inputs in the same order. the first candidate whose
branches and recursive calls check is selected. failed candidates restore
inference state. recursive calls use ordinary lexical resolution and compare
normalised argument values with induction evidence; aliases of descendants
are accepted, and a shadowing variable is checked by its own value.

- implicit inputs before the structural input, and explicit inputs its type
  dependeth on, are fixed. recursive calls must pass fixed explicit inputs
  unchanged and cannot supply implicit arguments.
- implicit inputs after the chosen structural input are rejected. each
  recursive call must supply every explicit input of the recursive definition;
  partial recursive applications are rejected.
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
  `brecOn`. the motive becometh `r{below: x below, now: x result}`, where
  `below` is a large elimination whose record holdeth, for each direct
  recursive field, that field's own `r{below, now}` record. a nested split of a
  descendant generaliseth over its record, so each deeper constructor's
  record nameth its fields' records. a call projecteth `now` from the record
  of the value it passeth, compared after normalisation.
- the passed value must be a proper descendant: the matched value itself, or
  a rebuilt copy of it, is rejected. a function child cannot be called under
  course-of-values recursion.
- nested recursive definitions retain enclosing definitions' induction
  evidence. a local binder shadoweth a recursive name ordinarily. calls to
  an unshadowed enclosing function still use its own evidence. nested
  matches preserve every applicable enclosing course-of-values record, so
  descendant checks for one function do not replace another function's checks.
- the recursive name cannot be used as a value. mutual recursion is rejected
  in this version, and so is recursion on an indexed family.

### records

[records](language.md#records) owneth the syntax;
[`examples/dependent_records.tung`](examples/dependent_records.tung) useth
types, values, projection, and update.

- a record type inhabiteth the largest universe of its field types; the empty
  record `r{}` hath the empty record type in the base universe.
- a record checked against a record type must match its fields exactly;
  inferred, its type listeth its fields. an update bindeth its base once.
- a projection of a variable stayeth neutral.
- the kernel storeth fields sorted by name, so source order never changeth
  identity. fields are not dependent, and records have no eta rule.
- a family cannot occur inside a record field of its own constructor.

### modules

[`examples/dependent_modules/`](examples/dependent_modules/) splitteth a
program across three files. run it with
`tung tongue/examples/dependent_modules/main.tung`.

```tung
use host.tung
use natural.tung tale

let main: 𝟙 deed ≔ >{then, tale~four repeat ('tung ' write), '\n' host~write}
```

- `use path` and `use path alias` import a module. `path` followeth the
  ordinary [module search rules](language.md#libraries-and-imports), so
  `tung.yaml` roots and `TUNG_PATH` apply.
- visibility and re-export syntax follow the ordinary
  [module rules](language.md#files-and-modules). a shown inductive family
  exposeth its constructors and generated eliminator. a re-exported flock
  carrieth its instance registry.
- each definition retaineth its canonical `ModuleId` and `SymbolId` through
  aliases and re-exports. bare-name ambiguity compareth these identities; two
  imports of one identity do not conflict.
- each module is checked once in dependency order, and identities are
  qualified by module, so a module imported along two paths keepeth one
  identity. the [import rules](language.md#libraries-and-imports) define
  cycle and missing-source diagnostics. errors inside an import retain that
  module's path and span as the use chain is extended.

### flocks and bizens

[`examples/dependent_flocks.tung`](examples/dependent_flocks.tung) defineth
equality and functor flocks, requiring bizens, and a parent flock.

```tung
flock hath_≍: [α: *, *] {
  let ≍: [α, α, 𝟚]
  let eftbend: [x: α, (x ≍ x) = yea]
}

let ≭: [@α: *, @: α hath_≍, a: α, b: α, 𝟚] ≔ match a ≍ b { yea ^ nay, nay ^ yea }

bizen: [@α: *, @: α hath_≍, (α maybe) hath_≍] {
  let ≍ ≔ { none, none ^ yea, a some, b some ^ a ≍ b, _, _ ^ nay }
}

flock atfoldsome: [φ: [*, *], @: φ functor, *] {
  let sheer: [@α: *, α, α φ]
}
```

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
  field through the eliminator. a member name is therefore an ordinary global;
  it cannot repeat another name in the module.
- each parent becometh an inherited instance `name_parent_i` of the parent
  flock. it projecteth the parent dictionary from a dictionary of this flock.
- a member whose bracketed type endeth in an equation,
  `let name:[binders, left = right]`, is a named law. `=` is the primitive
  identity type, so each side is one term and a compound side needeth
  parentheses.
  the law is an ordinary field of the flock's family, of type
  `[binders, left = right]`, in source order among the other members; earlier
  members in it refer to the constructor's earlier fields. a law with pattern
  slots matcheth them on both sides. nothing executeth or rewriteth with a law.
  its accessor is a source term, so a flock requirement provideth reusable
  proofs of its laws, and an explicitly constructed dictionary must supply
  them.
- accessors are core primitive projections `Field index dictionary`, built
  from the checked constructor and checked by the kernel. a projection reduceth
  only on a constructor application; on a neutral dictionary it stayeth a
  neutral `NField`, compared structurally.
- a bizen defineth each law of its flock as it defineth any member: the proof
  is checked against the field type with this bizen's earlier members
  substituted, so `eftbend` proveth a law that holdeth by computing them. an
  inline parent's law seeth the members defined for that parent. `sorry` is
  accepted as for any member and is reported for the bizen.
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
- the body holdeth only `let` definitions. each member and law is supplied
  exactly once; a missing or unknown one is rejected. an annotation on a
  member is checked and must agree with the member type.
- a bizen may also define the members and laws of a parent flock that hath no
  bizen of its own at those arguments. that parent's dictionary is built
  inline, and inherited search projecteth it from this bizen.
- a member that nameth its own accessor useth the flock through instance search,
  as any visible name doth, so it can use the flock at another type. the bizen
  being defined is not yet registered, so a recursive member is written as
  a recursive let that the member nameth, as in lean.
- the head's arguments fix the flock parameters before members are checked, so
  case functions need no annotation. parent fields are solved by instance
  search inside the bizen, where its requirements are local dictionaries.
- a bizen is a global definition named `bizen_n` in its module. it cannot be
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
  candidate's reason when available. bizens are unique per type, so
  every parent projection reacheth the same dictionary: the first matching
  inherited instance is used, and a diamond of parents is not ambiguous.
- a candidate's own requirements are solved recursively, to a depth of 16.
  a goal that repeateth one of its ancestors faileth, and a requirement whose
  type is still unknown waiteth as a goal of the declaration.
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

[`examples/dependent_list.tung`](examples/dependent_list.tung) defineth one
universe-polymorphic `list`, its `∅` and `‥` constructors, and ordinary append
(`·`), `warp`, and `gather`. check it with:

```sh
tung --check-module tongue/examples/dependent_list.tung
```

append these examples to that file to use the same family at several universes:

```tung
ilk unit: * { only: unit }
let values: unit list ≔ >{‥, only, only, ∅}
let types: * list ≔ >{‥, unit, [unit, unit], ∅}
let constructors: [*, *] list ≔ >{‥, list, ∅}
let joined: * list ≔ types · >{‥, unit, ∅}
```

- element types may be values of a universe or function types between universes.
  the same constructors and functions handle all of them.
- lists can index ordinary inductive families. computed append and map results
  compare by kernel conversion. order and duplicate elements remain observable.
- empty lists need a determined element type. supply `∅ @α` or an annotation
  when arguments and the expected type cannot determine it.
- append recurseth on its left input. an unknown left list remaineth neutral,
  including `xs · ∅`. right identity requireth an induction proof; the checker
  doth not add a special rewrite or infer an arbitrary concatenation split.
- list definitions are supplied as source. the compiler hath no built-in list
  type, operator names, element-kind rules, or implicit standard-library import.
  imports remain a separate migration stage.

### deeds and host bindings

[`examples/dependent_deed.tung`](examples/dependent_deed.tung) useth
bookhoard's host bindings, repeateth an action by induction, loopeth with the
deed fixed point, and readeth console input. check and run it with:

```sh
tung --check-module tongue/examples/dependent_deed.tung
tung tongue/examples/dependent_deed.tung
```

normalisation and execution share one host catalogue, `hostBindings` in `Tung.Primitive`, and
one failure convention: a fallible operation returneth an `maybe` or a
`text ∑ α`, as in the ordinary language. bookhoard declareth every key in
`_foreign.tung` and the `deed/` modules, with its signature, as described in
[language.md](language.md#runtime-boundary).

a top-level `let name:type ≔ 'key' fremmed` bindeth one trusted host constant.
the annotation is required and checked by the kernel. `Tung.Dependent.Host`
then matcheth its normalised type against the key's catalogued signature:
implicit type inputs, explicit inputs whose results do not depend on them,
and the result. universe levels are not compared. the program chooseth every
name.

- primitive types match by name. a host data type, such as `𝟙`, `𝟚`,
  `maybe`, `∏`, `∑`, `list`, `table`, `_process_result`,
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
  parameters. a literal inhabiteth the primitive type of its kind: `'x'` text,
  `42` ℕ, `+42` and `-7` ℤ, `1.5` float, and `` `a `` unicode. an integer
  literal always hath a sign; unsigned digits are a natural. equal literals
  convert; floats compare by bit pattern, so a NaN literal equaleth itself.
- a pure host operation computeth during checking when every input is a
  literal, or a list of literals, so `+2 + +2` convertth with `+4` and a type
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
  in `Tung.Primitive` defineth these operations once for the kernel, the
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
- [`examples/dependent_tales.tung`](examples/dependent_tales.tung)
  bindeth pure operations, and
  [`examples/dependent_host.tung`](examples/dependent_host.tung) useth files,
  tasks, and text.

### proving status

this summary pointeth to the rules above.
[`todo.md`](../todo.md#theorem-proving) ordereth the remaining work and its
open decisions.

available:

- the primitive identity type and bookhoard's `is.tung` lemmas
  ([logic](#logic)); `unbuild name` for any ilk or flock
  ([inductive declarations](#inductive-declarations-and-proofs)).
- dependent matching with index unification, impossible rows, computed
  scrutinees, and `match e for known`
  ([pattern matching](#pattern-matching-and-recursion)).
- structural, accumulator, and course-of-values recursion, and well-founded
  recursion through `ilk/accessible.tung`.
- `orsetting` axioms and `sorry` holes with goals
  ([runtime boundary](language.md#runtime-boundary)).
- [`bookhoard/ilk/list_setting.tung`](../bookhoard/ilk/list_setting.tung)
  proveth list theorems without `sorry`; `Test.Bookhoard` checketh that false and
  ill-founded proofs beside them are rejected for the stated reason.

current limits:

- an ordinary match doth not record the equation between its scrutinee and
  the chosen constructor; `match e for known` doth, by matching a fresh copy
  of `e` (see [algebraic data and patterns](language.md#algebraic-data-and-patterns)).
  `sift_sift_step` in `list_setting.tung` still passeth the equation by
  hand.
- there is no rewriting. a proof writeth the property for `transport` itself,
  or chaineth `leibnitz` and `throughgo`.
- automatic recursion is structural only. well-founded recursion is
  library code: `ilk/accessible.tung` defineth an accessibility family and
  `wellgrounded_selfcalling`, written as ordinary recursion on the
  accessibility proof. mutual and nested families, and automatic recursion
  over a value whose indices are constructors, are missing.
- `ℕ` equality, order, addition, subtraction, and multiplication have
  models, and `ilk/natural.tung` proveth its order and semiring laws by
  induction on them. `ℤ` equality, order, addition, subtraction,
  multiplication, and conversion to and from `ℕ` have models by sign cases
  in `ilk/integer.tung`, which proveth its order and ring laws: order and the
  identities by sign cases, and associativity and distributivity by writing
  each integer as `p difference q` and proving the law of differences from the
  `ℕ` laws. other host operations
  compute only on literals, so statements about them are unprovable.
  function extensionality is the listed axiom `fall_umtake` in `is.tung`.
- a large proof module checketh slowly, and every run checketh its imports
  again.

## design decisions

each entry recordeth a settled choice and its reason, and linketh to the rule
that implementeth it. open choices are in [`todo.md`](../todo.md).

### direction

- one parser and one checked dependent core serve every command, test, and
  editor service. the source followeth the maintainer's draft,
  [`tutorial.tung`](tutorial.tung).
- a superseded form is removed, not kept beside its replacement. removed
  forms include constructor-first patterns, documentary constructor field
  names, literal patterns in headers, the `!` token, the `law`, `show_ilk`, and
  `induce` keywords, the ordinary effect system, the `*` name prefix, generated
  `name_induct` names, and most-specific instance selection.
- the checker hath no special rule for an individual example. refactoring
  keepeth independent kernel checking, exact runtime tests, and adversarial
  source cases.

### logic

- predicative intensional type theory with inferred universe levels: no
  impredicative `Prop`, no `Sort u : Sort u`, no cumulativity
  ([logical boundary](#logical-boundary)).
- pure definitions are total, with no general recursion. `orsetting` declareth
  named axioms and `sorry` is the unfinished hole; trusted host constants
  enter only through the host catalogue.
- `=` and `eftbend` are primitive, so laws and compiler features such as
  `match e for known` state equations without an import. as bookhoard code
  they cost an import and a lookup per compiler-built equation and changed
  nothing provable; their lemmas stay in `is.tung`.
- axiom K stayeth unprovable: matching never equateth an index with a parameter
  it already equals.
- function extensionality is the axiom `orsetting fall_umtake` in `is.tung`,
  `[@α, @β, @f, @g, [x: α, (x f) = (x g)], f = g]`, as agda and lean assume
  or derive it; `--check` listeth it for every program that relieth on it.
  equality reflection, quotient types, and a separate proof universe are
  absent. deeds have no observational equality.

### syntax

- `≔` defineth, `=` is the identity type, and `≍` is boolean equality; one
  symbol never serveth two of these.
- a let header is only the name; arguments are annotation slots, so one form
  serveth values, functions, and types
  ([let declarations](language.md#let-declarations)).
- every constructor stateth its type, as in a gadt, so indexed families need
  no second form ([declarations and types](language.md#declarations-and-types)).
- a flock requirement `@:flock` never introduceth a name, and a law is a
  member whose type endeth in `=`; there is no `law` keyword
  ([flocks, bizens, and laws](language.md#flocks-bizens-and-laws)).
- `unbuild name` nameth an eliminator, replacing generated `name_induct`
  names; an alternative block form was rejected.
- an integer literal carrieth a sign and unsigned digits are `ℕ`, so a
  quantity that cannot be negative is a `ℕ` and `ℕ` subtraction stoppeth at
  zero.
- the formatter is canonical, two-space, and writeth `a: α`.

### names

- one namespace for terms and types, so a module declareth each top-level
  name once and a slot can shadow a type that a later slot nameth.
- generic polymorphic parameters use greek letters; parameters with a
  particular role use descriptive names.
- no term reuseth a type's name. a clashing constructor taketh a new name
  (`∏` with `both`, `evenbraid` with `+i`, `nonempty` with `‥′`), another
  single-constructor type taketh a `_` prefix, and a flock whose member
  shareth its name taketh a `hath_` prefix.
- a law is named by the operators and members of its left side in order,
  joined by `_`, as `·_·`, `∅_·`, `×_+`, and `warp_sameness`. `_self` marketh
  a repeated operand. a property word is added only when the operators alone
  are ambiguous, as `+_commute` and `≤_eftbend`.

### elaboration

- bidirectional elaboration never turneth an unknown written name into a
  parameter.
- instance search followeth lean: priorities, recency, fallback bizens, and
  output parameters ([flocks and bizens](#flocks-and-bizens)). this replaced
  most-specific selection and carrier inference from candidates, whose
  interaction was unpredictable and slow.
- no let is generalised over its holes, as hindley-milner would; a
  polymorphic let writeth its parameters. this removed a heuristic that turned
  leftover holes into placeholder constants, and no bookhoard code relied
  on it.
- a declaration's annotation chooseth its dictionaries before its body is
  checked, and a case function argument waiteth for later arguments to fix
  its input type ([inference boundary](#inference-boundary)).

### recursion and matching

- recursion followeth agda and rocq: a recursive call taketh a structurally
  smaller argument ([pattern matching](#pattern-matching-and-recursion)).
  other measures use well-founded recursion from `ilk/accessible.tung`.
  unbounded execution is allowed only in deeds, and there is no unchecked
  termination pragma.
- `ℕ` is a primitive inductive family represented by literals, so matching
  recurseth structurally while literals and host arithmetic stay efficient.
- a match on a computed scrutinee replaceth its occurrences in the goal, as
  agda's `with` doth; `match e for known` instead keepeth the equation, as
  lean's `match h : e`.
- matching unifieth constructor indices by computation, so impossible rows
  and `{}` need no new syntax.

### proofs and assumptions

- every bizen defineth each law it oweth, by a checked proof or by `sorry`.
  laws are erased and never rewrite.
- `orsetting` is a listed, allowed axiom, and `sorry` an unfinished hole that
  `--no-sorry` rejecteth ([runtime boundary](language.md#runtime-boundary)).
- a host operation may name a structural model that checking unfoldeth while
  the runner keepeth the native operation, so arithmetic stayeth fast and
  becometh provable ([deeds and host bindings](#deeds-and-host-bindings)).

### deeds and the host

- `α deed` is a primitive type like haskell `IO`, composed only by bookhoard
  monad methods; there is no effect system or sequencing syntax
  ([deeds](language.md#deeds)).
- a fallible host operation returneth an `maybe` or a `text ∑ α`, so failure
  is a value.
- one host catalogue serveth checking and running. a host data type is
  identified by its bookhoard path and name; there are no primitive bizens
  ([deeds and host bindings](#deeds-and-host-bindings)).
- runtime evaluation is call-by-need, so a branch or recursive call is
  computed only when used.
