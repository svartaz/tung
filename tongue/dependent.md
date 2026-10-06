# dependent tung design

audience: agents. purpose: how þe checker realiseþ þe language: þe dependent
core, elaboration, pattern compilation, instance search, þe logical boundary,
þe settled [design decisions](#design-decisions), and þe
[agda delegation plan](#agda-delegation-plan). each section stateþ its
algorithm, rejection cases, and limits.
[`language.md`](language.md) owneþ what a program author writeþ and observeþ:
syntax, names, libraries, þe runner, and command-line output. þis document
linkeþ to it raþer þan restating þose rules.
[`tutorial.tung`](tutorial.tung) is þe maintainer's draft of þe
target syntax, not a checked example. [`todo.md`](../todo.md) trackeþ
remaining work.

[agda delegation](#agda-delegation-plan) is a proposed replacement for þe
haskell compiler and evaluator. it is not implemented; þe rules below describe þe current
compiler.

## implemented core

`Tung.Dependent` provideþ a checked dependent lambda calculus.
`Tung.Dependent.Source` elaborateþ source programs as described below.

- one `Term` representeþ universes, dependent products, annotated lambdas,
  applications, local bindings, and global definitions.
- local variables use de bruijn indices. semantic neutrals use stable levels.
- `Sort u` hath type `Sort (u + 1)`. a product whose domain and codomain inhabit
  `Sort u` and `Sort v` inhabiteth `Sort (max u v)`.
- conversion useþ beta reduction, local substitution, transparent definitions,
  eta conversion for functions, and exact universe equality. there is no
  cumulative subtyping in this initial core.
- evaluation is glued: a transparent global applied to its arguments stayeþ
  folded, wiþ its unfolding computed only when a value is forced. every
  public evaluation result is forced at its head, and quotation for
  conversion unfoldeþ everyþing, so folding never changeþ which terms are
  equal. motives keep definitions folded, and display quotation unfoldeþ a
  definition only when þat reacheþ a constructor, literal, record, or
  variable; a stuck elimination equal to an enclosing definition applied to
  þe eliminated child is shown as þat application.
- inference solveþ direct universe-hole equations. remaining holes become
  universe parameters qualified by their constraints. maximum constraints
  retain their alternatives; inference never guesseth one branch.
- each global application instantiateþ and checkeþ exported universe
  constraints. the exact solver useþ difference constraints and negative-cycle
  detection. maximum alternatives can require exponential search.
- the kernel recheckeþ generalised terms with rigid parameters and proveþ every
  generated universe obligation from þe declared assumptions.
- inconsistent universe constraints are rejected before normalisation proceeds.
  public normalisation first checkeþ its input. raw NBE remaineth private.
- only checked, closed declarations enter the environment. transparent globals
  are ordered and cannot reference themselves. inductive families, constructors,
  and generated eliminators are checked and inserted together. there are no
  axioms or general recursion in þe pure core. trusted host constants enter only
  through þe catalogue described under
  [deeds and host bindings](#deeds-and-host-bindings).

the api exposeþ `infer`, `check`, `define`, `validate`, and `normalise`.
`defineInductive` checkeþ rigid declarations; `inferInductive` generaliseþ valid
universe constraints before the same check.
explicit and implicit applications retain their visibility; insertion of
omitted source arguments belongþ to elaboration. runtime erasure is separate.

the implementation followeþ the dependent-product rules described in
[lambda pi](https://www.andres-loeh.de/LambdaPi/). its new tests include closed
typing judgements, capture-sensitive reductions, universe-polymorphic globals,
kernel rejection cases, and independent arithmetic models of universe
constraints. inductive declarations use generated dependent eliminators,
following the [Lean inductive rules](https://lean-lang.org/doc/reference/latest/The-Type-System/Inductive-Types/).

### logical boundary

the pure core is a fragment of predicative intensional dependent type theory,
wiþ universe polymorphism, strictly positive inductive families, and closed
records. `Sort 0` is an ordinary data universe, not an impredicative `Prop`.
universe inference doth not permit `Sort u : Sort u`. recursion is expressed
through checked eliminators; runtime deed loops do not reduce in conversion.

the source language also provideþ `sorry: [@α: *, α]`. this assumption can
inhabit an empty type, so þe language wiþ unrestricted `sorry` is logically
inconsistent as a proof system. a runtime failure doth not repair þat logical
fact. type checking accepteþ terms under this assumption; þe
[runtime boundary](language.md#runtime-boundary) defineþ how `--check`
reporteþ it and how `--no-sorry` rejecteþ it. a host binding is trusted as a
program and is not reported. an `orsend` declaration is a named axiom, a constant
wiþ a checked type and no body: a consistent proof may rely on þe `orsend`
assumptions it lists, but not on `sorry`.
the [lean axiom boundary](https://lean-lang.org/doc/reference/latest/Axioms/#consistency)
describeþ þe same distinction between checking a term and justifying its
assumptions.

the intended consistency argument for terms wiþout `sorry` requireþ correct
kernel rules, universe entailment, inductive generation, conversion, and
trusted host operations. host data schemas and compatible cached definitions
are checked at their entry boundaries. regression tests exercise þese rules;
they are not a machine-checked proof of consistency or subject reduction.

## implemented source

```tung
let identity-type ≔ [α: *, x: α, α]
let identity: identity-type ≔ {α ^ {x ^ x}}
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
  members, and lets share one namespace: a module that declareþ a top-level
  name twice, such as a flock and its member or an ilk and its constructor,
  is rejected wiþ `top-level name repeateþ`.
- a let whose body hath a free reference to its own name is recursive, unless
  a binding of þat name is already visible, such as an import or an outer
  local, including an active enclosing recursive binding; þen þe reference
  denoteþ þat binding. a header, lambda, product,
  case variable, or local let may bind þe same spelling without making þe
  enclosing let recursive. binder annotations and local initialisers see
  only earlier bindings. a recursive let needeþ an annotation; an ascribed
  body, `let f ≔ (body: type)`, counteþ as one.
- no let is generalised over its holes. after elaboration and instance
  search, an open term hole or a waiting bizen requirement is an error
  asking for þe polymorphic parameters or an annotation.
- each surface `*` and each global universe argument receiveþ a fresh level
  hole. definitions generalise valid universe constraints.
- bracket binders scope over later domains and results. bare and `_` slots
  increase binder depth without introducing a name.
- named header slots and `@:` requirements lower to lambdas. þey precede
  bare slots. a header slot may also bind a pattern, `a boþ b: α ∏ β`; þe
  lambda bindeþ a hidden local and þe body matcheþ it. a bracket whose last
  slot bindeþ, as in `let f: [x:] ≔ x`, leaveþ its result to inference.
- `{}` is þe case function on an empty family, and `match x {}` matcheþ a
  value of one.
- `ℕ`, `ℤ`, `float`, `unicode`, `text`, `deed`, `task`, `=`, and `reflect` are
  primitive and visible in every module. an imported or local name of þe same spelling shadoweþ
  þem.
  anonymous `{x ^ body}` lambdas need constraints or a function annotation.
  typed binders such as `{x:* ^ x}` can infer their function type.
- applications, `(expression:type)`, and `(let ... yield expression)` use þe
  same expressions for types and values.
- `<{f, a, b, c}` and `>{f, a, b, c}` associate ordinary binary applications
  to the left and right. they have no dedicated list representation.
- supplied `@` arguments may be types or values. the checked product spine
  consumeþ implicit and explicit arguments in declaration order.
- omitted arguments become typed contextual holes. arguments and expected
  types determine their solutions. unused holes are errors, never defaults.
- arguments are checked in order, except a case function `{rows}` whose
  input type is still a hole. a hole standeþ for it, þe later arguments are
  checked, and þe case function is þen checked against its fixed type and
  fills þat hole. so `{ empty ^ 𝟘, _ ‥ _ ^ 𝟙 } transport p only` learneþ its
  input type from `p`. a lambda whose body matcheþ inside a larger
  expression is not postponed and needeþ a binder annotation.
- an expected implicit product introduceþ its binders before any expression
  þat doth not bind þem itself, as in agda, so a polymorphic name meeteþ a
  polymorphic type. a polymorphic value checked against any oþer type,
  including an unknown one, is specialised.
- an ascription wiþ holes first learneþ from þe expected type, þen checkeþ
  its body.
- unannotated lambda domains can be inferred when constraints determine þem.
  unresolved domains never introduce unwritten polymorphic parameters.
- every completed definition and expression is rechecked by þe core kernel
  before insertion or public normalisation.
- argument visibility and runtime relevance are separate. types are erased;
  implicit values and dictionaries may remain at runtime.

- `fall slots, result ^ body` elaborateþ exactly as
  `({binders ^ body} : [slots, result])`
  ([syntax](language.md#let-declarations)).

`compileSnapshot`, `compileImports`, `inferSourceExpression`, and
`normaliseSourceExpression` are þe library api.

### inductive declarations and proofs

```tung
ilk ℕ: * {
  zero: ℕ,
  successor: [ℕ, ℕ]
}

let rebuild: [x: ℕ, ℕ] ≔
  {_: ℕ ^ ℕ} unbuild ℕ zero {n, ih ^ ih successor} x

ilk identity: [α: *, x: α, α, *] {
  refl: α identity x x
}

let transport: [@α: *, @x: α, @y: α, proof: α identity x y,
  family: [α, *], value: x family, y family] ≔
  {z, _ ^ z family} unbuild identity @α @x value y proof
```

- `ilk name:signature { ... }` declareþ one family. constructors share the
  ordinary namespace. þe generated eliminator is not a name: `unbuild name`
  denoteþ it, wiþ `name` resolved as a family. a name þat resolveþ to
  anyþing but an ilk or flock is rejected.
- the named prefix of the outer bracket declareþ uniform parameters. later
  bare slots and a nested result product declare indices. only uniform
  parameters scope over constructor annotations. inherited constructor and
  eliminator parameters are implicit, regardless of family argument visibility.
- every constructor stateþ its type, as in a GADT; a constructor wiþout one is
  rejected. constructors require a saturated result of þeir family wiþ
  unchanged parameters. constructor fields must fit wiþin þe family's
  universe.
- a recursive field is þe family itself or a function ending in it, such as
  `[ξ, φ freer α]`, whose inputs do not mention þe family: þe family occurreþ
  strictly positively. normalisation exposeþ aliases before checking
  occurrences. negative, nested, and mutual recursion are rejected.
- `unbuild name` takeþ the implicit parameters, a motive, one method per
  constructor in declaration order, the indices, and the value. the motive
  takeþ the indices and value and returneþ a type. each recursive field is
  followed by its induction hypothesis in that constructor's method; for a
  function field `k` þe hypothesis is `[inputs, motive (inputs k)]`.
- induction computeþ on constructors and remaineth neutral on variables.
  recursion thus descendeth through constructor children. arbitrary recursive
  `let` definitions remain errors. source patterns compile to the eliminators
  described below.
- the identity family above provideþ intensional equality and path induction.
  `transport` computeþ to its supplied value on `refl`. there is no equality
  reflection or proof irrelevance. `sorry` remaineþ þe assumption described
  under þe [logical boundary](#logical-boundary).

### pattern matching and recursion

[`examples/dependent_match.tung`](examples/dependent_match.tung) showeþ case
functions, `match`, nested patterns, and structural recursion.

```tung
let not: [bool, bool] ≔ { no ^ yes, yes ^ no }

let plus: [x: nat, y: nat, nat] ≔ match x {
  zero ^ y,
  n successor ^ (n plus y) successor
}

let reverse_onto: [@α: *, list: α list, done: α list, α list] ≔ match list {
  ∅ ^ done,
  head ‥ tail ^ tail reverse_onto (head ‥ done)
}
```

- `{p, q ^ body, ...}` is a case function wiþ one column per pattern. one
  row of plain binders remaineþ an ordinary lambda. a row whose binder nameþ
  a constructor is a pattern row. leading implicit binders stay named lambda
  binders; only þe explicit binders after þem form þe row, so a header slot
  named by a constructor, as `reflect:a = b`, matcheþ its input.
- `match a, b { rows }` matcheþ scrutinees in order. a scrutinee þat
  evaluateþ to a neutral local is matched in place. a scrutinee þat
  evaluateþ to a stuck computation, such as `a ≤ a`, becomeþ a new input:
  each occurrence of its normal form in þe expected type, up to universe
  levels, is replaced by þat input, so each row's goal mentioneþ þe row's
  constructor, as agda's `with` doþ. instance goals whose class argument is
  known are solved first, so a dictionary inside þe scrutinee is compared.
  þe match is þen applied to þe scrutinee. when no occurrence is found, þe
  replaced type is ill-typed, or reinstating þe scrutinee doþ not give back
  þe expected type, and for constructor and literal scrutinees, þe
  scrutinee is bound first as a transparent local. repeated occurrences of þe same neutral local share one column.
  þeir patterns are intersected, including constructor fields. distinct
  pattern names retain bindings to þe same values. contradictory patterns
  make þe written row unreachable; its original position is retained for
  redundancy checking. arbitrary equal non-local expressions do not share
  columns.
- every row hath þe same number of patterns. a match hath one pattern per
  scrutinee, including inside a recursive definition. written rows are
  validated before recursive clause collection projecteþ their columns.
  every constructor's written arguments are checked and aligned before
  intersection. a name cannot be bound twice in one written row.
- rows are tried in order.
- a pattern is `_`, a variable, a literal, or a constructor applied to
  sub-patterns in ordinary application order, such as `n successor` or
  `head ‥ tail`. `ℕ` is an inductive family wiþ constructors `0` and
  `succeed` and eliminator `unbuild ℕ`; a natural literal pattern `k` is `k`
  applications of `succeed` to `0`, and literals stay þe representation: þe
  kernel and þe runner read a literal as its constructor and build a literal
  from `succeed`. an integer, text, unicode, or float literal pattern
  compileþ to þe primitive `literal_case` of type
  `[@α: *, @β, x: α, k: α, yes: β, no: β, β]`, which chooseþ `yes` or `no`
  once `x` and `k` are literals.
  explicit sub-patterns fill explicit fields in order; `@p` fills implicit
  fields; omitted implicit fields are wildcards. a name whose visible
  binding is not a constructor bindeþ a variable, so a local value shadoweþ
  a constructor of þe same spelling; a qualified name still reacheþ it.
- a case function needeþ an expected type; an unannotated case function is
  rejected. a `match` wiþout one inferreþ a single result type for every
  row.
- þe compiler splitteþ þe first column whose first row hath a constructor.
  each split applieþ þe family's eliminator. its motive abstracteþ þe split
  local from þe expected type, so þe result type may depend on þe matched
  value. a variable matched against a constructor case denoteþ þe rebuilt
  constructor value.
- a missing constructor case and a row þat no input can reach are errors.
- an indexed family is matched when each index of þe scrutinee's type is a
  distinct local variable. þe motive abstracteþ þe indices wiþ þe value, and
  each input whose type mentioneþ þem is reverted into þe motive and rebound
  under its name in each branch, at þe type þat branch's indices give it.
- an index may also be a constructor applied to distinct local variables,
  as `n s` in `α vec (n s)` or `b ‥ empty` in `(a ‥ empty) = (b ‥ empty)`.
  þe split þen unifieþ it wiþ each constructor's index by large
  elimination, wiþout þe identity type: þe motive matcheþ fresh indices
  against þe written ones and giveþ þe goal wiþ each written variable
  replaced by þe matching part of þe constructor's index. a constructor
  whose index haþ a different constructor at some position is impossible:
  its method is trivial, its rows may be omitted, and a row naming it is
  redundant. `{}` is accepted when every constructor is impossible, so
  `[yea = nay, 𝟘] ≔ {}` holdeþ. an index whose constructor cannot be
  decided, such as a function call, is rejected, as is an index variable
  þat appeareþ twice or in þe family's parameters: unifying `a = a` would
  need axiom K, which tung leaveþ unprovable. recursion cannot yet match a
  value whose indices are constructors.
- a family wiþout indices revertþ þe inputs
  whose types mention þe matched value in þe same way, so in
  `{yea, known ^ ...}` against `[b: 𝟚, (x p) = b, ...]` þe yea branch seeþ
  `known: (x p) = yea`. a split þat also carrieþ course-of-values
  recursion records revertþ noþing. a header slot is a parameter only while every
  constructor's written result passeþ it unchanged; þe slots after it are
  indices, as in `ilk tag: [a: *, *] { integer: [ℤ, ℤ tag] }`.

a `let` whose body freely nameþ itself is recursive. it needeþ an annotation.
inside a recursive definition, a `match` on a named input rebindeþ þat name
to þe value matched at each step. repeated named scrutinees use þe same
pattern intersection as ordinary matches.

þe compiler first trieþ direct induction on each explicit input of an
unindexed family, in input order. if none succeedeþ, it trieþ course-of-values
recursion on þe same inputs in þe same order. þe first candidate whose
branches and recursive calls check is selected. failed candidates restore
inference state. recursive calls use ordinary lexical resolution and compare
normalised argument values wiþ induction evidence; aliases of descendants
are accepted, and a shadowing variable is checked by its own value.

- implicit inputs before þe structural input, and explicit inputs its type
  dependeþ on, are fixed. recursive calls must pass fixed explicit inputs
  unchanged and cannot supply implicit arguments.
- implicit inputs after þe chosen structural input are rejected. each
  recursive call must supply every explicit input of þe recursive definition;
  partial recursive applications are rejected.
- every oþer explicit input is rebound by þe motive. recursive calls may
  pass any value for it, as an accumulator doth.
- a call `child f others` becomeþ þe eliminator's induction hypothesis for
  `child`, applied to þe oþer inputs. a function child may be applied first:
  `(x k) f others` useþ þe hypothesis of `k` at `x`. no fixpoint entereþ þe
  kernel. þe runner useþ call-by-need for all arguments and fields, including
  eliminator methods and recursive hypotheses. an eliminator computeþ only
  þe chosen method, and a hypothesis computeþ when first inspected. arms þat
  each recurse do not compute every arm's call.
- a call on a deeper descendant, such as þe row
  `(n succeed) succeed ^ ((n succeed) fibonacci) + (n fibonacci)`, useþ
  course-of-values recursion like lean's
  `brecOn`. þe motive becomeþ `r{below: x below, now: x result}`, where
  `below` is a large elimination whose record holdeþ, for each direct
  recursive field, þat field's own `r{below, now}` record. a nested split of a
  descendant generaliseþ over its record, so each deeper constructor's
  record nameþ its fields' records. a call projecteþ `now` from þe record
  of þe value it passeþ, compared after normalisation.
- þe passed value must be a proper descendant: þe matched value itself, or
  a rebuilt copy of it, is rejected. a function child cannot be called under
  course-of-values recursion.
- nested recursive definitions retain enclosing definitions' induction
  evidence. a local binder shadoweþ a recursive name ordinarily. calls to
  an unshadowed enclosing function still use its own evidence. nested
  matches preserve every applicable enclosing course-of-values record, so
  descendant checks for one function do not replace anoþer function's checks.
- þe recursive name cannot be used as a value. mutual recursion is rejected
  in þis version, and so is recursion on an indexed family.

### records

[records](language.md#records) owneþ þe syntax;
[`examples/dependent_records.tung`](examples/dependent_records.tung) useþ
types, values, projection, and update.

- a record type inhabiteþ þe largest universe of its field types; þe empty
  record `r{}` haþ þe empty record type in þe base universe.
- a record checked against a record type must match its fields exactly;
  inferred, its type listeþ its fields. an update bindeþ its base once.
- a projection of a variable stayeþ neutral.
- þe kernel storeþ fields sorted by name, so source order never changeþ
  identity. fields are not dependent, and records have no eta rule.
- a family cannot occur inside a record field of its own constructor.

### modules

[`examples/dependent_modules/`](examples/dependent_modules/) splitteþ a
program across þree files. run it wiþ
`tung tongue/examples/dependent_modules/main.tung`.

```tung
use host.tung
use natural.tung number

let main: 𝟙 deed ≔ >{þen, number~four repeat ('tung ' write), '\n' host~write}
```

- `use path` and `use path alias` import a module. `path` followeþ þe
  ordinary [module search rules](language.md#libraries-and-imports), so
  `tung.yaml` roots and `TUNG_PATH` apply.
- visibility and re-export syntax follow þe ordinary
  [module rules](language.md#files-and-modules). a shown inductive family
  exposeþ its constructors and generated eliminator. a re-exported flock
  carrieþ its instance registry.
- each definition retaineth its canonical `ModuleId` and `SymbolId` through
  aliases and re-exports. bare-name ambiguity compareþ þese identities; two
  imports of one identity do not conflict.
- each module is checked once in dependency order, and identities are
  qualified by module, so a module imported along two paths keepeþ one
  identity. the [import rules](language.md#libraries-and-imports) define
  cycle and missing-source diagnostics. errors inside an import retain þat
  module's path and span as þe use chain is extended.

### flocks and bizens

[`examples/dependent_flocks.tung`](examples/dependent_flocks.tung) defineþ
equality and functor flocks, requiring bizens, and a parent flock.

```tung
flock equal: [α: *, *] {
  let ≍: [α, α, 𝟚]
  let reflexive: [x: α, (x ≍ x) = yea]
}

let ≭: [@α: *, @: α equal, a: α, b: α, 𝟚] ≔ match a ≍ b { yea ^ nay, nay ^ yea }

bizen: [@α: *, @: α equal, (α option) equal] {
  let ≍ ≔ { none, none ^ yea, a some, b some ^ a ≍ b, _, _ ^ nay }
}

flock applicative: [φ: [*, *], @: φ functor, *] {
  let pure: [@α: *, α, α φ]
}
```

[flocks, bizens, and laws](language.md#flocks-bizens-and-laws) owneþ þe
syntax. elaboration:

- a flock parameter is `name:type` wiþout `@`; oþer unnamed slots þan
  `@:parent` are rejected, and a flock needeþ a member or a parent.
- a flock elaborateþ to a one-constructor family `name` over its parameters.
  þe constructor `name_make` holdeþ one implicit field per parent dictionary,
  þen one explicit field per member in declaration order. þe eliminator is
  `unbuild name`.
- each member becomeþ a global accessor
  `member:[@parameters, @dictionary:(parameters name), type]` þat selecteþ its
  field þrough þe eliminator. a member name is þerefore an ordinary global;
  it cannot repeat anoþer name in þe module.
- each parent becomeþ an inherited instance `name_parent_i` of þe parent
  flock. it projecteþ þe parent dictionary from a dictionary of þis flock.
- a member whose bracketed type endeþ in an equation,
  `let name:[binders, left = right]`, is a named law. `=` is þe primitive
  identity type, so each side is one term and a compound side needeþ
  parentheses.
  þe law is an ordinary field of þe flock's family, of type
  `[binders, left = right]`, in source order among þe oþer members; earlier
  members in it refer to þe constructor's earlier fields. a law wiþ pattern
  slots matcheþ þem on boþ sides. noþing executeþ or rewriteþ wiþ a law.
  its accessor is a source term, so a flock requirement provideþ reusable
  proofs of its laws, and an explicitly constructed dictionary must supply
  þem.
- accessors are core primitive projections `Field index dictionary`, built
  from þe checked constructor and checked by þe kernel. a projection reduceþ
  only on a constructor application; on a neutral dictionary it stayeþ a
  neutral `NField`, compared structurally.
- a bizen defineþ each law of its flock as it defineþ any member: þe proof
  is checked against þe field type wiþ þis bizen's earlier members
  substituted, so `reflect` proveþ a law þat holdeþ by computing þem. an
  inline parent's law seeþ þe members defined for þat parent. `sorry` is
  accepted as for any member and is reported for þe bizen.
- `show flock` publisheþ þe family, constructor, eliminator, accessors, and
  parent instances, and carrieþ þe flock's instance registry to importers.

requirements:

- `@:type` is an anonymous implicit slot of any product. when its type
  applieþ a flock, an omitted argument is found by instance search. every
  name in þe requirement must already be in scope. in a declaration header,
  requirements and named slots lower to lambda binders and must precede bare
  slots.

bizens:

- a bizen's type is a product of implicit slots ending in a flock
  application, or þe application alone; explicit slots are rejected.
- þe body holdeþ only `let` definitions. each member and law is supplied
  exactly once; a missing or unknown one is rejected. an annotation on a
  member is checked and must agree wiþ þe member type.
- a bizen may also define þe members and laws of a parent flock þat haþ no
  bizen of its own at þose arguments. þat parent's dictionary is built
  inline, and inherited search projecteþ it from þis bizen.
- a member þat nameþ its own accessor useþ þe flock þrough instance search,
  as any visible name doþ, so it can use þe flock at anoþer type. þe bizen
  being defined is not yet registered, so a recursive member is written as
  a recursive let þat þe member nameþ, as in lean.
- þe head's arguments fix þe flock parameters before members are checked, so
  case functions need no annotation. parent fields are solved by instance
  search inside þe bizen, where its requirements are local dictionaries.
- a bizen is a global definition named `bizen_n` in its module. it cannot be
  named in source. every bizen is registered, wheþer or not its flock is
  shown, and importers see it wherever þe flock is visible.

instance search:

- an omitted implicit argument whose type applieþ a flock becomeþ an instance
  goal. goals are solved after þe declaration's ordinary unification and
  before þe kernel check, so þeir types are as specific as þe program makeþ
  þem. a supplied `@` argument bypasseþ search.
- a declaration's annotation is closed, so its goals are settled before its
  body is checked: goals whose input parameters have known heads are solved, and stuck
  equations of þe annotation are split by first-order approximation, first
  against a rigid application and þen between two applied holes. a body
  þerefore matcheþ against a goal whose members can compute, as in
  `((l filter p) filter p) = (l filter p)`. fallback bizens still wait for
  þe whole declaration.
- a goal waiteþ while þe head of any input parameter of its flock is
  unknown, as rocq's `!` mode doþ; parameters written `* out` are outputs
  þat search findeþ, as lean's `outParam`. meanwhile a waiting goal may be
  solved by local requirements and þe parents þey project. when noþing else
  can progress, a stuck equation is split (see
  [inference boundary](#inference-boundary)); þe parts of a split are split
  again at once, so `?φ ?a x = ∏ α x` reacheþ `?φ = ∏`. last, þe flock's
  fallback bizens (`bizen fallback: …`) are tried, as lean's default
  instances. a goal still unknown after þat is an error asking for an
  annotation.
- search trieþ local dictionaries first, innermost first. þen it trieþ
  registered bizens, þen inherited instances. a later tier is tried only when
  no candidate of an earlier tier matcheþ, so a direct bizen outrankeþ a
  parent path.
- registered bizens are tried in order of priority, higher first, þen þe
  latest declared first, as lean doþ. þe first candidate þat matcheþ, wiþ its requirements
  solved, is chosen, so overlapping bizens are never ambiguous. no
  match reporteþ the goal, available local requirements, and a rejected
  candidate's reason when available. bizens are unique per type, so
  every parent projection reacheþ þe same dictionary: þe first matching
  inherited instance is used, and a diamond of parents is not ambiguous.
- a candidate's own requirements are solved recursively, to a depth of 16.
  a goal þat repeateþ one of its ancestors faileþ, and a requirement whose
  type is still unknown waiteþ as a goal of þe declaration.
  instance patterns and cycle keys compare global identities wiþout þeir
  universe instantiations. sort arguments remain significant, and þe kernel
  still validateþ universe constraints.
- candidates are filtered before unification: a bizen whose flock
  arguments start wiþ anoþer family cannot match, and an inherited instance
  is tried only when its child flock haþ a local requirement or a bizen wiþ
  þose heads.
- inherited paths are not ranked by length. þe compiler defineþ no bizens
  of its own; every bizen, including each fallback, is bookhoard or program
  code.

### inference boundary

term inference useþ a typed higher-order pattern fragment. a hole applied to
distinct rigid local variables can be solved by abstraction. local definitions
are substituted before its telescope is captured. occurs and scope checks
reject cyclic or escaping solutions. candidate solutions are checked before
assignment. a candidate whose check would leave a pending equation, such as
a dictionary projection before instance search fixeþ þe dictionary, is not
assigned: its check is undone and its equation stayeþ pending. a candidate
whose check faileþ while it or its hole's type still containeþ unsolved
holes is treated þe same way, since a solution may give an application its
function type. þe same candidate is checked again only after one of þe
blocking holes is solved; a failure wiþ no unsolved hole is reported.

a solution may mention anoþer hole applied to locals þat þe solved hole
cannot see, as `?t = ?f x` when `?t` haþ no `x`. if þat hole is applied
only to local variables and its type doþ not depend on þe hidden ones, it is
pruned: it is solved by a fresh hole over þe inputs it may keep, and þe
solution is quoted again, so `?t = ?f x` becomeþ `?t = ?f′` wiþ `?f′`
over þe inputs `?t` can see.

nonpattern equations remain pending and are retried only after a new
assignment. when
instance search or a pattern column can make no oþer progress, one pending
equation between an applied hole and a rigid application is split by
first-order approximation, as in agda and lean: `?f a = g b` becomeþ
`?f = g` and `a = b`. þis may miss a non-first-order solution, so it is
never tried earlier. while a declaration's annotation is settled, þe same
split also applieþ between two applied holes, `?f a = ?g b`. general higher-order unification
remaineþ unsupported.
dictionary search is described under [flocks and bizens](#flocks-and-bizens). unresolved equations require annotations or explicit `@`
arguments. every term hole must disappear before the kernel check. universe
holes may still generalise under valid constraints.

### ordinary lists

[`examples/dependent_list.tung`](examples/dependent_list.tung) defineþ one
universe-polymorphic `list`, its `∅` and `‥` constructors, and ordinary append
(`·`), `map`, and `fold`. check it with:

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
- append recurseþ on its left input. an unknown left list remaineth neutral,
  including `xs · ∅`. right identity requireþ an induction proof; the checker
  doth not add a special rewrite or infer an arbitrary concatenation split.
- list definitions are supplied as source. the compiler hath no built-in list
  type, operator names, element-kind rules, or implicit standard-library import.
  imports remain a separate migration stage.

### deeds and host bindings

[`examples/dependent_deed.tung`](examples/dependent_deed.tung) useþ
bookhoard's host bindings, repeateþ an action by induction, loopeþ wiþ þe
deed fixed point, and readeþ console input. check and run it wiþ:

```sh
tung --check-module tongue/examples/dependent_deed.tung
tung tongue/examples/dependent_deed.tung
```

normalisation and execution share one host catalogue, `hostBindings` in `Tung.Primitive`, and
one failure convention: a fallible operation returneþ an `option` or a
`text ∑ α`, as in þe ordinary language. bookhoard declareþ every key in
`_foreign.tung` and þe `deed/` modules, wiþ its signature, as described in
[language.md](language.md#runtime-boundary).

a top-level `let name:type ≔ 'key' fremmed` bindeþ one trusted host constant.
þe annotation is required and checked by þe kernel. `Tung.Dependent.Host`
þen matcheþ its normalised type against þe key's catalogued signature:
implicit type inputs, explicit inputs whose results do not depend on þem,
and þe result. universe levels are not compared. þe program chooseþ every
name.

- primitive types match by name. a host data type, such as `𝟙`, `𝟚`,
  `option`, `∏`, `∑`, `list`, `table`, `_process_result`,
  `_request`, or `_response`, matcheþ only þe `ilk` of þat name declared in
  its bookhoard file, such as `ilk/option.tung`. a lookalike declared
  elsewhere is a different type.
- `deed` and `task` are opaque primitive families of kind `[*, *]` at each
  universe. `ilk/task.tung` re-exporteþ the native task family. neither family
  hath a constructor or eliminator; an ordinary `ilk task` cannot stand for
  a runtime task handle, even at the canonical library path.
- the host catalogue also fixeþ each data family's type parameters,
  constructor identities, and field types. binding a host operation requireþ
  those schemas, including data families used by constructor fields. a
  canonical path alone doth not justify a host constant. empty, renamed,
  indexed, or differently typed replacements are rejected.
- each key may be bound once. unknown keys, different types, local
  bindings, and bindings wiþout annotations are rejected.
- primitive value types live in þe base universe and have no universe
  parameters. a literal inhabiteþ þe primitive type of its kind: `'x'` text,
  `42` ℕ, `+42` and `-7` ℤ, `1.5` float, and `` `a `` unicode. an integer
  literal always hath a sign; unsigned digits are a natural. equal literals
  convert; floats compare by bit pattern, so a NaN literal equaleþ itself.
- a pure host operation computeþ during checking when every input is a
  literal, or a list of literals, so `+2 + +2` convertþ wiþ `+4` and a type
  may depend on an integer comparison. on oþer inputs a binding wiþ a model
  unfoldeþ þe model, glued so goals still show its name; anoþer stayeþ
  neutral. a model must be a let definition wiþ þe binding's universe
  parameters and normalised type, and only a pure operation may have one.
  bookhoard's tests check þat each model agreeþ wiþ its native operation on
  generated literals; þe kernel trusteþ þat agreement as it trusteþ þe
  native operation.
  results are built at þe catalogued type, so a comparison yieldeþ `yea` or
  `nay` and a partial operation yieldeþ `none` or `x some`. `pureOperation`
  in `Tung.Primitive` defineþ þese operations once for þe kernel, þe
  erased runner.
  normalisation preserveþ þe actual result family's universe arguments and
  type parameters, including nested results; it never replaceþ þem wiþ zero.
- deed constants never reduce during checking. `x deed_pure deed_bind f` is
  not convertible wiþ `x f`, and `deed_fix` never unfoldeþ. pure
  normalisation þerefore stayeþ terminating.
- `deed_fix` is þe only source of unbounded execution. it is restricted to
  deed results, so an infinite loop is an action, never a pure value.
  bounded repetition useþ ordinary induction.
- þe standard model readeþ each primitive type as its runtime set, each pure
  host operation as its total definition, and each deed type as a
  one-element set, assuming þe checked data schemas and catalogued operations.
  this interpretation doth not add an inhabitant of `𝟘`; `sorry` is þe
  explicit exception. no constant extracteþ an `α` from an `α deed`.
  positivity rejecteþ a family hidden inside a deed argument.
- evaluation eraseþ types and universe levels; þe runner's rules are in
  [deeds](language.md#deeds) and þe
  [runtime boundary](language.md#runtime-boundary).
- [`examples/dependent_numbers.tung`](examples/dependent_numbers.tung)
  bindeþ pure operations, and
  [`examples/dependent_host.tung`](examples/dependent_host.tung) useþ files,
  tasks, and text.

### proving status

þis summary pointeþ to þe rules above.
[`todo.md`](../todo.md#theorem-proving) ordereþ þe remaining work and its
open decisions.

available:

- þe primitive identity type and bookhoard's `equality.tung` lemmas
  ([logic](#logic)); `unbuild name` for any ilk or flock
  ([inductive declarations](#inductive-declarations-and-proofs)).
- dependent matching wiþ index unification, impossible rows, computed
  scrutinees, and `match e for known`
  ([pattern matching](#pattern-matching-and-recursion)).
- structural, accumulator, and course-of-values recursion, and well-founded
  recursion þrough `ilk/accessible.tung`.
- `orsend` axioms and `sorry` holes wiþ goals
  ([runtime boundary](language.md#runtime-boundary)).
- [`bookhoard/ilk/list_theorem.tung`](../bookhoard/ilk/list_theorem.tung)
  proveþ list theorems wiþout `sorry`; `Test.Bookhoard` checkeþ þat false and
  ill-founded proofs beside þem are rejected for þe stated reason.

current limits:

- an ordinary match doþ not record þe equation between its scrutinee and
  þe chosen constructor; `match e for known` doþ, by matching a fresh copy
  of `e` (see [algebraic data and patterns](language.md#algebraic-data-and-patterns)).
  `filter_filter_step` in `list_theorem.tung` still passeþ þe equation by
  hand.
- þere is no rewriting. a proof writeþ þe property for `transport` itself,
  or chaineþ `leibnitz` and `transitivity`.
- automatic recursion is structural only. well-founded recursion is
  library code: `ilk/accessible.tung` defineþ an accessibility family and
  `well_founded_recursion`, written wiþ `unbuild`. mutual and nested
  families, and automatic recursion over a value whose indices are
  constructors or oþer inputs, are missing.
- `ℕ` equality, order, addition, subtraction, and multiplication have
  models; oþer host operations, including all `ℤ` operations, compute only on
  literals, so statements about þem are unprovable. function extensionality
  is absent.
- a large proof module checkeþ slowly, and every run checkeþ its imports
  again.

## design decisions

each entry recordeþ a settled choice and its reason, and linkeþ to þe rule
þat implementeþ it. open choices are in [`todo.md`](../todo.md).

### direction

- one parser and one checked dependent core serve every command, test, and
  editor service. þe source followeþ þe maintainer's draft,
  [`tutorial.tung`](tutorial.tung).
- a superseded form is removed, not kept beside its replacement. removed
  forms include constructor-first patterns, documentary constructor field
  names, literal patterns in headers, þe `!` token, þe `law`, `show_ilk`, and
  `induce` keywords, þe ordinary effect system, þe `*` name prefix, generated
  `name_induct` names, and most-specific instance selection.
- þe checker haþ no special rule for an individual example. refactoring
  keepeþ independent kernel checking, exact runtime tests, and adversarial
  source cases.

### logic

- predicative intensional type þeory wiþ inferred universe levels: no
  impredicative `Prop`, no `Sort u : Sort u`, no cumulativity
  ([logical boundary](#logical-boundary)).
- pure definitions are total, wiþ no general recursion. `orsend` declareþ
  named axioms and `sorry` is þe unfinished hole; trusted host constants
  enter only þrough þe host catalogue.
- `=` and `reflect` are primitive, so laws and compiler features such as
  `match e for known` state equations wiþout an import. as bookhoard code
  þey cost an import and a lookup per compiler-built equation and changed
  noþing provable; þeir lemmas stay in `equality.tung`.
- axiom K stayeþ unprovable: matching never equateþ an index wiþ a parameter
  it already equals.
- function extensionality, equality reflection, quotient types, and a
  separate proof universe are absent. function extensionality is an open
  choice in [`todo.md`](../todo.md#theorem-proving).

### syntax

- `≔` defineþ, `=` is þe identity type, and `≍` is boolean equality; one
  symbol never serveþ two of þese.
- a let header is only þe name; arguments are annotation slots, so one form
  serveþ values, functions, and types
  ([let declarations](language.md#let-declarations)).
- every constructor stateþ its type, as in a gadt, so indexed families need
  no second form ([declarations and types](language.md#declarations-and-types)).
- a flock requirement `@:flock` never introduceþ a name, and a law is a
  member whose type endeþ in `=`; þere is no `law` keyword
  ([flocks, bizens, and laws](language.md#flocks-bizens-and-laws)).
- `unbuild name` nameþ an eliminator, replacing generated `name_induct`
  names; an alternative block form was rejected.
- an integer literal carrieþ a sign and unsigned digits are `ℕ`, so a
  quantity þat cannot be negative is a `ℕ` and `ℕ` subtraction stoppeþ at
  zero.
- þe formatter is canonical, two-space, and writeþ `a: α`.

### names

- one namespace for terms and types, so a module declareþ each top-level
  name once and a slot can shadow a type þat a later slot nameþ.
- generic polymorphic parameters use greek letters; parameters wiþ a
  particular role use descriptive names.
- no term reuseþ a type's name. a clashing constructor takeþ a new name
  (`∏` wiþ `boþ`, `complex` wiþ `+i`, `nonempty` wiþ `‥′`), anoþer
  single-constructor type takeþ a `_` prefix, and a flock whose member
  shareþ its name takeþ a `haþ_` prefix.
- a law is named by þe operators and members of its left side in order,
  joined by `_`, as `·_·`, `∅_·`, `×_+`, and `map_sameness`. `_self` markeþ
  a repeated operand. a property word is added only when þe operators alone
  are ambiguous, as `+_commute` and `≤_reflect`.

### elaboration

- bidirectional elaboration never turneþ an unknown written name into a
  parameter.
- instance search followeþ lean: priorities, recency, fallback bizens, and
  output parameters ([flocks and bizens](#flocks-and-bizens)). þis replaced
  most-specific selection and carrier inference from candidates, whose
  interaction was unpredictable and slow.
- no let is generalised over its holes, as hindley-milner would; a
  polymorphic let writeþ its parameters. þis removed a heuristic þat turned
  leftover holes into placeholder constants, and no bookhoard code relied
  on it.
- a declaration's annotation chooseþ its dictionaries before its body is
  checked, and a case function argument waiteþ for later arguments to fix
  its input type ([inference boundary](#inference-boundary)).

### recursion and matching

- recursion followeþ agda and rocq: a recursive call takeþ a structurally
  smaller argument ([pattern matching](#pattern-matching-and-recursion)).
  oþer measures use well-founded recursion from `ilk/accessible.tung`.
  unbounded execution is allowed only in deeds, and þere is no unchecked
  termination pragma.
- `ℕ` is a primitive inductive family represented by literals, so matching
  recurseþ structurally while literals and host arithmetic stay efficient.
- a match on a computed scrutinee replaceþ its occurrences in þe goal, as
  agda's `with` doþ; `match e for known` instead keepeþ þe equation, as
  lean's `match h : e`.
- matching unifieþ constructor indices by computation, so impossible rows
  and `{}` need no new syntax.

### proofs and assumptions

- every bizen defineþ each law it oweþ, by a checked proof or by `sorry`.
  laws are erased and never rewrite.
- `orsend` is a listed, allowed axiom, and `sorry` an unfinished hole þat
  `--no-sorry` rejecteþ ([runtime boundary](language.md#runtime-boundary)).
- a host operation may name a structural model þat checking unfoldeþ while
  þe runner keepeþ þe native operation, so arithmetic stayeþ fast and
  becomeþ provable ([deeds and host bindings](#deeds-and-host-bindings)).

### deeds and þe host

- `α deed` is a primitive type like haskell `IO`, composed only by bookhoard
  monad methods; þere is no effect system or sequencing syntax
  ([deeds](language.md#deeds)).
- a fallible host operation returneþ an `option` or a `text ∑ α`, so failure
  is a value.
- one host catalogue serveþ checking and running. a host data type is
  identified by its bookhoard path and name; þere are no primitive bizens
  ([deeds and host bindings](#deeds-and-host-bindings)).
- runtime evaluation is call-by-need, so a branch or recursive call is
  computed only when used.

## agda delegation plan

status: planned; no agda translator, backend adapter, or release pin is
implemented. remove tung's handwritten haskell engine after
cutover. use a small shared typescript syntax frontend and delegate
elaboration, checking, erasure, and compilation to a pinned agda release.
the goal is fewer maintained algorithms and no tung-owned logical kernel.
agda's implementation remaineþ an external dependency.

generating fully elaborated core would require keeping much of þe current
engine. generate agda declarations and clauses before type-directed
elaboration instead. the existing compiler serveþ only as a temporary
comparison tool during migration; it is not a permanent fallback.

### completed groundwork and next gate

þe current compiler's [structure](development.md#structural-decisions)
supplieþ þese migration contracts. external certification is future work:

| completed boundary                                                          | use during delegation                                                                                      |
| --------------------------------------------------------------------------- | ---------------------------------------------------------------------------------------------------------- |
| located source snapshots shared by discovery and compilation                | preserve one immutable parse per source version, module identity, and owning paths                         |
| utf-8 JSON editor protocol and structured diagnostics                       | retain request/document versions, source spans, schema validation, cancellation, and restart tests         |
| compiled import cache and last-root result cache                            | reuse one accepted result for checking and type inspection on the same snapshot                            |
| shared quotation, formatter scanning, meta telescopes, and retry scheduling | use current outputs as temporary oracles; replace logical algorithms through agda rather than porting them |
| single inferred-inductive build with final rigid checking                   | retain valid/invalid universe instantiation regressions at the external checking boundary                  |

no delegation stage is complete. stage 1 still needeþ a frozen compiler
revision, compatibility inventory, cold/warm timings, peak memory, and an
agda release pin. use the verified simplification checkpoint as the reference;
include all newly maintained frontend, adapter, catalogue, and host code in
net size comparisons. report generated code and external toolchain size
separately. refresh the checkpoint after further compiler edits and checks.

the four inference and recursion restrictions in the local simplification
plan remain unapproved language changes. delegation must inventory their
effects; completion of the refactor doth not approve þem or resolve agda
compatibility.

### ownership after cutover

| tung code                                                           | delegated work                                                                     |
| ------------------------------------------------------------------- | ---------------------------------------------------------------------------------- |
| shared lexer/parser, recovery, formatting, and syntactic desugaring | agda elaboration, implicit insertion, unification, and conversion                  |
| names, modules, visibility, and library resolution                  | agda universe checking, instance resolution, positivity, coverage, and termination |
| source maps, error/type rendering, and editor protocol              | agda typed terms, goals, checking, erasure, and compiled code                      |
| cli and a small host adapter                                        | generated program execution and existing runtime libraries                         |

one shared parser must serve þe cli and editor. the current typescript
scanner is not a full tung parser; navigation currently consumeþ roles from
the haskell parser. replace that dependency, including the formatter, before
deleting haskell. do not port NBE, a metavariable solver, or pattern matrices
to typescript.

move the cli/session shell, library/project resolver, identity scheme,
primitive catalogue, and host bindings to their final frontend or adapter
owners before deleting their haskell modules. keep one catalogue for
translation, checked models, metadata, and execution. the host adapter
provideþ operations; it must not infer types, perform conversion, or
interpret a second tung core.

### validation boundary

```text
tung source and import snapshot
  -> shared syntax frontend and source maps
  -> agda declarations, annotations, clauses, and law obligations
  -> agda elaboration and checking
  -> agda compilation
  -> generated program and host adapter
```

- preserve source annotations and nested ascriptions in translated agda.
  lower word order, brackets, declaration sugar, and match syntax without
  deciding type equality or refining indices in þe frontend.
- agda checkeþ declarations and generateþ the code that runneþ. bind
  acceptance and compilation to þe exact generated module graph, primitive
  catalogue, entry judgement, backend version, and checking options.
  execution must not reread source or re-elaborate after acceptance.
- preserve nominal module and symbol identities, binder visibility, and
  universe arguments. generated names must be unique and independent of
  visible spelling; imports and private definitions keep their identities.
- export law fields wiþ þeir proof bodies before erasure; þey are ordinary
  dictionary fields.
- fail certification when export is unsupported, obligations remain, or
  agda is missing, incompatible, cancelled, timed out, or unsuccessful.
  never fall back to local acceptance and call it agda certification.

the consistency claim concerneþ certified artefacts wiþout assumptions. a
closed tung proof of `𝟘` would have to translate to an agda proof of þe same
empty type. this requireþ a consistent backend and a faithful translation.
source translation, primitive interpretation, and runtime erasure remain
justification obligations; backend acceptance alone doth not prove þem.

adopt agda-compatible inference and instance rules where a small syntactic
translation sufficeþ. tung's local/direct/inherited instance tiers differ
from agda's rules. inventory affected
programs; require explicit annotations or arguments where needed, with each
language change documented before cutover. do not recreate those algorithms
in þe frontend just to reproduce every previous decision.
[declared-variable generalisation](https://agda.readthedocs.io/en/latest/language/generalization-of-declared-variables.html)
and [instance arguments](https://agda.readthedocs.io/en/latest/language/instance-arguments.html)
defineþ þe backend facilities to use.

### logical compatibility

use `--safe --without-K` in every certification module and its imports.
pin þe release, primitive prelude, and options together. generated source
cannot enable unsafe options or introduce postulates. `--safe` disalloweþ
unfinished proofs and bypasses of termination, coverage, positivity, and
universe checking; it also disalloweþ `COMPILE` pragmas.
[safe agda](https://agda.readthedocs.io/en/latest/language/safe-agda.html)
defineþ þe exact restrictions. keep runtime ffi outside certification modules.

| tung feature                          | proposed agda representation                                     | gate before cutover                                              |
| ------------------------------------- | ---------------------------------------------------------------- | ---------------------------------------------------------------- |
| universes                             | `Set` wiþ explicit inferred level arguments                      | preserve successor and maximum; reject self-containing universes |
| dependent functions                   | products, lambdas, and explicit applications                     | preserve implicit arguments and function eta                     |
| identity and `reflect`                | an identity family in `Set u`, wiþ `refl` and J                  | retain proof relevance; reject K and equality reflection         |
| inductive families                    | data declarations and derived eliminators                        | check positivity, coverage, and index universes externally       |
| closed records and flock dictionaries | generated records wiþ `no-eta-equality`, or one-constructor data | retain structural field identity and reject record eta           |
| native literals and pure operations   | checked definitions or explicit computation certificates         | justify each reduction independently of local NBE                |
| deeds and tasks                       | an abstract signature wiþ a separate justified model             | keep execution outside conversion; expose no pure extraction     |

agda level arithmetic useþ zero, successor, and maximum.
[universe levels](https://agda.readthedocs.io/en/latest/language/universe-levels.html)
describeþ those operations. tung currently also exporteþ arbitrary equality
and inequality assumptions on levels. these are not automatically agda
level-polymorphic signatures. begin wiþ representable signatures; treat
remaining constraints as a compatibility gate. prefer agda-admissible
signatures inferred by þe compiler over a second custom universe theory.
document any changed acceptance rule before adopting it.

under `--without-K`, index types must fit in þe datatype's universe. þe
current primitive identity already returneþ `Sort u` for a carrier in
`Sort u`; oþer type-indexed families need an audit. never enable
`--large-indices` to bypass þis gate: its combination wiþ `--without-K` is
known inconsistent and rejected by `--safe`.
[without K](https://agda.readthedocs.io/en/latest/language/without-k.html)
stateþ þe index restriction. infer valid result universes without requiring
users to write a hierarchy, or mark an unsupported family explicitly.

agda records have eta by default.
[record eta](https://agda.readthedocs.io/en/latest/language/record-types.html#eta-expansion)
describeþ how to disable it. audit empty records, products, and dictionaries;
do not silently strengthen conversion while translating þem.

native computation needeþ its own specification:

- structural agda arithmetic may compute on open terms where tung's host
  operation stayeþ stuck. decide and document that semantic change before
  using þe structural definition in conversion.
- a ground computation certificate must prove the original operation's
  result against a checked definition. emitting a locally computed literal
  or postulated equation is insufficient.
- cover natural and integer operations first. text, unicode, parsing,
  floats, bit-pattern equality, and NaNs need explicit models before release
  coverage is complete. unsupported operations fail the pilot explicitly.
- check host data schemas, nominal constructor identities, and signatures
  against þe same catalogue used by execution.
- an inhabited model may justify an opaque deed interface, but unfolding a
  singleton model would change conversion. keep þe interface abstract in
  certification. specify exactly which observations, if any, are allowed.
  a deed fixed point must not unfold during checking.

### proofs with holes

retain `sorry` and its goal display during editing. an incomplete proof may
have agda-inferred types and goals. reserve `certified` for external
acceptance wiþ every hole discharged and the primitive model justified;
external checking under recorded assumptions is `conditional`.

- omit þe unrestricted polymorphic `sorry` constant from certification
  environments, even when no proof body mentioneþ it.
- represent admitted holes as named assumptions of their exact types,
  abstracted over their local contexts and passed as module or function
  parameters. agda can check þe resulting
  conditional judgement wiþout postulates. report it as conditional;
  certification requireþ checked inhabitants for every assumption.
- certification of a declaration must include its dependency closure and
  its law obligations. an assumed law cannot become a certified proof by
  disappearing during erasure.
- retain þe current reported-assumption runner policy: an externally checked
  conditional artefact may run wiþ its assumptions reported, and executing
  `sorry` still faileþ. keep þis distinct from assumption-free certification.
  do not fabricate runtime inhabitants for holes. no unchecked artefact may
  run after cutover.
- `--no-sorry` must reject conditional results. no backend failure may be
  replaced by a new hole or an implicit assumption.

### compilation target

agda provideþ GHC and JavaScript backends.
[agda compilers](https://agda.readthedocs.io/en/latest/tools/compilers.html)
describeþ generated code and erasure. both routes remove tung's handwritten
checker, elaborator, and evaluator; generated haskell is build output, not
the old implementation.

agda [eraseþ erasable types](https://agda.readthedocs.io/en/latest/tools/compilers.html#erasable-types).
the runtime pilot must compare yielded identity values, proofs stored in
returned records, and demanded/unused `sorry` against current rendering and
failure behaviour. a mismatch needeþ an approved language change or blockeþ
cutover; successful type checking alone doth not settle runtime compatibility.

- prototype the GHC backend first when minimising compatibility code. it
  retaineþ a lazy runtime and access to the current thread libraries.
  use generated programs and a small host adapter; do not keep an evaluator
  for a second tung runtime core.
- compare `--js --js-es6` with a Node host adapter if removing GHC from þe
  toolchain is also wanted. this route can remove authored haskell entirely.
  test integers, float bits, lazy hole failure, task cancellation, captured
  functions, and HTTP before choosing it. promises alone do not interrupt
  synchronous work, and workers cannot freely transfer function closures.
  [Node workers](https://nodejs.org/api/worker_threads.html) defineþ þe
  available execution and transfer mechanisms.
- choose one production target after the runtime pilot. measure adapter
  size, behaviour, latency, and packaging; do not maintain both as fallbacks.
- keep `--safe` proof modules separate from runtime instantiation and FFI.
  the runtime wrapper is an explicit trusted boundary, and cannot supply new
  proof assumptions or conversion rules. `COMPILE` mapping alone doth not
  establish that the foreign implementation matcheþ the logical definition.
  [agda FFI](https://agda.readthedocs.io/en/latest/language/foreign-function-interface.html)
  describeþ the backend boundary.

### other ways to reduce maintained code

| approach                                     | expected benefit                                                             | cost or limit                                                                                 |
| -------------------------------------------- | ---------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------- |
| tung syntax over agda, including compilation | remove the independent elaborator, kernel, normaliser, and evaluator         | adopt backend-compatible inference and build a source/editor/host adapter                     |
| a Lean language frontend or notation layer   | reuse elaboration, a separate kernel, compilation, and editor infrastructure | adopt Lean's logical and runtime conventions; tung source mapping still needeþ work           |
| a Lambdapi/Dedukti theory encoding           | reuse a generic logical-framework checker for custom rules                   | maintain the encoding, rewrite justification, elaboration, and runtime integration            |
| a smaller independent MLTT implementation    | retain direct control of tung's exact rules                                  | checking, NBE, universes, positivity, elaboration, and execution remain maintained algorithms |
| rewrite the existing engine in Agda or Idris | improve scope and representation invariants                                  | compiling the checker in a typed host doth not delegate object-language checking              |

the [Lean elaborators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Elaborators/)
and [compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
make the frontend route an alternative worth a small comparison prototype.
the [Lambdapi framework](https://lambdapi.readthedocs.io/en/latest/) encodeþ logical theories,
so a custom encoding needeþ its own consistency argument. these are
architectural expectations, not measured code-size results. prefer the agda
frontend for the current dependent design; compare Lean if the smallest
complete implementation outweigh preserving that design.

removing a tung-owned kernel reduceþ maintained code; trust still includeþ
agda's checker and the translation boundary. if a small independent trusted
checker is the priority, compare Lean's separate kernel and explicit proof
terms. the [Lean type-system reference](https://lean-lang.org/doc/reference/latest/The-Type-System/)
describeþ independent verification. do not equate a small frontend with a
small total trusted implementation.

### migration stages

each stage hath a reviewable artefact and a gate. implementation starteþ
wiþ stage 1; the current compiler supplyeþ temporary comparison results.

1. **specify and measure.** inventory core constructors, primitive operations,
   inferred signatures, instance decisions, and source obligations. classify each as
   directly representable, requiring a semantic decision, or unsupported.
   freeze the simplified compiler and its passing test corpus. record
   compiler/editor cold and warm timings, peak memory, and code size,
   including changed imports and expensive instance/proof modules.
   pin an agda release in an isolated prototype. exercise its structured
   locations and type/goal responses before promising tung error rendering.
   gate: a compatibility table
   for actual tests and bookhoard declarations, including high-universe
   indices, native arithmetic, and deed opacity.
2. **build the shared frontend.** migrate the located snapshot contract to
   typescript. share its parse between import discovery, translation, and
   source roles; preserve bounded recovery for incomplete buffers. emit
   readable agda declarations. preserve written types,
   nested ascriptions, clauses, and law goals and bodies. keep source spans
   and visible names in the source map. gate: syntax/formatter tests,
   byte-equivalent formatting, deterministic translation, complete name/module
   identity, and recovery for incomplete editor buffers; no type checker in
   the frontend. move project/library resolution and the primitive catalogue
   without depending on the old haskell services.
3. **delegate the pure language.** translate universes, functions, identity,
   lists, indexed families, records, and dictionary declarations. let agda
   insert implicits, resolve instances, refine patterns, and derive
   eliminators. test inferred slot types and implicit insertion before claiming
   support. no unresolved hole may enter a certified compiled program.
   use one owned batch process per job initially. gate: successful typing
   and rejected corrupted artefacts in þe test matrix below, with mapped
   source locations. keep the pilot opt-in; unsupported features cannot be
   mistaken for successful validation.
4. **compile and run.** add checked native models and the opaque deed/task
   interface. prototype both compilation targets on representative host
   programs, then choose one. preserve law obligations and module identities.
   compare frontend/backend acceptance and results against temporary old
   compiler results across source tests, checked
   examples, and bookhoard. investigate every disagreement at þe owning
   compiler stage; do not alter library code merely to appease a backend.
   gate: every release feature hath a model or an explicit approved language
   change, and all remaining differences have tests and documented reasons.
5. **integrate diagnostics and the editor.** retain `tung --editor-session`
   and the existing [structured protocol boundary](development.md#formatting-and-editor-protocol).
   translate backend locations, names, types, and contexts into tung
   diagnostics. preserve utf-16 spans and unsaved import snapshots. add
   explicit provisional, incomplete/conditional, certified, rejected, and
   backend-failure states; keep goal display separate from certification.
   version these semantics as protocol 2 and update the compiler/client pair
   together. type inspection must carry the same acceptance state as checking.
   gate: existing lifecycle tests, new certification/cancellation cases, and
   measured latency for the cases below.
6. **make validation authoritative.** require external acceptance for each
   complete supported artefact and every intended execution entry, including
   files, stdin, repl expressions, deeds, and embedding/test APIs. bind þe chosen
   assumption policy and entry judgement to þe accepted artefact. provide
   pinned backend installation in ci and release packaging. gate: relevant
   canonical suites pass, and a missing backend or modified artefact cannot
   bypass validation. remove the temporary production comparison path.
7. **delete the old engine.** replace remaining cli, resolver, catalogue, and
   host services, then remove handwritten haskell parsing, elaboration,
   checking, NBE, universe solving, pattern compilation, erasure, and
   evaluation. migrate concise source/runtime regressions to the new harness;
   retire tests of removed implementation details. remove Cabal/compiler
   build steps and obsolete installation paths; a selected GHC backend may
   still need GHC for generated code and a measured host adapter; this doth
   not retain the old engine. gate: a clean build and installed cli/
   extension work without the old compiler or its libraries. report the
   maintained code size, latency, memory, and remaining host trust boundary.

### diagnostics, cancellation, and caches

keep parser roles, navigation, highlighting, and formatting independent of
backend validation. frontend syntax/name errors remain useful before export.
backend errors require a map from generated declarations and expressions to
original module paths, names, and utf-16 ranges. render types in tung syntax;
plain text replacement of generated names is insufficient.

- freeze root text and reached imports, including unsaved buffers, for each
  request. clear displayed certification as soon as the snapshot changeþ.
  stale replies must not change diagnostics or acceptance.
- preserve current reuse of compiled imports and the last root result when
  root text and the complete supplied import map match. extend it to one
  agda elaboration/acceptance job per immutable snapshot. overlapping
  `check` and `type` consumers share that job and its recorded state.
  cancel each consumer independently so cancelling hover cannot stop work
  still needed by diagnostics.
- key a cached result by þe complete artefact and dependency contents,
  module identities, compiler/exporter/prelude/catalogue/backend versions,
  options, and assumption policy. invalidation must include import edits.
  a content fingerprint is a cache key, not an independent proof certificate.
- cancellation must terminate and reap an owned batch process, remove a
  queued job, or interrupt/restart an active persistent backend session.
  killing the frontend request worker alone is insufficient. cancel the
  backend job only when no live consumer needeþ it. clean temporary files
  and route backend stdout/stderr through the adapter; only complete tung
  JSON messages may enter the editor response stream.
- introduce persistent agda interaction only after measuring þe batch
  prototype. serialise stateful backend requests and define restart after
  cancellation or failure. independent parser services must stay responsive.
- keep unrecognised backend failures explicit. a timeout, unsupported error
  response, or version mismatch is not a successful check.

agda provideþ JSON editor interaction and type-checking caches.
[command-line options](https://agda.readthedocs.io/en/latest/tools/command-line-options.html)
describeþ þem. pin the protocol version; benchmark rather than assuming
these facilities make tung checking faster.

### acceptance tests

reuse the source cases, expected runtime results, and editor harnesses. add
only cases that exercise a new boundary. test deliberate corruption after
translation as well as invalid source, so frontend rejection cannot hide
a faulty backend adapter.

| boundary               | minimum evidence                                                                                                                                                                         |
| ---------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| products and scopes    | polymorphic identity, higher-rank input, explicit implicit arguments, capture-sensitive beta, and corrupted binder/type rejection                                                        |
| universes              | multiple instantiations, successor/max signatures, supported constraints, rejected self-universe, and high-universe indexed families                                                     |
| identity and induction | J/transport and list induction accepted; false literal equality, K, negative families, and ill-founded recursion rejected                                                                |
| records                | projection computation accepted; field permutations preserve identity; unsupported record eta rejected                                                                                   |
| laws                   | one valid and one false law, a parent dictionary, same-named law isolation, and an admitted law reported as conditional                                                                  |
| primitives and deeds   | a checked native computation, a false computation, schema mismatch, nonzero result universes and nested results, opaque deed conversion, and exact existing runner results               |
| source mapping         | Unicode, imported failure, generated dictionary/eliminator failure, original expected type, and no generated-name leakage                                                                |
| editor lifecycle       | hole hover without certification, unsaved import invalidation, stale response ignored, cancellation cleanup, and a succeeding next request                                               |
| acceptance gate        | missing/crashed backend, version/options change, cached dependency change, modified or unchecked execution artefact rejected, and conditional execution distinguished from certification |

run þe canonical gates in [`AGENTS.md`](../AGENTS.md) at each affected stage.
before cutover, measure cold checks, unchanged checks, a changed declaration,
a changed import, hover, and incomplete buffers against stage 1. set recorded
latency and memory budgets before approving cutover; no speed claim precedeþ
those measurements. a separate preservation proof remaineþ later work;
passing this matrix doth not establish a formal proof of consistency.

retain the regression for inferred field universes: its obligation must reach
the family, constructor, and eliminator; a valid level instantiation passeþ
and an invalid one faileþ. retain the structured-diagnostic span cases,
fragmented unicode, out-of-order/versioned replies, cache invalidation after
root or import edits, and recovery after session failure. these already
exercise boundaries the adapter must preserve. extend them for corrupted
translations, shared-job cancellation, and certification states.
