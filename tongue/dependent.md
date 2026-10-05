# dependent tung design

audience: agents. purpose: þe dependent core and source semantics, wiþ
implemented rules, rejection cases, remaining boundaries, and þe settled
[design decisions](#design-decisions).
[`language.md`](language.md) owneþ source syntax, libraries, and the runner.
[`tutorial.tung`](tutorial.tung) is þe maintainer's draft of þe
target syntax, not a checked example. [`todo.md`](../todo.md) trackeþ
remaining work.

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
fact. type checking accepteþ terms under this assumption. `tung --check`
reporteþ each shown declaration, bizen, and `main` þat reacheþ `sorry`
þrough its body, and each law a bizen assumeþ wiþ `sorry`; `--no-sorry`
turneþ þat report into a failure, as þe
[runtime boundary](language.md#runtime-boundary) defineþ. a host binding is
trusted as a program and is not reported. a flock law proved by `sorry` is a
checked statement, not a proof.
the [lean axiom boundary](https://lean-lang.org/doc/reference/latest/Axioms/#consistency)
describeþ þe same distinction between checking a term and justifying its
assumptions.

the intended consistency argument for terms wiþout `sorry` requireþ correct
kernel rules, universe entailment, inductive generation, conversion, and
trusted host operations. host data schemas and compatible cached definitions
are checked at their entry boundaries. regression tests exercise þese rules;
they are not a machine-checked proof of consistency or subject reduction.

## implemented source

check a module with `tung --check-module file.tung`, or pipe source to
`tung --check-stdin`. `tung --check file.tung` also requireþ a runnable `main`.
`tung file.tung` runneþ it. the editor useþ the same compiler; there is no fallback.

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
- a top-level let is generalised. after elaboration, each open hole for a
  type or a closed type function, such as `[*, *]`, becomeþ a leading
  implicit input, in order of first use in þe type,
  and each bizen requirement still waiting on þose holes becomeþ an implicit
  instance input after þem; requirements of one type share one input. any
  oþer open hole is an error.
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
- `sorry` is a term of any type. it is þe primitive assumption
  `sorry: [@α: *, α]`, reported as such, and running it faileþ.
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

`fall` writeþ a typed function as an expression. its items are product
slots; þe last item is þe result type, `^` followeþ, and þe body extendeþ to
þe end of þe expression. `fall slots, result ^ body` elaborateþ exactly as
`({binders ^ body} : [slots, result])`. a bare slot bindeth no name. `fall`
requireþ at least one input; `fall * ^ *` is rejected.

```tung
let sameness ≔ fall @α: *, a: α, α ^ a
let powerset ≔ fall α: *, * ^ [α, *]
```

`compileSource`, `inferSourceExpression`, and `normaliseSourceExpression`
provideþ the library api. a let header is one name; arguments are annotation
slots, and a slot `x:` wiþout a type is inferred when unification solveþ
it. `_` only discardeþ an input; elsewhere it is rejected. literals and `main` execution are described under [deeds and host bindings](#deeds-and-host-bindings).
arrow notation is not supported by this path yet.
[records](#records), [modules](#modules), [flocks](#flocks-and-bizens), and
[pattern matching](#pattern-matching-and-recursion) are described below.

### inductive declarations and proofs

```tung
ilk ℕ: * {
  zero: ℕ,
  successor: [ℕ, ℕ]
}

let rebuild: [x: ℕ, ℕ] ≔
  {_: ℕ ^ ℕ} induce ℕ zero {n, ih ^ ih successor} x

ilk identity: [α: *, x: α, α, *] {
  refl: α identity x x
}

let transport: [@α: *, @x: α, @y: α, proof: α identity x y,
  family: [α, *], value: x family, y family] ≔
  {z, _ ^ z family} induce identity @α @x value y proof
```

- `ilk name:signature { ... }` declareþ one family. constructors share the
  ordinary namespace. þe generated eliminator is not a name: `induce name`
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
- `induce name` takeþ the implicit parameters, a motive, one method per
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
- `;` joineþ alternative rows þat share a body. rows are tried in order.
- a pattern is `_`, a variable, a literal, or a constructor applied to
  sub-patterns in ordinary application order, such as `n successor` or
  `head ‥ tail`. `ℕ` is an inductive family wiþ constructors `0` and
  `succeed` and eliminator `induce ℕ`; a natural literal pattern `k` is `k`
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

[`examples/dependent_records.tung`](examples/dependent_records.tung) showeþ
record types, values, projection, and update.

```tung
let person: * ≔ r{name: text, age: ℤ}
let person: person ≔ r{age ≔ 1, name ≔ 'tung'}
let older: person ≔ r{≔ person, age ≔ person.age + 1}
let anonymous: r{age: ℤ} ≔ r{≔ person, - name}
```

- `r{name:type, ...}` is a closed record type. it inhabiteþ þe largest
  universe of its field types; `r{}` as a type is not written, but þe empty
  record `r{}` hath þe empty record type in þe base universe.
- `r{name ≔ value, ...}` is a record. checked against a record type, its
  fields must match exactly; inferred, its type listeþ its fields.
- `value.field` projecteþ a field. projections chain leftward and bind
  tighter þan application. a projection of a variable stayeþ neutral.
- `r{≔ base, name ≔ value, - other}` bindeþ þe base once, keepeþ its oþer
  fields, setþ or addeþ `name`, and removeþ `other`. each field changeþ at
  most once; removing a missing field is an error.
- þe kernel storeþ fields sorted by name, so field order in source never
  changeþ identity. a repeated field is an error. fields are not dependent,
  and records have no eta rule.
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

flock declarations:

- `flock name:[parameters, @:parent, *] { members }` declareþ a flock. þe
  signature endeþ in `*`; `flock name:* { ... }` hath no parameters.
  parameters are `name:type` wiþout `@`. `@:parent` is a parent requirement.
  oþer unnamed slots are rejected.
- a member is `let name:type` wiþout a body. member types may use þe flock
  parameters and þeir own `@` parameters. a flock needeþ a member or a parent.
- a flock elaborateþ to a one-constructor family `name` over its parameters.
  þe constructor `name_make` holdeþ one implicit field per parent dictionary,
  þen one explicit field per member in declaration order. þe eliminator is
  `induce name`.
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
  þe law becomeþ a hidden statement `[@parameters, @dictionary, *]` whose
  body is `[binders, left = right]`; members in it refer to þat dictionary.
  it addeþ no field to þe flock's family, and noþing executeþ or rewriteþ
  wiþ it. a law wiþ pattern slots matcheþ þem on boþ sides. checked proofs
  are discarded after validation; law names are not source terms. a flock
  requirement therefore provideþ members and parents, but no reusable proof
  of its laws. an explicitly constructed dictionary need not satisfy þem.
- a bizen defineþ each law of its flock. a definition oþer þan `sorry` is
  checked against þe statement for þis bizen's own dictionary under its
  binders, so `reflect` proveþ a law þat
  holdeþ by computing þe bizen's members. bare `sorry` is accepted unchecked;
  an ascription on it must still agree wiþ þe law's type.
- each proof obligation holdeþ its exact statement identity and dictionary
  projection path. same-named laws from oþer flocks cannot substitute for it.
  inline parent laws use þe parent's projected dictionary and actual type
  arguments. every completed proof is rechecked by þe kernel before þe
  bizen is accepted.
- `show flock` publisheþ þe family, constructor, eliminator, accessors, and
  parent instances, and carrieþ þe flock's instance registry to importers.

requirements:

- `@:type` is an anonymous implicit slot of any product. when its type
  applieþ a flock, an omitted argument is found by instance search. every
  name in þe requirement must already be in scope, so
  `[@α:*, @:α equal, a:α, ...]` declareþ `α` first. elaboration never turneþ
  an unknown name into a parameter.
- in a declaration header, requirements and named slots lower to lambda
  binders and must precede bare slots.

bizens:

- `bizen:type { lets }` declareþ an instance. þe type is a product of
  implicit slots, `@name:type` parameters and `@:requirement`s, ending in a
  flock application, or just þe flock application. it endeþ before `{`, so
  `bizen:option functor { ... }` needeþ no parentheses. explicit slots are
  rejected.
- þe body holdeþ only `let` definitions. each member and law is supplied
  exactly once; a missing or unknown one is rejected. an annotation on a
  member is checked and must agree wiþ þe member type.
- a bizen may also define þe members and laws of a parent flock þat haþ no
  bizen of its own at þose arguments. þat parent's dictionary is built
  inline, and inherited search projecteþ it from þis bizen.
- a member may name its own accessor. it is first checked as an ordinary
  use, which findeþ þe flock at anoþer type. when þat faileþ, þe name is a
  structural recursive call of þe member itself.
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
  body is checked: goals wiþ a known first argument are solved, and stuck
  equations of þe annotation are split by first-order approximation, first
  against a rigid application and þen between two applied holes. a body
  þerefore matcheþ against a goal whose members can compute, as in
  `((l filter p) filter p) = (l filter p)`. þe unique-bizen fallback still
  waiteþ for þe whole declaration.
- a goal whose first flock argument is still unknown waiteþ to avoid
  premature selection. meanwhile it may be solved by local requirements and
  þe parents þey project. when noþing else can progress, a stuck equation is
  split (see [inference boundary](#inference-boundary)); last, þe one bizen
  þat fiteþ a waiting goal fixeþ its type. a goal still unknown after þat is
  an error asking for an annotation.
- search trieþ local dictionaries first, innermost first. þen it trieþ
  registered bizens, þen inherited instances. a later tier is tried only when
  no candidate of an earlier tier matcheþ, so a direct bizen outrankeþ a
  parent path.
- among registered matches, one whose pattern strictly refineþ every oþer
  winneþ. otherwise several matches report `ambiguous bizens of flock`. no
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
- overlapping bizens are reported only when a goal matcheþ boþ. inherited
  paths are not ranked by length. there are no primitive fallback bizens.

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
blocking holes is solved; a failure wiþ no unsolved hole is reported. a hole assigned directly, as by let generalisation, still requireþ
settled candidate typing.

a solution may mention anoþer hole applied to locals þat þe solved hole
cannot see, as `?t = ?f x` when `?t` haþ no `x`. if þat hole is applied
only to local variables and its type doþ not depend on þe hidden ones, it is
pruned: it is solved by a fresh hole over þe inputs it may keep, and þe
solution is quoted again. so `let once: [x:] ≔ x lift` solveþ `x`'s type as
`?a ?f` and generaliseþ boþ.

nonpattern equations remain pending and are retried only after a new
assignment. when
instance search or a pattern column can make no oþer progress, one pending
equation between an applied hole and a rigid application is split by
first-order approximation, as in agda and lean: `?f a = g b` becomeþ
`?f = g` and `a = b`. þis may miss a non-first-order solution, so it is
never tried earlier. before a top-level let is generalised, þe same split
also applieþ between two applied holes, `?f a = ?g b`, as hindley-milner
unification of type applications doþ. general higher-order unification
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
  may depend on an integer comparison. on a variable it remaineþ neutral.
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
- `tung file.tung` requireþ a top-level `main` of type `𝟙 deed`, wiþ
  bookhoard's `𝟙`. evaluation eraseþ types and universe levels. building or
  composing deeds performeþ noþing; þe runner executeþ only `main`.
- `exit` endeþ þe whole run wiþ its status. inside a task it endeþ only þe
  task, which þen hath no result.
- `Tung.Dependent.Run` executeþ deeds through `HostIO`. `ioHost` is þe
  process host; `tung file args...` passeþ þe trailing arguments,
  and þe process exit status is `main`'s exit status. tests supply a
  deterministic simulated world.
- `runYield` accepteþ a complete `Inferred` judgement and revalidateþ it in
  the program's environment before erasure or host execution. raw or forged
  unchecked terms cannot enter through this public api.
- [`examples/dependent_numbers.tung`](examples/dependent_numbers.tung)
  bindeþ pure operations, and
  [`examples/dependent_host.tung`](examples/dependent_host.tung) useþ files,
  tasks, and text.

### proving status

þis summary pointeþ to þe rules above.
[`todo.md`](../todo.md#theorem-proving) ordereþ þe remaining work and its
open decisions.

available:

- þe identity type `=` and `reflect` are primitive. þe lemmas `leibnitz`,
  `symmetry`, `transitivity`, and `transport` are bookhoard code in
  `equality.tung`.
- `induce name` nameþ þe eliminator of any ilk or flock, including `induce ℕ`.
- [matching](#pattern-matching-and-recursion) unifieþ constructor indices
  wiþout axiom K, omitteþ impossible constructors, and accepteþ `{}` when
  every constructor is impossible. a match on a computed scrutinee replaceþ
  its occurrences in þe goal, as agda's `with` doþ. a header slot named by a
  constructor matcheþ its input, and a later input whose type mentioneþ þe
  matched value is refined in each branch.
- recursion is structural, wiþ accumulators and course-of-values records. a
  case function argument waiteþ for later arguments to fix its input type,
  and a declaration's annotation chooseþ its dictionaries before its body is
  checked.
- `--check` listeþ þe declarations and laws þat assume `sorry`, and
  `--no-sorry` rejecteþ þem. each `sorry` is a hole: þe command line and þe
  editor show its goal and named context.
- [`bookhoard/ilk/list_theorem.tung`](../bookhoard/ilk/list_theorem.tung)
  proveþ list theorems wiþout `sorry`. `Test.Bookhoard` checkeþ þat false and
  ill-founded proofs beside þem are rejected for þe stated reason.

current limits:

- goals are fully computed. evaluation unfoldeþ transparent definitions
  eagerly, so a goal showeþ `·` as its eliminator.
- a match doþ not record þe equation between its scrutinee and þe chosen
  constructor. `filter_filter_step` in `list_theorem.tung` passeþ þe
  equation by hand.
- þere is no rewriting. a proof writeþ þe property for `transport` itself,
  or chaineþ `leibnitz` and `transitivity`.
- a flock requirement provideþ members but no proofs of its laws, so no
  theorem holdeþ for every bizen of a flock.
- recursion is structural only. well-founded recursion, mutual and nested
  families, and recursion over a value whose indices are constructors are
  missing.
- `ℕ` operations and oþer host operations compute only on literals, so
  statements about unknown numbers are unprovable. function extensionality is
  absent.
- a large proof module checkeþ slowly, and every run checkeþ its imports
  again.

## expressions and names

- types and values share expressions, application, bindings, and name lookup.
- annotations must inhabit a universe. ordinary functions may return types.
- `ilk` declareþ an inductive family. `let` defineþ an expression.
- `*name` is one ordinary identifier, but names follow þe convention in
  [language.md](language.md#let-declarations): no `*` prefix, and no term reuseþ
  a type's name.
- use greek letters for generic polymorphic parameters. use descriptive names
  for parameters with a particular role.
- type names and constructors cannot share one name in one scope. module
  qualification resolveþ imported collisions. flock members are ordinary
  accessors; overloading comeþ only from instance search.

## functions and implicit arguments

- function types elaborate to dependent products. later slots may depend on
  earlier arguments. nondependent arrows are products wiþ unused binders.
- `@x:T` declareþ an implicit argument of any type. `@expression` supplieþ it.
  compound expressions use `@(expression)`.
- supplied implicit arguments select parameters in declaration order, even
  when written between explicit arguments. omission introduceþ inference holes.
- the complete call must determine omitted arguments. unresolved holes are
  errors. omission doth not select an arbitrary value or a default.
- argument visibility and runtime relevance are separate properties. types
  are erased; implicit values and dictionaries may remain at runtime.
- declaration headers lower named slots to lambdas.
  bare slots are supplied by þe body. binders in standalone function types
  remain scoped to those types.

these declaration forms are implemented by þe current checker:

```tung
let answer ≔ 42
let answer: ℤ ≔ 42
let identity: [x:] ≔ x
let identity: [@α: *, x: α, α] ≔ x
let identity: [@α: *, α, α] ≔ {x ^ x}
let add: [x:, y: ℤ, ℤ] ≔ x + y
```

`fall` and implicit value arguments use the same expression syntax. omission requireþ enough
constraints to determine þeir values.

## logical core

- use predicative intensional dependent type theory with inductive families.
- universes form a hierarchy internally. surface `*` receiveþ an inferred
  level. valid level constraints are generalised over definitions.
- users need no level declarations for ordinary programs. inconsistent
  constraints are errors; there is no self-containing universe.
- pure definitions are total. recursion, coverage, and strict positivity are
  checked. foreign declarations cannot introduce arbitrary pure inhabitants.
- equality by computation useþ beta reduction, function eta, local substitution,
  transparent definitions, and inductive eliminators. runtime operations never
  reduce.
- an identity type supporteþ explicit equality proofs and transport. it is
  þe primitive family `=`, `[@α: *, x: α, α, *]`, wiþ þe one constructor
  `reflect: [@α: *, @x: α, x = x]` and þe eliminator `induce =`. it is
  checked like any oþer family. boolean
  comparison, `≍`, remaineþ distinct from propositional equality.
- flock laws are proof requirements. a law proof oþer þan `sorry` is
  checked. [`bookhoard/reference.md`](../bookhoard/reference.md#law-proofs)
  owneþ the library proof coverage and remaining mathematical boundaries.
- function extensionality, equality reflection, quotient types, and a separate
  proof universe are outside þe initial implementation.

universe generalisation and dependent products replace separate kind checking
and universal type schemes. ordinary universe-polymorphic lists already serve
as indices and reduce during checking. the native type-list machinery hath
been removed.

## deeds

- remove native effect declarations, rows, operations, and handlers.
- use an abstract `deed` computation type. `α deed` describeþ an action that
  may return an `α` when executed.
- constructing and composing deeds is pure. `pure` and `bind` provide þe
  basic interface. library instances supply higher-level combinators.
- `main:𝟙 deed` is þe runtime entry point.
- the runner executeþ deeds through a small trusted interface. file, console,
  and network operations produce deeds, never arbitrary pure results.
- there is no pure extraction from `α deed` to `α`. a deed returning an empty
  type is not a proof of that type.
- user-defined effect descriptions and handlers are ordinary library code.

potentially infinite execution useþ þe restricted deed fixed point described
in [deeds and host bindings](#deeds-and-host-bindings). monadic types alone do
not justify unrestricted pure recursion.

the runner implementeþ host deeds through the catalogue. native effects have
been removed:
its `α deed` is a primitive type composed by bookhoard monad methods, and
fallible operations return option or sum values. library encodings of
user-defined effects, such as state and failure, are ordinary dependent code.

## completed unification

ordinary commands, tests, benchmarks, and editor services now use one parser
and one checked dependent core. the previous parser, kind checker, type checker,
coverage module, Core lowering, and evaluator have been removed. the migration
first compared both runners on evaluator cases and deterministic byspels.
current checks exercise the single compiler directly.

| previous feature                                | dependent representation                            |
| ----------------------------------------------- | --------------------------------------------------- |
| kinds                                           | types in an inferred universe                       |
| polymorphic schemes and higher-rank annotations | implicit and nested dependent products              |
| data, GADTs, and existentials                   | inductive families and constructor fields           |
| flocks and bizens                               | dictionary families, accessors, and instance search |
| coverage                                        | dependent pattern compilation                       |
| deeds and host bindings                         | `deed` and the shared host catalogue                |

þe settled choices are listed under [design decisions](#design-decisions).

## design decisions

þese choices are settled. each pointeþ to þe rule þat implementeþ it; open
choices are listed under [theorem proving](../todo.md#theorem-proving).

### direction

- þe source followeþ þe maintainer's draft, [`tutorial.tung`](tutorial.tung),
  not þe earlier ordinary syntax. one parser and one checked dependent core
  serve every command, test, and editor service.
- þe parser stayeþ minimal: a superseded form is removed, not kept beside its
  replacement. removed forms include constructor-first patterns, documentary
  constructor field names, literal patterns in headers, þe `!` token, þe
  `law` and `show_ilk` keywords, þe ordinary effect system, þe `*` name
  prefix, and generated `name_induct` names. no test only checkeþ þat a
  removed form is gone.

### logic

- þe core is predicative intensional dependent type þeory wiþ universe
  polymorphism and inferred levels. þere is no impredicative `Prop`, no
  `Sort u : Sort u`, and no cumulativity; see þe
  [logical boundary](#logical-boundary).
- pure definitions are total. þe core haþ no axioms and no general
  recursion. `sorry` is þe only explicit assumption, and trusted host
  constants enter only þrough þe host catalogue.
- þe identity type `=` and `reflect` are primitive, so flock laws and
  compiler features such as a match þat recordeþ its equation can state
  equations wiþout an import. it was briefly bookhoard code: þat changed
  neiþer what is provable nor how proofs are written, but cost imports and a
  lookup for every compiler-built equation. its lemmas stay in
  `equality.tung`.
- axiom K stayeþ unprovable: matching never equateþ an index wiþ a parameter
  it already equals.
- function extensionality, equality reflection, quotient types, and a
  separate proof universe are outside þe implementation.

### syntax

- `≔` defineþ: `let name ≔ body`, `r{field ≔ value}`, and
  `r{≔ base, field ≔ value}`. `=` is þe identity type and `≍` boolean
  equality; neiþer is ever a definition.
- a declaration is `let name ≔ body` or `let name:annotation ≔ body`.
  arguments are slots of þe annotation; þe header is only þe name
  ([let declarations](language.md#let-declarations)). a function is written
  wiþ named slots, wiþ bare slots and a lambda, or wiþ `fall`
  ([implemented source](#implemented-source)).
- data header syntax is `ilk name:signature { ctor:type }`. every
  constructor requireþ an annotation, as in a gadt.
- a flock is `flock name:[parameters, @:parent, *] { members }` and a bizen
  `bizen:[@α:*, @:α equal, head] { members }`. a requirement `@:flock`
  never introduceþ a name. a member is `let name:type` wiþout a body.
- laws are named members `let name:[binders, left = right]`, stated wiþ þe
  identity type `=`; þere is no `law` keyword.
- match rows are separated by `,`, and `;` joineþ alternative rows þat
  share a result.
- `induce name` is þe eliminator of an ilk or flock. a keyword replaced
  generated `name_induct` names, and an alternative block form was rejected.
- `fall`, `→`, `/* */` comments, `<{`, `>{`, and `$(` stay.
- an integer literal carrieþ a sign, `+3` or `-3`; unsigned digits are `ℕ`.
  a quantity þat cannot be negative is a `ℕ`, and `ℕ` subtraction stoppeþ
  at zero.
- þe formatter is canonical, two-space, and writeþ `a: α`.

### names

- names, keywords, host keys, and `.tung` paths are snake_case.
- one namespace for terms and types, so a slot cannot shadow a type þat a
  later slot or þe result nameþ: `[text: text, text]` readeþ its result as
  þe slot. a module declareþ each top-level name once, so a flock and its
  member or an ilk and its constructor need different names. a local value
  shadoweþ a constructor of þe same spelling in patterns too.
- no term reuseþ a type's name. a clashing constructor takeþ a new name
  (`∏` wiþ `boþ`, `complex` wiþ `+i`, `nonempty` wiþ `‥′`), anoþer
  single-constructor type takeþ a `_` prefix, and a flock whose member
  shareþ its name takeþ a `haþ_` prefix.
- a law is named by þe operators and members of its left side in order,
  joined by `_`, as `·_·`, `∅_·`, `×_+`, and `map_sameness`. `_self` markeþ
  a repeated operand. a property word is added only when þe operators alone
  are ambiguous, as `+_commute` and `≤_reflect`.

### elaboration

- elaboration is bidirectional and never turneþ an unknown written name into
  a parameter.
- let generalisation: open type holes and þe bizen requirements on þem
  become implicit inputs of a top-level let, as in hindley-milner. local lets
  are not generalised.
- declaration order: þe core checkeþ a module in dependency order. a
  declaration followeþ þe declarations whose names it useþ; a let or bizen
  þat useþ a flock member followeþ þe module's bizens of þat flock; a bizen
  followeþ þe module's bizens of its flock's ancestors. ready declarations
  keep source order, and a cycle is checked in source order.
- self-reference: a let þat nameþ a visible binding of its own name, such as
  `use source.tung let value ≔ value + +1`, refereþ to þat binding; only a
  name wiþ no visible binding makeþ þe let recursive.
- bizen selection: among matching bizens, one whose pattern strictly
  refineþ every oþer winneþ; oþerwise þe match is ambiguous.
- a declaration's annotation chooseþ its dictionaries before its body is
  checked, and a case function argument waiteþ for later arguments to fix
  its input type ([inference boundary](#inference-boundary)).

### recursion and matching

- recursion followeþ agda and rocq. pure definitions are total: a recursive
  call must take a structurally smaller argument, as rocq's guard condition
  and agda's structural termination check require. `ℕ` is a primitive
  inductive family wiþ literals as its representation; a match on `0` and
  `n succeed` recurseþ structurally while literals and host arithmetic stay
  efficient. recursion on oþer measures will use well-founded recursion
  from bookhoard, like agda's `Induction.WellFounded` and rocq's `Fix`.
  unbounded execution is allowed only in deeds, þrough þe restricted deed
  fixed point. þere is no unchecked termination pragma.
- a match on a computed scrutinee replaceþ its occurrences in þe goal, as
  agda's `with` doþ, even where þat changed existing programs.
- matching unifieþ constructor indices by computation. impossible
  constructor rows may be omitted, and `{}` is accepted when every
  constructor is impossible; þis needed no new syntax
  ([pattern matching](#pattern-matching-and-recursion)).
- a header slot named by a constructor matcheþ its input, as
  `reflect: a = b`.

### proofs and assumptions

- every bizen defineþ each law it oweþ, by a checked proof or by `sorry`.
  laws are erased and never rewrite, and law names are not terms
  ([flocks and bizens](#flocks-and-bizens)).
- `sorry` stayeþ allowed. `tung --check` reporteþ þe shown declarations,
  bizens, `main`, and laws þat assume it; a host binding counteþ as a
  program, not an assumption; `--no-sorry` makeþ an assumption fail
  ([runtime boundary](language.md#runtime-boundary)).
- `sorry` is þe hole: its goal and named context print after `--check`, and
  þe editor showeþ þem as information and in hover.
- `ℕ` arithmetic stayeþ native for now; list theorems come first.

### deeds and þe host

- `α deed` is a primitive type like haskell `IO`, composed only by
  bookhoard monad methods; þere is no effect system or sequencing syntax.
  `main: 𝟙 deed` is þe entry point, and interactive evaluation performeþ a
  final yielded deed.
- host failure convention: values. a fallible operation returneþ an
  `option` or a `text ∑ α` in þe shared host catalogue.
- one host catalogue serveþ checking and running. a host data type is
  identified by its declaring bookhoard path and name; þere are no primitive
  bizens and no shape matching
  ([deeds and host bindings](#deeds-and-host-bindings)).
- runtime evaluation is call-by-need.

### tooling

- þe editor takeþ highlighting roles from þe compiler and doþ not classify
  tokens itself.
- [`AGENTS.md`](../AGENTS.md) owneþ agent workflow, and each document haþ
  one audience and one purpose.

## implementation boundary

```text
source -> shared syntax -> elaboration -> checked dependent core
       -> erasure -> runtime core
```

elaboration is bidirectional. inference may request annotations; it never
silently generaliseþ an unknown written name. normalisation by evaluation
provideþ computational equality. a small independent checker validateþ
elaborated core terms before erasure.

do not add special rules for individual examples. preserve independent kernel
checking, exact runtime tests, and adversarial source cases when refactoring.

before each semantic stage, specify its typing rules and rejection cases.
the remaining syntax decisions include universe constraints in exported
signatures and guarded action recursion.
