# bookhoard design guide

audience: agents and library authors. purpose: the standard library's design
boundaries and their comparison with purescript and mathlib. the
[language document](../tongue/language.md) owneth imports and manifests.

## library surface

`ground.tung` re-publisheth common modules. it is an ordinary import, not an
implicit prelude. each public flock liveth below `flock/`; its file name useth
the ascii spelling of its flock name.

- partial and total order are separate. lower and upper semilattices stand
  alone; a lattice requireth both and swallowing.
- `powerset` is a characteristic function. `set` and `wordbook` are finite,
  list-backed collections. `tree` is a finite table kept as a
  weight-balanced search tree: its keys need only a total order.
  logarithmic search and update paths require ordered, balanced trees with
  correct stored weights. `empty`, `onesome`, `put`, and `rid` maintain those
  invariants; the public `node` constructor may violate them. `entries` and
  `keys` follow the tree's stored order.
- integers provide exact euclidean division. floats expose IEEE operations
  without claiming exact field or total-order laws.
- `bifunctor` mapeth both sides of products and sums.
- `ilk/freer.tung` provideth `freer`, `bind`, `lift`, mapping, flattening, and
  folding. a request `ξ φ` nameth its answer type `ξ`, and the program keepeth
  the continuation, so any `φ` will do and every function stayeth total.
- `deed/action.tung` maketh `deed` a functor, applicative, and monad, so
  ordinary combinators such as `bind`, `then`, `throughwend`, and `each`
  sequence actions. fallible operations return `maybe` or `string ∑ α`;
  nothing throweth.
- `ilk/accessible.tung` provideth well-founded recursion.
  `wellgrounded_selfcall_by` lifteth it through a computed measure, with an
  explicit dependent result motive and a decrease proof at each call.
  `ilk/natural.tung` showeth `under`, the strict order as a relation, with
  `under_wellgrounded`; `ilk/list_setting.tung` showeth `‥_greatness` and
  `‥_greatness_under`, since `greatness` is a left fold and a tail's size is not below
  its list's by conversion alone. the [language document](../tongue/language.md#let-declarations)
  giveth the call notation.
- `deed/misfaresome.tung` and `deed/onstand.tung` layer failure and state over `deed`
  as single-constructor wrappers, so each hath its own functor, applicative,
  and monad bizens. they are specialised to `deed`, not general transformers:
  a transformer over any monad would need its laws for an arbitrary inner
  monad, while these prove theirs from the three deed assumptions below.

## naming and style

- a flock that only nameth one member and stateth no law is named `hath_x`,
  where `x` is that member: `hath_+`, `hath_≤`, `hath_≍`, `hath_naught`. a
  lawless flock of several members is named for what they share, as `catamorphism`
  for `gather₀` and `gather₁` and `elementary` for the elementary functions,
  never `hath_` of a name that is not a member. a flock with
  laws, or one that combineth lawful parents, is named for its structure,
  such as `monoid_+` or `order_whole`.
- declared names use the term spellings in
  [`AGENTS.md`](../AGENTS.md#writing-rules). existing module paths keep their
  ascii spellings: `hath_+` liveth in `hath_eke.tung`, `monoid_+` in
  `monoid_eke.tung`, and `≍_to_=` in `same_to_is.tung`.
  the filename spellings of `+`, `-`, `·`, `÷`, `%`, `≤`, `≍`, `=`, and
  `∋` are respectively `eke`, `offdraw`, `fold`, `deal`, `deal_leftover`,
  `at_most`, `same`, `is`, and `inhold`.
- `flock/algebra/whole/` holdeth two families. the eke family is
  `semigroup_+`, `monoid_+` with `naught`, and `group_+` with `-`; the fold
  family is `semigroup_·`, `monoid_·` with `one`, and `group_·` with `/`.
  each parent is required, so `monoid_·` requireth `semigroup_·` and
  `hath_one`. numbers multiply with `·`, and lists, strings, sets, `maybe`,
  `unempty`, functions, and the `lower` and `upper` wrappers combine with
  `·` too; `…·` foldeth a collection in the fold family and `…+` in the eke
  family. `semiring` requireth `monoid_+` and `monoid_·`, and `ring`
  requireth `semiring` and `group_+`. functions have no pointwise `ring`:
  its two paths to the codomain's addition are separate dictionaries.

- a shown name is read qualified by its module, so it doth not repeat the
  module: `ilk/wholetale.tung` showeth `to_ℕ`, read `integer~to_ℕ`, not
  `wholetale_to_natural`. a host binding taketh that name directly; the
  library keepeth no second alias for it.
- a let whose body is one anonymous function of a single row bindeth its
  inputs in the header instead: `let +_+: [f:, g:, h:] ≔ …`, not
  `let +_+ ≔ {f, g, h ^ …}`. the lambda stayeth only where a header would need
  a written type the lambda inferreth, as a pattern input after implicit type
  inputs, `{@β ^ {entries from_list ^ …}}`.
- a let whose named inputs are matched at once is a case function over bare
  slots: `let f: [ℕ, ℕ, ℕ] ≔ {m, 0 ^ m, …}`, not
  `let f: [m: ℕ, n: ℕ, ℕ] ≔ match n {…}`. an input keepeth its name when the
  type mentioneth it, as in a proof `[a: ℕ, (a ≤ a) = yea]`.

## purescript comparison

[purescript prelude](https://pursuit.purescript.org/packages/purescript-prelude/6.0.1/docs/Prelude)
informeth the small surface. the mapping is approximate:

| purescript family                 | bookhoard counterpart                            | boundary                                                               |
| --------------------------------- | ------------------------------------------------ | ---------------------------------------------------------------------- |
| `eq`, `ord`, lattice              | equality, order, semilattice, and lattice flocks | raw comparison, order laws, and lattice laws remain distinct           |
| `semigroup`, `monoid`, `group`    | `semigroup_·`, `monoid_·`, `group_·` and `_+`    | `lower` and `upper` carriers remain distinct                           |
| `semiring`, `ring`, `field`       | arithmetic and euclidean flocks                  | IEEE float division doth not claim exact algebra                       |
| `functor`, `applicative`, `monad` | collection flocks                                | product applicative and monad require a monoid for the first component |
| `foldable`, `traversable`         | `catamorphism`, `throughwend`                    | applicative evidence belongeth to each polymorphic traversal           |
| `maybe`, `either`, `tuple`        | `maybe`, `∑`, `∏`                                | sums and products are library inductives                               |
| `effect`                          | `deed`                                           | a primitive type; `deed/action.tung` supplieth its monad bizens        |
| `array`, `map`, `set`             | `list`, `wordbook`, `set`, `powerset`            | a packed random-access array is absent                                 |

boolean conjunction useth `𝟚 lower`; disjunction useth `𝟚 upper`.
[purescript traversable](https://pursuit.purescript.org/packages/purescript-foldable-traversable/docs/Data.Traversable)
informeth the `functor` and `catamorphism` parent flocks. tung doth not copy its open
record rows, lazy assumptions, or effect encoding.

## lean and mathlib comparison

lean and mathlib inform algebraic boundaries and finite collections. a
[multiset](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Multiset/Defs.html)
retaineth repetition without order. a
[finite set](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Defs.html)
pairth a multiset with a proof of no duplicates.

tung hath no quotient types. `powerset` is
`[a, 𝟚]`. wrap it in `lower` for intersection or `upper` for
union; no bare powerset monoid chooseth between them.

`set` requireth one lawful `order_whole` dictionary for its element type.
its hidden carrier storeth an increasing list of distinct elements with a
checked invariant. `from_list` sorteth and removeth duplicates; `to_list`
returneth canonical order. insertion, filtering, union, and intersection
preserve the invariant. membership useth the same order dictionary, rather
than arbitrary list membership or a separate boolean comparison.

an invariant certificate is unit evidence when the boolean check holdeth,
and empty otherwise. its uniqueness is proved by cases, without proof
irrelevance. sorted lists with the same members are identical; this giveth
set extensionality and all set algebra laws without `sorry` or new axioms.
`ilk/set_list.tung`, `ilk/set_list_setting.tung`, and `ilk/set_list_order.tung`
contain the ordinary list algorithms, preservation proofs, extensionality,
and inclusion proofs. the wrapper in `ilk/set.tung` keepeth its constructor
private and lifteth boolean membership laws to set identity.

`wordbook` still exposeth its raw `from_list` constructor and may contain
duplicate keys. `set~from_list` and `wordbook~from_list` remain distinct by
qualification; the former is a smart constructor function.

the planned order-insensitive bag is tracked in [`todo.md`](../todo.md).
flock laws are members whose types are identities (`=`) over the other
members. a bizen proveth each law or assumeth it with `sorry`; a requirement
provideth the laws as proofs. laws are never evaluator rewrite rules.

## law proofs

[`is.tung`](is.tung) proveth `leibnitz` (congruence), `evenmete`,
`throughgo`, and `throughbear` for the ordinary indexed identity type `=` by
matching `eftbend`. proofs use computation, constructor cases, or
checked induction. list, non-empty list, sum, option, and wordbook mapping laws
need no new axioms. finite boolean arithmetic and finite bounds also reduce
by cases. generic min/max idempotence holdeth for either comparison result.

[`ilk/list_setting.tung`](ilk/list_setting.tung) proveth standalone list
theorems without `sorry`: no confusion and injectivity of `‥`, appending,
mapping, both folds, filtering, reversing, and repetition. law names are terms
too. [`ilk/natural.tung`](ilk/natural.tung) proveth the ℕ order and semiring
laws by induction on structural operation models;
[`ilk/wholetale.tung`](ilk/wholetale.tung) proveth the ℤ order and ring laws from
sign cases and natural-number laws. bookhoard tests compare both carriers'
models with native operations and reject false and ill-founded list proofs.

remaining `sorry` statements have distinct boundaries:

| statements                          | boundary                                                        |
| ----------------------------------- | --------------------------------------------------------------- |
| string, unicode, and euclidean laws | native operations without a model reduce only on literal inputs |

the [flock rules](../tongue/dependent.md#flocks-and-bizens) specify proof
checking and runtime use. `sorry` is an assumption, so checking an instance doth
not establish its remaining laws.

follow the [proof checking guide](../tongue/language.md#proof-checking) to audit
a named theorem or a declaration applying a chosen bizen's law.

function-carrier laws hold pointwise from the result carrier's laws, and the
freer and powerset laws compare continuations and characteristic functions;
each useth `fall_umtake` from [`is.tung`](is.tung), function extensionality,
a listed `orsetting`. product, option, and lower/upper laws use the
requirement's own laws, which a dictionary carrieth. no native equation is
assumed.

deed laws use three host monad assumptions in
[`deed/action.tung`](deed/action.tung): `deed_sheer_bind`, `deed_bind_sheer`,
and `deed_bind_bind`, the monad laws of the host's `deed_sheer` and
`deed_bind`. proofs comparing bound continuations also use `fall_umtake`.
deeds are opaque to conversion, so these are axioms, as lean's
`IO` satisfieth them by its model; the functor, applicative, and monad laws
of `deed` follow. a free inductive `deed` cannot replace them while
`deed_steadfast` existeth: its step `[α deed, α deed]` would put `deed` left
of an arrow in a constructor, which strict positivity rejecteth. a lawful
looping deed would need coinduction.

`order_whole` also requireth `≤_=`: antisymmetry in identity, not only in
boolean sameness. the generic total-order bizens of `∧` and `∨` require only
`order_whole`, so one dictionary carrieth every operation and law they use,
and they prove commutativity, associativity, swallowing, and both
distributive laws by cases on comparisons. a separate `≍_to_=`
requirement would not serve: a parent is a dictionary field, so two
requirements reaching `≍` by different paths cannot be shown to share it.
`𝟚` and `𝟛` prove `≤_=` by cases inside their bizens, and `ℕ` and `ℤ` from their sound
sameness.

[`flock/same_to_is.tung`](flock/same_to_is.tung) stateth that boolean
sameness agreeth with identity, as lean's `LawfulBEq`: `≍_=` turneth
`(a ≍ b) = yea` into `a = b`, and `≍_eftbend` giveth `(a ≍ a) = yea`. `𝟙`,
`𝟚`, `𝟛`, `ℕ`, and `ℤ` prove it by cases or induction. `maybe`, lists,
non-empty lists, products, and sums gain a structural `≍` and prove it from
their components' `≍_to_=`, which they require alone: its parent `≍` is
then the one their `≍` useth. a law that needeth sound sameness requireth
it.

finite set law tests audit generic commutativity, associativity,
distributivity, the least element, and sound boolean sameness without holes
or axioms. runtime tests check canonical enumeration and the former order
and repetition counterexamples. a set still requireth decidable total order;
`powerset` keepeth its unrestricted predicate representation.
