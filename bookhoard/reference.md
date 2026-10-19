# bookhoard design guide

audience: agents and library authors. purpose: the standard library's design
boundaries and their comparison with purescript and mathlib. the
[language document](../tongue/language.md) owneth imports and manifests.

## library surface

`often.tung` re-publisheth common modules; it is an ordinary import, not a
prelude. each public flock liveth below `flock/`, in a file named by the ascii
spelling of its flock name.

- partial and total order are separate. lower and upper semilattices stand
  alone; a lattice requireth both and swallowing.
- integers provide exact euclidean division. floats expose IEEE operations
  without claiming exact field or total-order laws.
- `mightset` is a characteristic function `[α, 𝟚]`; its pointwise `·` is
  intersection, and `upper` giveth union. `set` and `wordbook` are finite,
  list-backed collections ([sets](#sets)).
- `tree` is a finite table kept as a weight-balanced search tree, needing only
  a total order on keys. logarithmic paths require ordered, balanced trees
  with correct stored weights: `empty`, `onesome`, `put`, and `rid` keep these
  invariants, while the public `knot` constructor may break them. `entries`
  and `keys` follow stored order.
- `bifunctor` mappeth both sides of products and sums.
- functions from `ρ` are the reader `(ρ →)`, a functor, applicative, and
  monad; functions into `ρ` are `(ρ ←)`, a `contravariant` functor whose
  `witherwarp` precomposeth. a function ilk is no application, so search
  cannot find `φ` from it: write `warp @(ρ →)`.
- `monad` stateth `bind_bind`, binding's associativity, beside its unit laws.
  `ilk/kleisli.tung` wrappeth `[α, β φ]` as `α (φ kleisli) β`, a category for
  any monad: `▷` bindeth and `sheer` is `sameness`.
- `ilk/freer.tung` provideth `freer`, `bind`, `lift`, mapping, flattening, and
  folding. a request `ξ φ` nameth its answer type `ξ` and the program keepeth
  the continuation, so any `φ` serveth and every function stayeth total.
- `deed.tung` maketh `deed` a functor, applicative, and monad, so ordinary
  combinators such as `bind`, `then`, `throughwend`, and `each` sequence
  actions. fallible operations return `maybe` or `string ∨ α`; nothing
  throweth.
- `deed/misfaresome.tung` and `deed/hade.tung` layer failure and state over
  `deed` as one-constructor wrappers with their own functor, applicative, and
  monad bizens. they are specialised to `deed`: a transformer over any monad
  would need laws for an arbitrary inner monad, while these prove theirs from
  the [deed assumptions](#assumptions).
- `yoneda.tung` stateth the yoneda lemma for a functor on types: `lift` and
  `unlift` convert between `α φ` and `φ yoneda α`, the transformations from
  functions out of `α`. `unlift_lift` followeth from `warp_sameness`;
  `lift_unlift` needeth the transformation's `kindful` proof and holdeth at
  each input, since function extensionality reacheth no implicit inputs.
  `functor` hath no composition law, so naturality is not proved.
- `yoneda_co.tung` is the dual: `φ yoneda_co α` keepeth a hidden `β φ` beside a
  function `[β, α]`, a functor for any `φ` whose mapping composeth the
  function. `unlift` needeth `φ functor`; `unlift_lift` holdeth, and the other
  round trip only after `unlift`, since tung hath no quotient types.
- `ilk/grounded.tung` provideth well-founded recursion, and
  `wellgrounded_selfcall_by` lifteth it through a computed measure with an
  explicit dependent motive and a decrease proof per call. `ilk/kindful.tung`
  showeth `under`, the strict order as a relation, with `under_wellgrounded`;
  `ilk/list_setting.tung` showeth `‥_manyhood` and `‥_manyhood_under`,
  since `manyhood` is a left fold and a tail's size is not below its list's
  by conversion alone. the
  [language document](../tongue/language.md#local-blocks-and-recursion) giveth
  the call notation.

## algebra

`flock/algebra/whole/` holdeth two families. each parent is required, so
`monoid_·` requireth `semigroup_·` and `hath_one`.

- the eke family is `semigroup_+`, `monoid_+` with `naught`, and `group_+`
  with negation `-` (laws `+_-` and `-_+`). the fold family is `semigroup_·`,
  `monoid_·` with `one`, and `group_·` with inverse `/` (laws `·_/` and
  `/_·`).
- binary forms are named for what they do, left to right: `b -+ a` negateth
  `b` then addeth `a`, so it is `a` less `b`, and `b /· a` inverteth `b` then
  multiplieth by `a`. `-+` is a member of `hath_-` beside `-`, so integers and
  floats subtract in one native step; `group_+` and `ring` prove `-+_+`, that
  it equalleth `(b -) + a`. `ℕ` hath no negation, so its subtraction that
  stoppeth at naught is `∸`.
- numbers multiply with `·`, and lists, strings, sets, `maybe`, `unempty`,
  functions, and the `lower` and `upper` wrappers combine with `·` too. `…·`
  foldeth a collection in the fold family and `…+` in the eke family. boolean
  conjunction is `𝟚 lower` and disjunction `𝟚 upper`.
- `semiring` requireth `monoid_+` and `monoid_·`. `ring` requireth `semiring`
  and `hath_-` and stateth `+_-` and `-_+` itself; a derived bizen maketh every
  ring a `group_+`, so a ring reacheth `+` through one dictionary path, as
  pointwise function rings and modules need. `module` is an additive `group_+`
  a ring acteth on by `∘`; every ring is a module over itself.

proved theorems:

| file                    | theorems                                                                                      |
| ----------------------- | --------------------------------------------------------------------------------------------- |
| `group_fold.tung`       | `one_alone`, `/_alone`, `·_strike`, `strike_·`, `/_/`, `one_/`, `/_over_·`, `/·_strike`       |
| `group_eke.tung`        | `naught_alone`, `-_alone`, `+_strike`, `strike_+`, `-_-`, `naught_-`, `-_over_+`, `-+_strike` |
| `ring.tung`             | `-_·`, `·_-`, `-_·_-`, `one_-_·`                                                              |
| `module.tung`           | `naught_∘`, `∘_naught`, `-_∘`, `∘_-`, `one_-_∘`                                               |
| `category.tung`         | `sameness_alone`                                                                              |
| `groupoid.tung`         | `witherwend_alone`, `witherwend_witherwend`, `sameness_witherwend`, `witherwend_over_▷`       |
| `ilk/kindful.tung`      | `heir_incast`, `heir_+`, `strike_+`, `+_∸`, `·_swap`                                          |
| `ilk/list_setting.tung` | `warp_manyhood`, `manyhood_·`, `eftwend_manyhood`                                             |

`group_likeshaper.tung` defineth `likeshaped`, `kernel`, and `shadow` for
`group_·` and proveth `one_f` and `/_f`; that the kernel is a normal subgroup
(`kernel_one`, `kernel_·`, `kernel_/`, `kernel_spin`); that the shadow is a
subgroup (`shadow_one`, `shadow_·`, `shadow_/`); and the first isomorphism
theorem in coset form, `(a f) = (b f)` exactly when `a /· b` lieth in the
kernel (`fibre_kernel`, `kernel_fibre`). without quotient types, the quotient
group is the kernel-coset relation.

## naming and style

- a flock that nameth one member and stateth no law is `hath_x`, after that
  member: `hath_+`, `hath_≤`, `hath_≍`, `hath_naught`. a lawless flock of
  several members is named for what they share, as `downshaper` for `gather₀`
  and `gather₁` and `elementary` for the elementary functions, never `hath_`
  of a non-member. a flock with laws, or combining lawful parents, is named for
  its structure, as `monoid_+` or `order_whole`.
- declared names follow [`AGENTS.md`](../AGENTS.md#writing-rules). module
  paths keep ascii spellings: `+`, `-`, `·`, `÷`, `%`, `≤`, `≍`, `=`, and `∋`
  are `eke`, `offdraw`, `fold`, `deal`, `deal_leftover`, `at_most`, `same`,
  `is`, and `inhold`, so `hath_+` liveth in `hath_eke.tung` and `≍_to_=` in
  `same_to_is.tung`.
- a shown name is read qualified, so it repeateth no module name:
  `ilk/wholetale.tung` showeth `to_ℕ`, read `wholetale~to_ℕ`. a host binding
  taketh that name directly, with no second alias.
- a let whose body is one single-row lambda bindeth its inputs in the header:
  `let +_+: [f:, g:, h:] ≔ …`, not `let +_+ ≔ {f, g, h ^ …}`. the lambda
  stayeth only where a header would need a type the lambda inferreth, as a
  pattern input after implicit type inputs, `{@β ^ {entries from_list ^ …}}`.
- a let whose body is a one-row match on its inputs destructureth them in the
  header: `let deal_step: [e: ℕ, q ⸴ r: ℕ ∧ ℕ, ℕ ∧ ℕ]`, not `p: ℕ ∧ ℕ` with
  `match p { q ⸴ r ^ … }`. an input keepeth its name only when a later slot
  or the result nameth it.
- a let whose named inputs are matched at once is a case function over bare
  slots: `let f: [ℕ, ℕ, ℕ] ≔ {m, 0 ^ m, …}`, not
  `let f: [m: ℕ, n: ℕ, ℕ] ≔ match n {…}`. an input keepeth its name when the
  type nameth it, as in a proof `[a: ℕ, (a ≤ a) = yea]`.

## law proofs

bookhoard hath no `sorry`. proofs use computation, constructor cases, or
checked induction; a bizen assuming a law with `sorry` would be reported, and
checking it would not establish the law. the
[flock rules](../tongue/dependent.md#flocks-and-bizens) specify law checking,
and [proof checking](../tongue/language.md#proof-checking) auditeth a theorem
or a declaration applying a chosen bizen's law.

- [`is.tung`](is.tung) proveth `leibnitz`, `evenmete`, `throughgo`, and
  `throughbear` for `=` by matching `eftbend`.
- list, non-empty list, sum, option, and wordbook mapping laws, finite boolean
  arithmetic, and finite bounds reduce by cases or induction; generic min/max
  idempotence holdeth for either comparison result.
- [`ilk/list_setting.tung`](ilk/list_setting.tung) proveth no confusion and
  injectivity of `‥`, appending, mapping, both folds, filtering, reversing, and
  repetition.
- [`ilk/kindful.tung`](ilk/kindful.tung) proveth the ℕ order and semiring laws
  by induction on structural operation models;
  [`ilk/wholetale.tung`](ilk/wholetale.tung) proveth the ℤ order, ring, and
  euclidean laws from sign cases and ℕ laws. ℕ dealing is modelled by
  selfcalling on the dealt tale and ℤ dealing by sign cases of ℕ dealing; the
  leftover of a dealt `m heir_undernaught` is turned to `e ∸ r`, so it is never
  undernaught. tests compare every model with its native operation and reject
  false and ill-founded list proofs.
- [`ilk/list_order.tung`](ilk/list_order.tung) ordereth lists
  lexicographically from `≤` alone and proveth the whole-order laws from the
  worths' order.
- product, option, and lower/upper laws use the requirement's own laws,
  carried by its dictionary; function-carrier laws hold pointwise from the
  result carrier's. no native equation is assumed.
- `order_whole` requireth `≤_=`, antisymmetry in identity, not only boolean
  sameness, so the generic total-order bizens of `⋏` and `⋎` need only
  `order_whole` and prove commutativity, associativity, swallowing, and both
  distributive laws by cases on comparisons. a separate `≍_to_=` requirement
  would fail: a parent is a dictionary field, so two requirements reaching `≍`
  by different paths cannot be shown to share it. `𝟚` and `𝟛` prove `≤_=` by
  cases and `ℕ` and `ℤ` from sound sameness.
- [`flock/same_to_is.tung`](flock/same_to_is.tung) stateth that boolean
  sameness agreeth with identity, as lean's `LawfulBEq`: `≍_=` turneth
  `(a ≍ b) = yea` into `a = b`, and `≍_eftbend` giveth `(a ≍ a) = yea`. `𝟙`,
  `𝟚`, `𝟛`, `ℕ`, and `ℤ` prove it by cases or induction; `maybe`, lists,
  non-empty lists, products, and sums gain a structural `≍` proved from their
  components' `≍_to_=`, which they require alone, so its parent `≍` is the one
  their `≍` useth. a law needing sound sameness requireth it.

### assumptions

every assumption is a listed `orsetting`:

- `fall_umfang` in [`is.tung`](is.tung), function extensionality, serveth
  function-carrier laws, the freer and mightset laws, which compare
  continuations and characteristic functions, the kleisli laws, and deed proofs
  comparing bound continuations.
- [`deed.tung`](deed.tung) assumeth the monad laws of the host's `deed_sheer`
  and `deed_bind`: `deed_sheer_bind`, `deed_bind_sheer`, and `deed_bind_bind`,
  from which the functor, applicative, and monad laws of `deed` follow. deeds
  are opaque to conversion, so these are axioms, as lean's `IO` satisfieth
  them by its model. a free inductive `deed` cannot replace them while `fast`
  existeth: a fast declaration is sound only because every deed type is a
  one-element set in the model, and a free inductive deed hath many elements,
  so an unbounded self-call could build an ill-founded one. a lawful looping
  deed would need coinduction.
- the host's `unicode` and `string` are opaque.
  [`ilk/unicode.tung`](ilk/unicode.tung) modelleth scalar sameness and order
  by code points and [`ilk/string/building.tung`](ilk/string/building.tung)
  string sameness, order, and yoking by scalar lists, so their order and monoid
  laws follow from the round trips `kindful_unicode`, `list_string`, and
  `string_list`.

## sets

`set` requireth one lawful `order_whole` dictionary for its elements. its
hidden carrier storeth an increasing list of distinct elements with a checked
invariant: `from_list` roweth and riddeth duplicates, `to_list` returneth
canonical order, and insertion, filtering, union, and intersection preserve the
invariant. membership useth the same dictionary, not arbitrary list membership
or a separate boolean comparison.

an invariant certificate is unit evidence when the boolean check holdeth and
empty otherwise; its uniqueness is proved by cases, without proof
irrelevance. sorted lists with the same members are identical, which giveth
set extensionality and every set algebra law without `sorry` or new axioms.
`ilk/set_list.tung`, `ilk/set_list_setting.tung`, and
`ilk/set_list_order.tung` hold the list algorithms, preservation proofs,
extensionality, and inclusion proofs; `ilk/set.tung` keepeth its constructor
private and lifteth boolean membership laws to set identity. tests audit
generic commutativity, associativity, distributivity, the least element, and
sound sameness without holes or axioms, and check canonical enumeration and
that insertion order and repetition do not matter.

`wordbook` still exposeth its raw `from_list` constructor and may hold
duplicate keys; `set~from_list`, a smart constructor, and `wordbook~from_list`
stay distinct by qualification. a set needeth a decidable total order, while
`mightset` keepeth its unrestricted predicate. the planned order-insensitive
bag is tracked in [`todo.md`](../todo.md).

## comparisons

[purescript prelude](https://pursuit.purescript.org/packages/purescript-prelude/6.0.1/docs/Prelude)
informeth the small surface; the mapping is approximate:

| purescript family                 | bookhoard counterpart                            | boundary                                                               |
| --------------------------------- | ------------------------------------------------ | ---------------------------------------------------------------------- |
| `eq`, `ord`, lattice              | equality, order, semilattice, and lattice flocks | raw comparison, order laws, and lattice laws remain distinct           |
| `semigroup`, `monoid`, `group`    | `semigroup_·`, `monoid_·`, `group_·` and `_+`    | `lower` and `upper` carriers remain distinct                           |
| `semiring`, `ring`, `field`       | arithmetic and euclidean flocks                  | IEEE float division doth not claim exact algebra                       |
| `functor`, `applicative`, `monad` | collection flocks                                | product applicative and monad require a monoid for the first component |
| `foldable`, `traversable`         | `downshaper`, `throughwend`                      | applicative evidence belongeth to each polymorphic traversal           |
| `maybe`, `either`, `tuple`        | `maybe`, `∨`, `∧`                                | sums and products are library inductives                               |
| `effect`                          | `deed`                                           | a primitive type; `deed.tung` supplieth its monad bizens               |
| `array`, `map`, `set`             | `list`, `wordbook`, `set`, `mightset`            | a packed random-access array is absent                                 |

[purescript traversable](https://pursuit.purescript.org/packages/purescript-foldable-traversable/docs/Data.Traversable)
informeth the `functor` and `downshaper` parents. tung copieth neither its open
record rows, lazy assumptions, nor effect encoding.

lean and mathlib inform algebraic boundaries and finite collections: a
[multiset](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Multiset/Defs.html)
keepeth repetition without order, and a
[finite set](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Defs.html)
paireth a multiset with a proof of no duplicates. tung hath no quotient types,
so `set` keepeth a canonical sorted list instead.
