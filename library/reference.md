# library design guide

audience: agents and library authors. purpose: the standard library's design
boundaries and their comparison with purescript and mathlib. the
[language document](../tongue/language.md) owneth imports and manifests.

## library surface

`often.tung` re-publisheth common modules; it is an ordinary import, not a
prelude. each public class liveth below `class/`, in a file named by the ascii
spelling of its class name.

- partial and total order are separate. lower and upper semilattices stand
  alone; a lattice requireth both and swallowing.
- integers provide exact euclidean division. floats expose IEEE operations
  without claiming exact field or total-order laws.
- `powerset` is a characteristic function `[α, 𝟚]`; its pointwise `·` is
  intersection, and `upper` giveth union. `set` and `wordbook` are finite,
  list-backed collections ([sets](#sets)).
- `tree` is a finite table kept as a weight-balanced search tree, needing only
  a total order on keys. logarithmic paths require ordered, balanced trees
  with correct stored weights: `empty`, `onesome`, `put`, and `rid` keep these
  invariants, while the public `knot` constructor may break them. `entries`
  and `keys` follow stored order.
- `bifunctor` mappeth both sides of products and sums.
- `topology` openeth parts of a type. a part is a type-valued predicate
  `[α, *]`, not a `powerset`, because a join of a whole family of parts, stated
  by `among`, cannot always be computed. `subset`, `meet`, and `preimage`
  work on parts: lying under goeth through, a meet is the greatest part under
  both, and a preimage keepeth meets and lying under. `either_open` joineth
  two open parts as a family over `𝟚`. a function is `steady` when the preimage
  of every open part is open; `identity` is steady, and a steady function after a
  steady function is steady by `▷_steady`.
- openness is a type, not a proof-irrelevant claim, so two proofs that a
  part is open may differ. the inner of a part, the join of every open part
  under it, is not stated: that family is indexed by parts, one universe above
  the parts that `join_open` joineth, and universes are predicative.
- functions from `ρ` are the reader `(ρ →)`, a functor, applicative, and
  monad; functions into `ρ` are `(ρ ←)`, a `contravariant` functor whose
  `contramap` precomposeth. a function type is no application, so search
  cannot find `φ` from it: write `map @(ρ →)`.
- `monad` stateth `bind_bind`, binding's associativity, beside its unit laws.
  `type/kleisli.tung` wrappeth `[α, β φ]` as `α (φ kleisli) β`, a category for
  any monad: `▷` bindeth and `sheer` is `identity`.
- `type/freer.tung` provideth `freer`, `bind`, `lift`, mapping, flattening, and
  folding. a request `ξ φ` nameth its answer type `ξ` and the program keepeth
  the continuation, so any `φ` serveth and every function stayeth total.
- `effect.tung` maketh `effect` a functor, applicative, and monad, so ordinary
  combinators such as `bind`, `then`, `traverse`, and `each` sequence
  actions. fallible operations return `optional` or `string ∨ α`; nothing
  throweth.
- `type/hade.tung` layereth state over any monad `φ` as a one-constructor
  wrapper with its own functor, applicative, and monad bizens, whose laws
  follow from `φ`'s. `type/bare.tung` is the monad that doth nothing, so
  `σ hade bare` is pure state and `σ hade effect` may perform effects. a bizen
  requiring `φ monad` dependeth on every monad bizen of its own module, so the
  operations and laws live in `type/hade/building.tung`, the functor and
  applicative bizens in `type/hade/applicative_bizen.tung`, and the monad bizen
  in `type/hade.tung`, which re-showeth the public names.
- `type/vector.tung`: `α vector n` is a list of exactly `n` values, so
  `head` and `tail` need no `optional`, `at` taketh an `n natural_below` from
  `type/natural_below.tung` (the tales below `n`), and `zip` paireth two lists of one
  manyhood. the manyhood is an index after the value type, so `vector n` is
  no `[*, *]` application and hath no functor bizen; `map` is a plain function.
- `type/natural_division.tung`: `a ∣ b` when some `k` hath `a · k = b`, and
  `greatest_common_divisor` by euclid's division, with `greatest_common_divisor_∣` and
  `∣_greatest_common_divisor` as its defining laws. it counteth down `b` steps rather
  than recursion on a wellfounded relation, whose unfolding would carry a
  groundedness proof other than the recursive call's own. conversion seeth
  that dividing by `b next` yieldeth an outcome but matching cannot, so its
  lemmas take that outcome and its equation as inputs.
- `effect/fallible.tung` layereth failure over `effect` alone and proveth its
  laws from the [effect assumptions](#assumptions).
- `yoneda.tung` stateth the yoneda lemma for a functor on types: `lift` and
  `unlift` convert between `α φ` and `φ yoneda α`, the transformations from
  functions out of `α`. `unlift_lift` followeth from `map_identity`;
  `lift_unlift` needeth the transformation's `natural` proof and holdeth at
  each input, since function extensionality reacheth no implicit inputs.
  `functor` hath no composition law, so naturality is not proved.
- `yoneda_co.tung` is the dual: `φ yoneda_co α` keepeth a hidden `β φ` beside a
  function `[β, α]`, a functor for any `φ` whose mapping composeth the
  function. `unlift` needeth `φ functor`; `unlift_lift` holdeth, and the other
  round trip only after `unlift`, since tung hath no quotient types.
- `type/grounded.tung` provideth well-founded recursion, and
  `wellfounded_recur_by` lifteth it through a computed measure with an
  explicit dependent motive and a decrease proof per call. `type/natural.tung`
  showeth `under`, the strict order as a relation, with `under_wellfounded`;
  `type/list_theorem.tung` showeth `‥_manyhood` and `‥_manyhood_under`,
  since `manyhood` is a left fold and a tail's size is not below its list's
  by conversion alone. the
  [language document](../tongue/language.md#local-blocks-and-recursion) giveth
  the call notation.

## algebra

`class/algebra/total/` holdeth two families. each parent is required, so
`monoid_·` requireth `semigroup_·` and `hath_one`.

- the additive family is `semigroup_+`, `monoid_+` with `zero`, and `group_+`
  with negation `-` (laws `+_-` and `-_+`). the multiplicative family is `semigroup_·`,
  `monoid_·` with `one`, and `group_·` with inverse `/` (laws `·_/` and
  `/_·`).
- binary forms are named for what they do, left to right: `b -+ a` negateth
  `b` then addeth `a`, so it is `a` less `b`, and `b /· a` inverteth `b` then
  multiplieth by `a`. `-+` is a member of `hath_-` beside `-`, so integers and
  floats subtract in one native step; `group_+` and `ring` prove `-+_+`, that
  it equalleth `(b -) + a`. `ℕ` hath no negation, so its subtraction that
  stoppeth at zero is `∸`.
- numbers multiply with `·`, and lists, strings, sets, `optional`, `unempty`,
  functions, and the `lower` and `upper` wrappers combine with `·` too. `…·`
  foldeth a collection in the multiplicative family and `…+` in the additive family. boolean
  conjunction is `𝟚 lower` and disjunction `𝟚 upper`.
- `semiring` requireth `monoid_+` and `monoid_·`. `ring` requireth `semiring`
  and `hath_-` and stateth `+_-` and `-_+` itself; a derived bizen maketh every
  ring a `group_+`, so a ring reacheth `+` through one dictionary path, as
  pointwise function rings and modules need. `module` is an additive `group_+`
  a ring acteth on by `∘`; every ring is a module over itself.

proved theorems:

| file                     | theorems                                                                                  |
| ------------------------ | ----------------------------------------------------------------------------------------- |
| `group_multiply.tung`    | `one_alone`, `/_alone`, `·_strike`, `strike_·`, `/_/`, `one_/`, `/_over_·`, `/·_strike`   |
| `group_add.tung`         | `zero_alone`, `-_alone`, `+_strike`, `strike_+`, `-_-`, `zero_-`, `-_over_+`, `-+_strike` |
| `ring.tung`              | `-_·`, `·_-`, `-_·_-`, `one_-_·`                                                          |
| `module.tung`            | `zero_∘`, `∘_zero`, `-_∘`, `∘_-`, `one_-_∘`                                               |
| `category.tung`          | `identity_alone`                                                                          |
| `groupoid.tung`          | `invert_alone`, `invert_invert`, `identity_invert`, `invert_over_▷`                       |
| `type/natural.tung`      | `next_inject`, `next_+`, `strike_+`, `+_∸`, `·_swap`                                      |
| `type/list_theorem.tung` | `map_manyhood`, `manyhood_·`, `eftwend_manyhood`                                          |

`group_homomorphism.tung` defineth `homomorphic`, `kernel`, and `image` for
`group_·` and proveth `one_f` and `/_f`; that the kernel is a normal subgroup
(`kernel_one`, `kernel_·`, `kernel_/`, `kernel_turn`); that the image is a
subgroup (`image_one`, `image_·`, `image_/`); and the first isomorphism
theorem in coset form, `(a f) = (b f)` exactly when `a /· b` lieth in the
kernel (`fibre_kernel`, `kernel_fibre`). without quotient types, the quotient
group is the kernel-coset relation.

## naming and style

- a class that nameth one member and stateth no law is `hath_x`, after that
  member: `hath_+`, `hath_≤`, `hath_≍`, `hath_zero`. a lawless class of
  several members is named for what they share, as `catamorphism` for `gather₀`
  and `gather₁` and `elementary` for the elementary functions, never `hath_`
  of a non-member. a class with laws, or combining lawful parents, is named for
  its structure, as `monoid_+` or `order_total`.
- declared names follow [`AGENTS.md`](../AGENTS.md#writing-rules). module
  paths keep ascii spellings: `+`, `-`, `·`, `÷`, `%`, `≤`, `≍`, `=`, and `∋`
  are `add`, `subtract`, `multiply`, `divide`, `divide_leftover`, `at_most`, `equal`,
  `is`, and `inhold`, so `hath_+` liveth in `hath_add.tung` and `≍_to_=` in
  `equal_to_is.tung`.
- a shown name is read qualified, so it repeateth no module name:
  `type/integer.tung` showeth `to_ℕ`, read `integer~to_ℕ`. a host binding
  taketh that name directly, with no second alias.
- a let whose body is one single-row lambda bindeth its inputs in the header:
  `let +_+: [f:, g:, h:] ≔ …`, not `let +_+ ≔ {f, g, h ^ …}`. the lambda
  stayeth only where a header would need a type the lambda inferreth, as a
  pattern input after implicit type inputs, `{@β ^ {entries from_list ^ …}}`.
- a let whose body is a one-row match on its inputs destructureth them in the
  header: `let divide_step: [e: ℕ, q ⸴ r: ℕ ∧ ℕ, ℕ ∧ ℕ]`, not `p: ℕ ∧ ℕ` with
  `match p { q ⸴ r ^ … }`. an input keepeth its name only when a later slot
  or the result nameth it.
- a let whose named inputs are matched at once is a case function over bare
  slots: `let f: [ℕ, ℕ, ℕ] ≔ {m, 0 ^ m, …}`, not
  `let f: [m: ℕ, n: ℕ, ℕ] ≔ match n {…}`. an input keepeth its name when the
  type nameth it, as in a proof `[a: ℕ, (a ≤ a) = yea]`.

## law proofs

the library hath no `sorry`. proofs use computation, constructor cases, or
checked induction; a bizen assuming a law with `sorry` would be reported, and
checking it would not establish the law. the
[class rules](../tongue/dependent.md#classes-and-bizens) specify law checking,
and [proof checking](../tongue/language.md#proof-checking) auditeth a theorem
or a declaration applying a chosen bizen's law.

- [`is.tung`](is.tung) proveth `leibnitz`, `symmetry`, `transit`, and
  `throughbear` for `=` by matching `reflect`.
- list, non-empty list, sum, option, and wordbook mapping laws, finite boolean
  arithmetic, and finite bounds reduce by cases or induction; generic min/max
  idempotence holdeth for either comparison result.
- [`type/list_theorem.tung`](type/list_theorem.tung) proveth no confusion and
  injectivity of `‥`, appending, mapping, both folds, filtering, reversing, and
  repetition.
- [`type/natural.tung`](type/natural.tung) proveth the ℕ order and semiring laws
  by induction on structural operation models;
  [`type/integer.tung`](type/integer.tung) proveth the ℤ order, ring, and
  euclidean laws from sign cases and ℕ laws. ℕ division is modelled by
  recursion on the dividend tale and ℤ division by sign cases of ℕ division; the
  leftover of a dividend `m next_negative` is turned to `e ∸ r`, so it is never
  negative. tests compare every model with its native operation and reject
  false and ill-founded list proofs.
- [`type/list_order.tung`](type/list_order.tung) ordereth lists
  lexicographically from `≤` alone and proveth the total-order laws from the
  values' order.
- product, option, and lower/upper laws use the requirement's own laws,
  carried by its dictionary; function-carrier laws hold pointwise from the
  result carrier's. no native equation is assumed.
- `order_partial` requireth `≤_=`, antisymmetry in `=`, beside the boolean
  `≤_antisymmetry`. the boolean law alone would let any preorder pass with a
  `≍` that holdeth everywhere. a separate `≍_to_=` requirement would not mend
  it: a parent is a dictionary field, so two requirements reaching `≍` by
  different paths cannot be shown to share it. `order_total` addeth only
  `≤_total`, and the generic total-order bizens of `⋏` and `⋎` prove
  commutativity, associativity, swallowing, and both distributive laws by
  cases on comparisons. `𝟚` and `𝟛` prove `≤_=` by cases, `ℕ`, `ℤ`, lists,
  `unicode`, and `string` from sound equality, and sets from their `≍_to_=`.
- `field` stateth that multiplication swappeth, that `one` is not `zero`, and that
  `÷` undoeth multiplying by every divisor but `zero`; a law for dividing by
  `zero` would make `zero` and `one` the same. `euclidean` stateth by
  `%_some` that dividing by every divisor but `zero` yieldeth an outcome, so
  a `%` that always yieldeth none is not euclidean.
- [`class/equal_to_is.tung`](class/equal_to_is.tung) stateth that boolean
  equality agreeth with identity, as lean's `LawfulBEq`: `≍_=` turneth
  `(a ≍ b) = yea` into `a = b`, and `≍_reflect` giveth `(a ≍ a) = yea`. `𝟙`,
  `𝟚`, `𝟛`, `ℕ`, and `ℤ` prove it by cases or induction, and `unicode` and
  `string` through their code points and scalar lists; `optional`, lists,
  non-empty lists, products, and sums gain a structural `≍` proved from their
  components' `≍_to_=`, which they require alone, so its parent `≍` is the one
  their `≍` useth. a law needing sound equality requireth it.

### assumptions

every assumption is a listed `axiom`:

- `extend` in [`is.tung`](is.tung), function extensionality, serveth
  function-carrier laws, the freer and powerset laws, which compare
  continuations and characteristic functions, the kleisli laws, and effect proofs
  comparing bound continuations.
- [`effect.tung`](effect.tung) assumeth the monad laws of the host's `effect_sheer`
  and `effect_bind`: `effect_sheer_bind`, `effect_bind_sheer`, and `effect_bind_bind`,
  from which the functor, applicative, and monad laws of `effect` follow. effects
  are opaque to conversion, so these are axioms, as lean's `IO` satisfieth
  them by its model. a free inductive `effect` cannot replace them while `fast`
  existeth: a fast declaration is sound only because every effect type is a
  one-element set in the model, and a free inductive effect hath many elements,
  so an unbounded self-call could build an ill-founded one. a lawful looping
  effect would need coinduction.
- the host's `unicode` and `string` are opaque.
  [`type/unicode.tung`](type/unicode.tung) modelleth scalar equality and order
  by code points and [`type/string/building.tung`](type/string/building.tung)
  string equality, order, and joining by scalar lists, so their order and monoid
  laws follow from the round trips `natural_unicode`, `list_string`, and
  `string_list`.

## sets

`set` requireth one lawful `order_total` dictionary for its elements. its
hidden carrier storeth an increasing list of distinct elements with a checked
invariant: `from_list` sorteth and riddeth duplicates, `to_list` returneth
canonical order, and insertion, filtering, union, and intersection preserve the
invariant. membership useth the same dictionary, not arbitrary list membership
or a separate boolean comparison.

an invariant certificate is unit evidence when the boolean check holdeth and
empty otherwise; its uniqueness is proved by cases, without proof
irrelevance. sorted lists with the same members are identical, which giveth
set extensionality and every set algebra law without `sorry` or new axioms.
`type/set_list.tung`, `type/set_list_theorem.tung`, and
`type/set_list_order.tung` hold the list algorithms, preservation proofs,
extensionality, and inclusion proofs; `type/set.tung` keepeth its constructor
private and lifteth boolean membership laws to set identity. tests audit
generic commutativity, associativity, distributivity, the least element, and
sound equality without holes or axioms, and check canonical enumeration and
that insertion order and repetition do not matter.

`wordbook` still exposeth its raw `from_list` constructor and may hold
duplicate keys; `set~from_list`, a smart constructor, and `wordbook~from_list`
stay distinct by qualification. a set needeth a decidable total order, while
`powerset` keepeth its unrestricted predicate. the planned order-insensitive
bag is tracked in [`todo.md`](../todo.md).

## comparisons

[purescript prelude](https://pursuit.purescript.org/packages/purescript-prelude/6.0.1/docs/Prelude)
informeth the small surface; the mapping is approximate:

| purescript family                 | library counterpart                               | boundary                                                               |
| --------------------------------- | ------------------------------------------------- | ---------------------------------------------------------------------- |
| `eq`, `ord`, lattice              | equality, order, semilattice, and lattice classes | raw comparison, order laws, and lattice laws remain distinct           |
| `semigroup`, `monoid`, `group`    | `semigroup_·`, `monoid_·`, `group_·` and `_+`     | `lower` and `upper` carriers remain distinct                           |
| `semiring`, `ring`, `field`       | arithmetic and euclidean classes                  | IEEE float division doth not claim exact algebra                       |
| `functor`, `applicative`, `monad` | collection classes                                | product applicative and monad require a monoid for the first component |
| `foldable`, `traversable`         | `catamorphism`, `traverse`                        | applicative evidence belongeth to each polymorphic traversal           |
| `optional`, `either`, `tuple`     | `optional`, `∨`, `∧`                              | sums and products are library inductives                               |
| `effect`                          | `effect`                                          | a primitive type; `effect.tung` supplieth its monad bizens             |
| `array`, `map`, `set`             | `list`, `wordbook`, `set`, `powerset`             | a packed random-access array is absent                                 |

[purescript traversable](https://pursuit.purescript.org/packages/purescript-foldable-traversable/docs/Data.Traversable)
informeth the `functor` and `catamorphism` parents. tung copieth neither its open
record rows, lazy assumptions, nor effect encoding.

lean and mathlib inform algebraic boundaries and finite collections: a
[multiset](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Multiset/Defs.html)
keepeth repetition without order, and a
[finite set](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Defs.html)
paireth a multiset with a proof of no duplicates. tung hath no quotient types,
so `set` keepeth a canonical sorted list instead.
