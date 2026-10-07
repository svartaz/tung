# bookhoard design guide

audience: agents and library authors. purpose: the standard library's design
boundaries and their comparison with purescript and mathlib. the
[language document](../tongue/language.md) owneth imports and manifests.

## library surface

`ground.tung` re-publisheth common modules. it is an ordinary import, not an
implicit prelude. each public flock liveth below `flock/`; its file name matcheth
its flock name.

- partial and total order are separate. lower and upper semilattices stand
  alone; a lattice requireth both and absorption.
- `powerset` is a characteristic function. `set` and `table` are finite,
  list-backed collections.
- integers provide exact euclidean division. floats expose IEEE operations
  without claiming exact field or total-order laws.
- `bifunctor` mapeth both sides of products and sums.
- `ilk/freer.tung` provideth `freer`, `bind`, `lift`, mapping, flattening, and
  folding. a request `ξ φ` nameth its answer type `ξ`, and the program keepeth
  the continuation, so any `φ` will do and every function stayeth total.
- `deed/action.tung` maketh `deed` a functor, applicative, and monad, so
  ordinary combinators such as `warp_flat`, `then`, `traverse`, and `each`
  sequence actions. fallible operations return `maybe` or `text ∑ α`;
  nothing throweth.

## naming and style

- a flock that only nameth members and stateth no law is named `hath_x`.
  when its one member is a symbol, `x` is that symbol: `hath_+`, `hath_≤`,
  `hath_≍`. otherwise `x` is the member's word, as `hath_zero`. a flock with
  laws, or one that combineth lawful parents, is named for its structure,
  such as `monoid` or `order_whole`.
- a flock's file name is its flock name, kept ascii: a symbol flock taketh
  the anglish word, so `hath_+` liveth in `hath_eke.tung` and `hath_≤` in
  `hath_at_most.tung`.

- a shown name is read qualified by its module, so it doth not repeat the
  module: `ilk/integer.tung` showeth `to_ℕ`, read `integer~to_ℕ`, not
  `integer_to_natural`. a host binding taketh that name directly; the
  library keepeth no second alias for it.
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
| `semigroup`, `monoid`             | `semigroup`, `monoid`                            | `lower` and `upper` carriers remain distinct                           |
| `semiring`, `ring`, `field`       | arithmetic and euclidean flocks                  | IEEE float division doth not claim exact algebra                       |
| `functor`, `applicative`, `monad` | collection flocks                                | product applicative and monad require a monoid for the first component |
| `foldable`, `traversable`         | `hath_cata`, `traverse`                          | applicative evidence belongeth to each polymorphic traversal           |
| `maybe`, `either`, `tuple`        | `maybe`, `∑`, `both`                             | sums and products live in the core                                     |
| `effect`                          | `deed`                                           | a primitive type; `deed/action.tung` supplieth its monad bizens        |
| `array`, `warp`, `set`            | `list`, `table`, `set`, `powerset`               | a packed random-access array is absent                                 |

boolean conjunction useth `𝟚 lower`; disjunction useth `𝟚 upper`.
[purescript traversable](https://pursuit.purescript.org/packages/purescript-foldable-traversable/docs/Data.Traversable)
informeth the `functor` and `hath_cata` parent flocks. tung doth not copy its open
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

`set` and `table` expose `from_list`. `empty`, `singleton`, and `put` preserve
uniqueness, but direct `set~from_list` may build a noncanonical value.
`set~from_list` and `table~from_list` remain distinct by qualification.

the planned order-insensitive bag is tracked in [`todo.md`](../todo.md).
flock laws are members whose types are identities (`=`) over the other
members. a bizen proveth each law or assumeth it with `sorry`; a requirement
provideth the laws as proofs. laws are never evaluator rewrite rules.

## law proofs

[`is.tung`](sameness.tung) proveth `leibnitz` (congruence), `evenmete`,
`throughgo`, and `transport` for the primitive identity type `=` by
matching `backbend`. proofs use computation, constructor cases, or
checked induction. list, non-empty list, sum, option, and table mapping laws
need no new axioms. finite boolean arithmetic and finite bounds also reduce
by cases. generic min/max idempotence holdeth for either comparison result.

[`ilk/list_setting.tung`](ilk/list_setting.tung) proveth standalone list
theorems without `sorry`: no confusion and injectivity of `‥`, appending,
mapping, both folds, filtering, reversing, and repetition. law names are terms too. [`ilk/natural.tung`](ilk/natural.tung) proveth the ℕ
order and semiring laws by induction on the structural models of its
operations, so statements about lengths may now be proved. the bookhoard tests also try
false and ill-founded proofs beside these theorems and require each to be
rejected.

remaining `sorry` statements have distinct boundaries:

| statements                                                                             | boundary                                                                                                                                        |
| -------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------- |
| text, unicode, and euclidean laws                                                      | native operations without a model reduce only on literal inputs                                                                                 |
| deed laws                                                                              | deed constructors and composition are opaque in conversion; there is no observational equality principle                                        |
| four freer laws and powerset complement                                                | pointwise proofs require equality of continuation or characteristic functions; function extensionality is absent                                |
| function-carrier algebra, order, lattice, and bound laws                               | function extensionality and reusable component-law evidence are absent                                                                          |
| product algebra, option associativity, and infimal/supremal monoids and semigroups     | component laws are checked at instance declaration but not available as terms through a dictionary                                              |
| generic total-order min/max commutativity, associativity, absorption, and distribution | parent operations are abstract; boolean order laws provide no identity soundness for `≍`, and their proofs are unavailable through requirements |
| remaining set laws                                                                     | membership constraints carry no laws, and raw list identity observeth order and duplicates                                                      |

the [flock rules](../tongue/dependent.md#flocks-and-bizens) specify proof
checking and erasure. `sorry` is an assumption, so checking an instance doth
not establish its remaining laws. no native equations, extensionality axiom,
or additional assumptions are introduced by these proofs.

some remaining statements are false under their present assumptions:

- generic total-order min/max commutativity needeth boolean equality to imply
  identity. a two-constructor type with `≍` and `≤` both constantly `yea`
  meeteth every stated order law. its minimum selecteth the first input, so
  swapping distinct inputs changeth the result.
- for sets with ordinary boolean membership, let `a` and `b` be the
  singletons `yea` and `nay`. `a ∨ b` storeth `[nay, yea]`, while `b ∨ a`
  storeth `[yea, nay]`. union commutativity is therefore false in identity.
  `empty ∨ (a ∨ b)` and `(empty ∨ a) ∨ b` also store different orders.
  left empty identity and the bottom law reverse a two-element list.
- intersection commutativity also distinguishth representations: intersecting
  `[yea, nay]` with `[nay, yea]` preserveth the left input's order.

set equality by `≍` cannot replace identity `=` in these proofs. a lawful
extensional representation and stronger membership assumptions require a
separate library design change. [`todo.md`](../todo.md) tracketh that work.
