# bookhoard design guide

audience: agents and library authors. purpose: the standard library's design
boundaries and their comparison wiþ purescript and mathlib. the
[language document](../tongue/language.md) owneþ imports and manifests.

## library surface

`ground.tung` re-publisheþ common modules. it is an ordinary import, not an
implicit prelude. each public flock liveþ below `flock/`; its file name matcheþ
its flock name.

- partial and total order are separate. lower and upper semilattices stand
  alone; a lattice requireþ both and absorption.
- `powerset` is a characteristic function. `set` and `table` are finite,
  list-backed collections.
- integers provide exact euclidean division. floats expose IEEE operations
  without claiming exact field or total-order laws.
- `bifunctor` mapeþ both sides of products and sums.
- `ilk/freer.tung` provideþ `freer`, `bind`, `lift`, mapping, flattening, and
  folding. a request `ξ φ` nameþ its answer type `ξ`, and þe program keepeþ
  þe continuation, so any `φ` will do and every function stayeþ total.
- `deed/action.tung` makeþ `deed` a functor, applicative, and monad, so
  ordinary combinators such as `map_flat`, `þen`, `traverse`, and `each`
  sequence actions. fallible operations return `option` or `text ∑ α`;
  noþing throweþ.

## purescript comparison

[purescript prelude](https://pursuit.purescript.org/packages/purescript-prelude/6.0.1/docs/Prelude)
informeþ the small surface. the mapping is approximate:

| purescript family                 | bookhoard counterpart                            | boundary                                                               |
| --------------------------------- | ------------------------------------------------ | ---------------------------------------------------------------------- |
| `eq`, `ord`, lattice              | equality, order, semilattice, and lattice flocks | raw comparison, order laws, and lattice laws remain distinct           |
| `semigroup`, `monoid`             | `semigroup`, `monoid`                            | `infimal` and `supremal` carriers remain distinct                      |
| `semiring`, `ring`, `field`       | arithmetic and euclidean flocks                  | IEEE float division doth not claim exact algebra                       |
| `functor`, `applicative`, `monad` | collection flocks                                | product applicative and monad require a monoid for the first component |
| `foldable`, `traversable`         | `cata`, `traverse`                               | applicative evidence belongeþ to each polymorphic traversal            |
| `maybe`, `either`, `tuple`        | `option`, `∑`, `boþ`                             | sums and products live in the core                                     |
| `effect`                          | `deed`                                           | a primitive type; `deed/action.tung` supplieþ its monad bizens         |
| `array`, `map`, `set`             | `list`, `table`, `set`, `powerset`               | a packed random-access array is absent                                 |

boolean conjunction useþ `𝟚 infimal`; disjunction useþ `𝟚 supremal`.
[purescript traversable](https://pursuit.purescript.org/packages/purescript-foldable-traversable/docs/Data.Traversable)
informeþ the `functor` and `cata` parent flocks. tung doth not copy its open
record rows, lazy assumptions, or effect encoding.

## lean and mathlib comparison

lean and mathlib inform algebraic boundaries and finite collections. a
[multiset](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Multiset/Defs.html)
retaineth repetition without order. a
[finite set](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Defs.html)
pairþ a multiset wiþ a proof of no duplicates.

tung hath no quotient types. `powerset` is
`[a, 𝟚]`. wrap it in `infimal` for intersection or `supremal` for
union; no bare powerset monoid chooseþ between them.

`set` and `table` expose `from_list`. `empty`, `singleton`, and `put` preserve
uniqueness, but direct `set~from_list` may build a noncanonical value.
`set~from_list` and `table~from_list` remain distinct by qualification.

the planned order-insensitive bag is tracked in [`todo.md`](../todo.md).
flock laws are identity types (`=`) over þe members. a bizen proveþ each law
or assumeþ it wiþ `sorry`; laws are never evaluator rewrite rules.

## law proofs

[`equality.tung`](equality.tung) proveþ `leibnitz` (congruence), `symmetry`,
`transitivity`, and `transport` for þe primitive identity type `=` by
matching `reflect`. proofs use computation, constructor cases, or
checked induction. list, non-empty list, sum, option, and table mapping laws
need no new axioms. finite boolean arithmetic and finite bounds also reduce
by cases. generic min/max idempotence holdeth for either comparison result.

[`ilk/list_theorem.tung`](ilk/list_theorem.tung) proveþ standalone list
theorems wiþout `sorry`: no confusion and injectivity of `‥`, appending,
mapping, both folds, filtering, reversing, and repetition. þey are terms,
unlike law names. ℕ arithmetic is native and computeþ only on literals, so
statements about lengths are not among þem. þe bookhoard tests also try
false and ill-founded proofs beside þese theorems and require each to be
rejected.

remaining `sorry` statements have distinct boundaries:

| statements                                                                             | boundary                                                                                                                                        |
| -------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------- |
| integer, natural, text, unicode, and euclidean laws                                    | native operations reduce on literal inputs; there are no equations for open inputs                                                              |
| deed laws                                                                              | deed constructors and composition are opaque in conversion; there is no observational equality principle                                        |
| four freer laws and powerset complement                                                | pointwise proofs require equality of continuation or characteristic functions; function extensionality is absent                                |
| function-carrier algebra, order, lattice, and bound laws                               | function extensionality and reusable component-law evidence are absent                                                                          |
| product algebra, option associativity, and infimal/supremal monoids and semigroups     | component laws are checked at instance declaration but not available as terms through a dictionary                                              |
| generic total-order min/max commutativity, associativity, absorption, and distribution | parent operations are abstract; boolean order laws provide no identity soundness for `≍`, and their proofs are unavailable through requirements |
| remaining set laws                                                                     | membership constraints carry no laws, and raw list identity observeþ order and duplicates                                                       |

the [flock rules](../tongue/dependent.md#flocks-and-bizens) specify proof
checking and erasure. `sorry` is an assumption, so checking an instance doth
not establish its remaining laws. no native equations, extensionality axiom,
or additional assumptions are introduced by these proofs.

some remaining statements are false under their present assumptions:

- generic total-order min/max commutativity needeþ boolean equality to imply
  identity. a two-constructor type with `≍` and `≤` both constantly `yea`
  meeteth every stated order law. its minimum selecteþ þe first input, so
  swapping distinct inputs changeþ þe result.
- for sets with ordinary boolean membership, let `a` and `b` be þe
  singletons `yea` and `nay`. `a ∨ b` storeþ `[nay, yea]`, while `b ∨ a`
  storeþ `[yea, nay]`. union commutativity is therefore false in identity.
  `empty ∨ (a ∨ b)` and `(empty ∨ a) ∨ b` also store different orders.
  left empty identity and þe bottom law reverse a two-element list.
- intersection commutativity also distinguishþ representations: intersecting
  `[yea, nay]` with `[nay, yea]` preserveþ þe left input's order.

set equality by `≍` cannot replace identity `=` in these proofs. a lawful
extensional representation and stronger membership assumptions require a
separate library design change. [`todo.md`](../todo.md) trackeþ that work.
