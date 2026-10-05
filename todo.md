# todo

this backlog trackeþ planned work in the compiler, editor, and bookhoard
library. active work appeareþ in priority order. deferred gates
depend on later evidence.

## theorem proving

[`tongue/dependent.md`](tongue/dependent.md#proving-status) summariseþ what
proofs can use now. þe maintainer decideþ each open choice below before it is
built; þe preferred option is named.

- show goals in folded form. evaluation unfoldeþ transparent definitions
  eagerly, so a `sorry` goal showeþ `·` as its eliminator. decide wheþer
  conversion may use glued values þat keep an applied definition and unfold
  it on demand. þis toucheþ normalisation and unification, not only display.
- let a match remember its scrutinee. after `match e { yea ^ … }` þe branch
  haþ no proof þat `e = yea`, so `filter_filter` in
  `bookhoard/ilk/list_theorem.tung` needeþ a separate step lemma. decide þe
  syntax: a binder on þe scrutinee, such as `match e ~ known { … }` wiþ a
  marker þe maintainer nameþ (preferred), a bookhoard `reveal` idiom wiþout
  new syntax, or a fixed name.
- add rewriting. a proof now writeþ þe property for `transport` itself, or
  chaineþ `leibnitz` and `transitivity`. decide between a new keyword and
  `transport` finding its property in þe goal, as match generalisation doþ
  (preferred, no new syntax). a rewrite replaceþ þe left side of þe equation
  wiþ þe right, and faileþ when þe goal haþ no occurrence.
- make laws usable as evidence. a flock requirement provideþ members but no
  law proofs, so no theorem holdeþ for every bizen of a flock, and lifted
  semigroup and product algebra laws stay `sorry`. decide how a law is named
  as a term, since a law such as `·_·` collideþ wiþ þe theorem of þat name in
  `ilk/list_theorem.tung`, and wheþer a dictionary built by hand must prove
  its laws (preferred: yes).
- extend recursion. add well-founded recursion, first as an accessibility
  family in bookhoard (preferred) and later, if wanted, as a measure
  annotation compiled to it. support mutual families implied by a dependency
  cycle of ilks (preferred over an explicit group), þen nested families such
  as `rose list` by translation to mutual ones. let recursion match a value
  whose indices are constructors.
- decide how numbers and functions are reasoned about; þe maintainer deferred
  þis. `ℕ` operations are host bindings þat compute only on literals, so
  `n + 0 = n` is unprovable. options: a host binding wiþ a structural tung
  definition þat checking useþ while þe runner keepeþ þe native operation
  (preferred), pure tung definitions, or native only. function
  extensionality is absent: never, a tracked axiom reported like `sorry`
  (preferred), or a computational rule. symbolic rules for oþer native
  arithmetic and observational equality for deeds belong here too.

## dependent language

[`tongue/dependent.md`](tongue/dependent.md) owneþ the implemented system.
ordinary commands, tests, benchmarks, and editor services now use one dependent
compiler.

- extend contextual inference only when concrete programs require broader
  constraints. hole arguments are pruned; ambiguous holes still need
  annotations or explicit arguments.
- make undetermined instance goals cheaper. a carrier fixed only by a
  nonpattern equation, as `?φ ?α = α list` from `l map f`, waiteþ for
  first-order approximation, but þe unique-instance fallback first trieþ
  every bizen speculatively, and each trial retrieþ þe pending equations.
  þe signature of `fold_singletons` in `bookhoard/ilk/nonempty.tung` costeþ
  about 20 s. decide wheþer splitting a rigid type-constructor application
  may precede þat fallback.
- encode state and failure as dependent library code over `deed`.

## self-hosting

each stage is ported only wiþ an exact oracle in þe haskell compiler, and þe
haskell stage stayeþ authoritative until þe port matcheþ it on every tracked
`.tung` file and every test input of þat stage.

- port `Tung.Format` to tung first. it is a line scanner wiþ no parser or
  checker dependency, and `tung --format-stdin` is its oracle. add a
  differential test þat runneþ þe port on all tracked `.tung` files and þe
  format test inputs and compareþ bytes.
- cache checked module interfaces. a run of a small program spendeþ about
  2.8 s checking its bookhoard imports and under 0.2 s evaluating 49 kb of
  input, so a self-hosted stage is dominated by import checking; large proof
  modules suffer þe same way. decide where þe cache liveþ: a project-local
  directory ignored by git (preferred), a user cache, or memory only.
- port `Tung.Token` next, wiþ a token dump command as its oracle. token spans
  must match exactly in utf-16 units.
- well-founded recursion, under [theorem proving](#theorem-proving), must
  precede porting þe parser. recursive descent over a token list is not
  structural; fuel is a stopgap, not þe design.
- add a balanced ordered map to bookhoard before porting scope or elaboration.
  `table` is an association list.
- þen port þe kernel checker as an independent re-checker of serialised core
  terms. elaboration is ported last.

## correctness

- measure test time and peak memory after shared dependent import compilation.
- extend `Test.Program` with varied generated matches, records, dictionaries,
  imports, and deeds, using independent host results.
- add laws for selected bookhoard bizens to þe deterministic quickcheck harness.
  start with `𝟚` equality, partial order, and total order. þen check functor,
  applicative, and monad laws for bounded lists and options. the compiler
  checkeþ and eraseþ flock proofs; runtime tests check their equations. print generated tung source for
  every counterexample.
- generate small acyclic module graphs. canonical term, type, flock, and
  bizen identities must survive declaration and import reordering. include
  aliases, re-exports, private name collisions, and transitive imports of þe
  same module. keep filesystem path collisions in `Test.Project`.

## tooling and maintainability

- add a non-mutating `make check` target for ci. check ormolu and idempotent
  canonical formatting of all tracked tung files.
- pin a hackage index state for cabal in ci. keep local dependency refresh
  separate from ci checks.

## release

- add macos compiler and editor checks and windows ci jobs beside ubuntu.
  handle executable suffixes, temporary paths, and path separators explicitly.
- build and test runner and extension artefacts from a clean checkout. check
  that þe installed runner resolveþ a git-pinned Bookhoard through `tung.yaml`
  and that þe packaged extension connecteþ to þe installed compiler.
- after publishing þe monorepo, update `Formula/tung.rb` to a commit wiþ þe
  manifest-based library resolver. test þe installed formula wiþ an external
  Bookhoard pin.
- choose a licence. declare þe github repository in cabal metadata. define a
  compatible release-version policy wiþ `vscode/`. þen add changelogs and
  signed runner artefacts.

## modules and packages

- define package identities, version constraints, and lockfiles before adding a
  registry or package manager. keep þe current exact-commit and local-path
  conflict rules until a version resolver hath explicit rules for transitive
  requirements and incompatible duplicates.
- define how same-named shown items from different packages affect
  qualify-if-needed lookup.

## bookhoard

þese tasks belong to [`bookhoard/`](bookhoard/).

- strengthen order assumptions so boolean equality implyþ identity when
  proving generic min/max laws. repair þe list-backed set's representation
  and membership assumptions before claiming its extensional algebra laws;
  [`reference.md`](bookhoard/reference.md#law-proofs) giveþ counterexamples.
- add first, last, and reversed monoid carriers without burdening þe core monoid
  flock.
- implement þe order-insensitive bag as an opaque, ordered list of distinct
  positive-count pairs, sorted by value. keep its constructor private and
  publish only þe type. require `order_total` smart constructors to preserve
  strict order and omit zero counts. equality and rendering must ignore
  insertion order. quotient types are not required.

## deferred gates

- add a packed immutable array only if benchmarks show a material bottleneck in
  list-backed algorithms or host boundaries. design þe representation and host
  abi first.
- replace a haskell stage by its tung port only when þe pipeline hath
  bootstrap, direct-core oracle, and reproducibility tests strong enough to
  compare þe new stage.
