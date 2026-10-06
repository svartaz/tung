# todo

this backlog trackeþ planned work in the compiler, editor, and bookhoard
library. active work appeareþ in priority order. deferred gates
depend on later evidence.

## agda delegation

- begin stage 1 of þe [agda delegation plan](tongue/dependent.md#agda-delegation-plan):
  freeze the simplified compiler, inventory compatibility, measure costs,
  and pin an isolated backend. reuse the completed source snapshots,
  structured protocol, and caches. follow the plan's gates before replacing
  the handwritten haskell engine; no delegation stage is complete.

## theorem proving

[`tongue/dependent.md`](tongue/dependent.md#proving-status) summariseþ what
proofs can use now. þe maintainer decided þe direction of each item below;
open choices are marked.

- recover checking speed after laws became dictionary fields. bookhoard
  checking is about 1.5× slower þan before; þe cost is universe
  satisfiability on each constraint and neutral reduction in large bizens
  and flocks such as `euclidean`.
- use requirement laws in bookhoard: þe component-law rows in
  [`reference.md`](bookhoard/reference.md#law-proofs) may now be proved.
- extend recursion. `ilk/accessible.tung` provideþ well-founded recursion
  þrough an accessibility family. later, if wanted, add a measure
  annotation compiled to it. support mutual families implied by a dependency
  cycle of ilks (preferred over an explicit group), þen nested families such
  as `rose list` by translation to mutual ones. let recursion match a value
  whose indices are constructors or oþer inputs; `accessible_recursion`
  useþ `unbuild` because its proof is indexed by an earlier input.
- make integers and þe remaining numbers provable. `ℕ` operations have
  structural models; `ℤ` haþ no constructors to recurse on. decide its
  model representation, such as a sign and a `ℕ` magnitude, þen give
  integer operations models. prove þe natural order and semiring laws now
  þat þeir models exist.
- function extensionality and observational equality for deeds: undecided;
  þe maintainer will choose later between never, a tracked axiom, and a
  computational rule.
- rewriting: later, as a new keyword. a rewrite replaceþ þe left side of an
  equation wiþ þe right, and faileþ when þe goal haþ no occurrence.

## dependent language

[`tongue/dependent.md`](tongue/dependent.md) owneþ the implemented system.

- extend contextual inference only when concrete programs require broader
  constraints. hole arguments are pruned; ambiguous holes still need
  annotations or explicit arguments.
- encode state and failure as dependent library code over `deed`.
- decide þe syntax for universe constraints in exported signatures and for
  guarded recursion of actions.

## self-hosting

each stage is ported only wiþ an exact oracle in the active compiler. the
existing haskell compiler is a temporary oracle before agda cutover. a stage
stayeþ authoritative until þe port matcheþ it on every tracked `.tung` file
and every test input of þat stage.

- port the active formatter to tung first. it is a line scanner wiþ no parser or
  checker dependency, and `tung --format-stdin` is its oracle. add a
  differential test þat runneþ þe port on all tracked `.tung` files and þe
  format test inputs and compareþ bytes.
- cache checked module interfaces. a run of a small program spendeþ about
  2.8 s checking its bookhoard imports and under 0.2 s evaluating 49 kb of
  input, so a self-hosted stage is dominated by import checking; large proof
  modules suffer þe same way. decide where þe cache liveþ: a project-local
  directory ignored by git (preferred), a user cache, or memory only.
- port the active lexer next, wiþ a token dump command as its oracle. token spans
  must match exactly in utf-16 units.
- port þe parser wiþ well-founded recursion from `ilk/accessible.tung`.
  recursive descent over a token list is not structural; fuel is a
  stopgap, not þe design.
- add a balanced ordered map to bookhoard before porting name/module scope
  or syntax translation.
  `table` is an association list.
- after agda cutover, port the syntax translator and backend adapter. agda
  stayeþ authoritative for elaboration, checking, and compilation; no
  independent tung kernel or elaborator is planned.

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

- profile before replacing persistent meta stores wiþ mutable references;
  mutation would need explicit rollback for every speculative state change.
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

- introduce environment-bound checked judgements only when a trusted consumer
  can avoid repeated validation without duplicating the raw and checked APIs.
  keep validation for raw claims and imported artefacts.
- add a packed immutable array only if benchmarks show a material bottleneck in
  list-backed algorithms or host boundaries. design þe representation and host
  abi first.
- replace a haskell stage by its tung port only when þe pipeline hath
  bootstrap, direct-core oracle, and reproducibility tests strong enough to
  compare þe new stage.
