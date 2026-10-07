# todo

this backlog tracketh planned work in the compiler, editor, and bookhoard
library. active work appeareth in priority order. deferred gates
depend on later evidence.

## agda delegation

- begin stage 1 of the [agda delegation plan](tongue/dependent.md#agda-delegation-plan):
  freeze the simplified compiler, inventory compatibility, measure costs,
  and pin an isolated backend. reuse the completed source snapshots,
  structured protocol, and caches. follow the plan's gates before replacing
  the handwritten haskell engine; no delegation stage is complete.

## theorem proving

[`tongue/dependent.md`](tongue/dependent.md#proving-status) summariseth what
proofs can use now. the maintainer decided the direction of each item below;
open choices are marked.

- recover checking speed. `byspel/word_count.tung` checketh in about 16 s,
  against about 11 s before laws became dictionary fields; global lookups
  compare symbol names as strings, and neutral reduction remaineth large.
- use requirement laws in bookhoard: the component-law rows in
  [`reference.md`](bookhoard/reference.md#law-proofs) may now be proved.
- extend recursion. `ilk/accessible.tung` provideth well-founded recursion
  through an accessibility family. later, if wanted, add a measure
  annotation compiled to it. support mutual families implied by a dependency
  cycle of ilks (preferred over an explicit group), then nested families such
  as `rose list` by translation to mutual ones. let recursion match a value
  whose indices are constructors or other inputs; `accessible~selfcalling`
  useth `unbuild` because its proof is indexed by an earlier input.
- function extensionality and observational equality for deeds: undecided;
  the maintainer will choose later between never, a tracked axiom, and a
  computational rule.
- rewriting: later, as a new keyword. a rewrite replaceth the left side of an
  equation with the right, and faileth when the goal hath no occurrence.

## dependent language

[`tongue/dependent.md`](tongue/dependent.md) owneth the implemented system.

- extend contextual inference only when concrete programs require broader
  constraints. hole arguments are pruned; ambiguous holes still need
  annotations or explicit arguments.
- encode state and failure as dependent library code over `deed`.
- decide the syntax for universe constraints in exported signatures and for
  guarded recursion of actions.

## self-hosting

each stage is ported only with an exact oracle in the active compiler. the
existing haskell compiler is a temporary oracle before agda cutover. a stage
stayeth authoritative until the port matcheth it on every tracked `.tung` file
and every test input of that stage.

- port the active formatter to tung first. it is a line scanner with no parser or
  checker dependency, and `tung --format-stdin` is its oracle. add a
  differential test that runneth the port on all tracked `.tung` files and the
  format test inputs and compareth bytes.
- cache checked module interfaces. a run of a small program spendeth about
  2.8 s checking its bookhoard imports and under 0.2 s evaluating 49 kb of
  input, so a self-hosted stage is dominated by import checking; large proof
  modules suffer the same way. decide where the cache liveth: a project-local
  directory ignored by git (preferred), a user cache, or memory only.
- port the active lexer next, with a token dump command as its oracle. token spans
  must match exactly in utf-16 units.
- port the parser with well-founded recursion from `ilk/accessible.tung`.
  recursive descent over a token list is not structural; fuel is a
  stopgap, not the design.
- add a balanced ordered map to bookhoard before porting name/module scope
  or syntax translation.
  `table` is an association list.
- after agda cutover, port the syntax translator and backend adapter. agda
  stayeth authoritative for elaboration, checking, and compilation; no
  independent tung kernel or elaborator is planned.

## correctness

- measure test time and peak memory after shared dependent import compilation.
- extend `Test.Program` with varied generated matches, records, dictionaries,
  imports, and deeds, using independent host results.
- add laws for selected bookhoard bizens to the deterministic quickcheck harness.
  start with `𝟚` equality, partial order, and total order. then check functor,
  applicative, and monad laws for bounded lists and options. the compiler
  checketh and eraseth flock proofs; runtime tests check their equations. print generated tung source for
  every counterexample.
- generate small acyclic module graphs. canonical term, type, flock, and
  bizen identities must survive declaration and import reordering. include
  aliases, re-exports, private name collisions, and transitive imports of the
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
  that the installed runner resolveth a git-pinned Bookhoard through `tung.yaml`
  and that the packaged extension connecteth to the installed compiler.
- after publishing the monorepo, update `Formula/tung.rb` to a commit with the
  manifest-based library resolver. test the installed formula with an external
  Bookhoard pin.
- choose a licence. declare the github repository in cabal metadata. define a
  compatible release-version policy with `vscode/`. then add changelogs and
  signed runner artefacts.

## modules and packages

- define package identities, version constraints, and lockfiles before adding a
  registry or package manager. keep the current exact-commit and local-path
  conflict rules until a version resolver hath explicit rules for transitive
  requirements and incompatible duplicates.
- define how same-named shown items from different packages affect
  qualify-if-needed lookup.

## bookhoard

these tasks belong to [`bookhoard/`](bookhoard/).

- strengthen order assumptions so boolean equality implyth identity when
  proving generic min/max laws. repair the list-backed set's representation
  and membership assumptions before claiming its extensional algebra laws;
  [`reference.md`](bookhoard/reference.md#law-proofs) giveth counterexamples.
- add first, last, and reversed monoid carriers without burdening the core monoid
  flock.
- implement the order-insensitive bag as an opaque, ordered list of distinct
  positive-count pairs, sorted by value. keep its constructor private and
  publish only the type. require `order_whole` smart constructors to preserve
  strict order and omit zero counts. equality and rendering must ignore
  insertion order. quotient types are not required.

## deferred gates

- add a packed immutable array only if benchmarks show a material bottleneck in
  list-backed algorithms or host boundaries. design the representation and host
  abi first.
- replace a haskell stage by its tung port only when the pipeline hath
  bootstrap, direct-core oracle, and reproducibility tests strong enough to
  compare the new stage.
