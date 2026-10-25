# todo

planned work in priority order. current behaviour belongeth to the
[language reference](tongue/language.md), checker design to
[dependent.md](tongue/dependent.md), and workflow to
[development.md](tongue/development.md).

## dependent language

- universe levels stay fully implicit; there is no level syntax. report an
  inconsistent universe as the source `*` occurrences and definitions that
  would make a universe contain itself, and show inferred universe signatures
  in hover and `--name` in that form.
- report when a shown name's inferred universe constraints change, beside the
  module interface cache, since importers depend on them.

## self-hosting

the haskell stage stayeth authoritative until its tung port matcheth every
tracked `.tung` file and stage test input against an exact oracle.

- port the active lexer first, with a token dump command as its oracle. token
  spans must match exactly in utf-16 units.
- port the parser with well-founded recursion from `type/grounded.tung`.
  recursive descent over a token list is not structural; fuel is a
  stopgap, not the design.
- port the tidier after them, since it readeth tokens, comments, and the
  parse. `tung --tidy-stdin` is its oracle: a differential test runneth the
  port on all tracked `.tung` files and the tidy test inputs and compareth
  bytes.

## tooling and maintainability

- reduce repeated normalisation and allocation in large proof checks; instance
  search is the next measured cost after universe solving. preserve inferred
  universe constraints and kernel rechecking.
- pin a hackage index state for cabal in ci. keep local dependency refresh
  separate from ci checks.

## release

- add windows ci jobs beside ubuntu and macos. handle executable suffixes,
  temporary paths, path separators, and the makefile's shell commands.
- build and test runner and extension artefacts from a clean checkout. check
  that the installed runner resolveth a git-pinned library through `tung.yaml`
  and that the packaged extension connecteth to the installed compiler.
- after publishing the monorepo, update `Formula/tung.rb` to that commit and
  test the installed formula with an external library pin.
- define a release-version policy shared by `tongue/` and `vscode/`. then add
  changelogs and signed runner artefacts.

## modules and packages

- define package identities, version constraints, and lockfiles before adding a
  registry or package manager. keep the current exact-commit and local-path
  conflict rules until a version resolver hath explicit rules for transitive
  requirements and incompatible duplicates.
- define how same-named shown items from different packages affect
  qualify-if-needed lookup.

## library

these tasks belong to [`library/`](library/).

- add first, last, and reversed monoid carriers without burdening the core monoid
  class.
- implement the order-insensitive bag as an opaque, ordered list of distinct
  positive-count pairs, sorted by value. keep its constructor private and
  publish only the type. require `order_total` smart constructors to preserve
  strict order and omit zero counts. equality and rendering must be
  independent of the order in which values were added. quotient types are not required.

## deferred gates

- a free inductive `effect`, whose laws would follow by induction, needeth
  coinduction while `fast` existeth, since an unbounded self-call could build
  an ill-founded inductive effect. until then the three effect axioms stay.
- add a packed immutable array only if benchmarks show a material bottleneck in
  list-backed algorithms or host boundaries. design the representation and host
  abi first.
- replace a haskell stage by its tung port only when the pipeline hath
  bootstrap, direct-core oracle, and reproducibility tests strong enough to
  compare the new stage.
