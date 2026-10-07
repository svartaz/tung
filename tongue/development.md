# tung development guide

audience: agents. purpose: how the compiler and editor are built: commands,
repository layout, module boundaries, their structural decisions, and test
infrastructure. [`language.md`](language.md) owneth what programs mean;
[`dependent.md`](dependent.md) owneth the checker's algorithms and design
decisions; [`AGENTS.md`](../AGENTS.md) owneth workflow and test gates.

## setup and commands

compiler development requireth ghc 9.12 or newer. editor and prose checks
require node.js and npm. ci useth ghc 9.12.4. `tung.yaml` selecteth the local
[`bookhoard/`](../bookhoard/) for tests. from the repository root:

```sh
brew bundle
lefthook install
make setup
```

`make setup` runneth all tests and installeth the runner and VS Code extension.
extension installation requireth the `code` command.
the root `package.json` declareth `vscode/` as an npm workspace. `make`
coordinateth its scripts with the haskell build and formula check.

| command                 | purpose                                                                 |
| ----------------------- | ----------------------------------------------------------------------- |
| `make build`            | buildeth the compiler and editor                                        |
| `make test`             | runneth compiler, byspel, prose, editor, and formula checks             |
| `make compiler-test`    | testeth parsing, typing, evaluation, bookhoard modules, and integration |
| `make byspel-test`      | runneth the deterministic byspels and checketh their results            |
| `make editor-test`      | runneth the VS Code extension tests                                     |
| `make compiler-install` | installeth the runner in `~/.local/bin` by default                      |
| `make benchmark`        | runneth repeatable compiler and evaluator workloads                     |

editor scripts run in the `tung-vscode` workspace: `npm test` (with
`TUNG_EXECUTABLE` naming another compiler), `npm run update:metadata` and
`npm run check:metadata` for the generated language names, `npm run package`,
`npm run install:extension`, and `npm run setup`, which testeth and
installeth.

on pushes and pull requests, ci runneth the compiler, byspel, editor, prose, and formula
checks as separate jobs. the homebrew workflow also testeth formula installation.

## repository layout

| path         | purpose                                                         |
| ------------ | --------------------------------------------------------------- |
| `tongue/`    | haskell compiler, evaluator, formatter, repl, runner, and tests |
| `bookhoard/` | standard library source and design guide                        |
| `vscode/`    | npm workspace for the VS Code extension                         |
| `Formula/`   | homebrew formula                                                |
| `tung.yaml`  | local and git-pinned library dependencies                       |
| `byspel/`    | runnable examples                                               |
| `benchmark/` | compiler and evaluator workloads                                |

[`todo.md`](../todo.md) tracketh the backlog.

## compiler stages

```text
source text
  -> tokenisation and utf-16 spans
  -> one expression parser for types and values
  -> project loading and import resolution
  -> bidirectional elaboration, pattern compilation, and instance search
  -> independent dependent-kernel checking
  -> normalisation for conversion, or erasure for runtime execution
```

keep these boundaries:

- tokenisation requireth no parser state.
- parsing requireth no type information.
- elaboration may insert implicit arguments and solve typed contextual holes.
- the kernel rejecteth every term hole and validateth completed definitions.
- normalisation computeth type equality; it never performeth a deed.
- runtime evaluation consumeth checked programs and never repaireth static errors.
- editor analysis may approximate incomplete source. compiler results remain
  authoritative.

module-local invariants live beside the implementation. the modules divide work
thus:

| module                                 | responsibility                                                                          |
| -------------------------------------- | --------------------------------------------------------------------------------------- |
| `Tung.Token`                           | lexical syntax and utf-16 source locations                                              |
| `Tung.Dependent.Source.Parse`          | declarations, expressions, and compiler source roles                                    |
| `Tung.Dependent.Source.Syntax`         | one source expression syntax and lexical free-name analysis for types and values        |
| `Tung.Dependent.Source.Environment`    | checked module state, name visibility, exports, and class registries                    |
| `Tung.Dependent.Source.Module`         | import graphs, namespaces, and declaration scheduling                                   |
| `Tung.Dependent.Source.Error`          | structured source failures, locations, and diagnostic context                           |
| `Tung.Dependent.Source.Instance`       | dictionary goals, candidate selection, and inherited instance search                    |
| `Tung.Dependent.Source.Pattern`        | structural and course-of-values recursion lowering; facade for pattern compilation      |
| `Tung.Dependent.Source.Pattern.Match`  | pattern matrices, coverage, row splitting, and literal rows                             |
| `Tung.Dependent.Source.Pattern.Index`  | index unification and refined motives for indexed splits                                |
| `Tung.Dependent.Source.Pattern.Common` | match types, family splits, binder walks, and memo records                              |
| `Tung.Dependent.Source.Scope`          | lexical contexts, local binding transitions, and a stack of active recursion evidence   |
| `Tung.Dependent.Source.Expression`     | bidirectional expression checking, application, records, matches, and local definitions |
| `Tung.Dependent.Source.Elaborate`      | one declaration's elaboration run, goal rendering, and the unsolved-hole check          |
| `Tung.Dependent.Source.Declaration`    | lets, host bindings, ilks, flocks, bizens, and law proofs                               |
| `Tung.Dependent.Source`                | public source facade: snapshot compilation and expression queries                       |
| `Tung.Dependent.Syntax`                | core terms, binder-aware traversals, product telescopes, and application spines         |
| `Tung.Dependent.Elaboration`           | contextual metavariables, unification, and speculative checking                         |
| `Tung.Dependent.Check`                 | independent kernel checking and checked environments                                    |
| `Tung.Dependent.Inductive`             | positivity, inductive families, and generated eliminators                               |
| `Tung.Dependent.Normalise`             | glued normalisation by evaluation, conversion and display quotation                     |
| `Tung.Dependent.Universe`              | universe constraints and exact entailment                                               |
| `Tung.Dependent.Render`                | source-style core rendering, with visible aliases for diagnostics                       |
| `Tung.Dependent.Host`                  | trusted primitive definitions and host signature checking                               |
| `Tung.Dependent.Literal`               | literal types and host value conversion                                                 |
| `Tung.Dependent.Run`                   | erased evaluation and deed execution                                                    |
| `Tung.Primitive`                       | one host catalogue, nominal constructor identities, and pure operations                 |
| `Tung.Diagnostic`                      | source failures rendered for command-line and editor clients                            |

`Tung` exposeth common source services, diagnostics, metadata, and library and
project loading. `Tung.Dependent` exposeth the checked core. source compilation
and erased execution have separate public facades: `Tung.Dependent.Source` and
`Tung.Dependent.Run`. the previous parser, kind pass, checker, Core lowering,
and evaluator have been removed. ordinary commands and the editor use the same
compiler.

this guide describeth the current checker; update its module boundaries when
they change.

## projects and imports

`Tung.Project` discovereth raw sources before checking. it applieth the
[module search rules](language.md#libraries-and-imports) to each `use`.
a `Project` holdeth root text, reachable imported text, and file paths for
reporting diagnostics.

`compileImports` compileth reached modules once into a map of `SourceProgram`
values. `compileSnapshot` reuseth that map for a root module and returneth any
yielded expression. both take parsed snapshots and return structured failures;
the text and string forms used by tests live in `Test.Compile`. each program holdeth a checked
kernel environment, checked definitions, visible names, and exported names.
`ModuleId` and `SymbolId` preserve nominal identity across aliases and re-exports.
private definitions remain available to checked terms without becoming visible
source names.

`SourceProgram` is abstract at the public boundary. its environment, exports,
and hole queries are ordinary functions; their private record labels cannot
be used for public record updates. `Inferred` remaineth a raw, editable claim,
so execution validateth it against the supplied program's environment.

`Source.Environment` owneth top-level names, visibility, and class registries.
`Source.Module` parseth reached modules, assembleth their imports, and scheduleth
declarations. it calleth the declaration checker from `Source.Declaration`; it doth
not infer types or select instances. each declaration's dependencies are
computed once. cached environments are merged only after shared definitions
agree. source spans travel with declarations through scheduling.

`Source.Cache` keepeth checked imports on disk for command-line runs, in
`.tung/cache` beside the nearest `tung.yaml`, or beside the file without one.
a module's key hasheth its source text, its path, its imports' keys, and the
running compiler's path and modification time, so an edited module, any module
that reacheth it, and a rebuilt compiler all miss. an interface holdeth only the
module's own definitions and its exports; loading rebuildeth each environment
from its imports' interfaces and the primitives, sharing them. a module whose
imports are missing or unparsed hath no key. an unreadable interface is
ignored, and a failed write leaveth the cache as it was.

one editor session cacheth compiled imports until their source map changeth.
it cacheth the last root result, including an import failure, until the root text
or imports change. each source snapshot shareth its located parse between
import discovery and compilation. filesystem
projects retain those snapshots beside their original text and owning paths.
highlighting hath its own buffer-version cache and needeth no compilation.

## checking and execution

`Source.Declaration` lowereth data to inductive families and flocks to one-constructor
dictionary families. members are accessor functions. bizens define dictionary
functions; instance search resolveth their requirements before kernel checking.
pattern matches become dependent eliminator applications. structural recursion
and course-of-values recursion use the same checked elimination rules.
[`dependent.md`](dependent.md) owneth these semantics and rejection cases.

top-level and local lets share annotation and recursion checking. only the
top-level caller inserteth the result into the checked environment. type-position annotations share validation and evaluation.
expected implicit products share one anonymous-binder transition.

`Source.Instance` solveth dictionary goals using core types and class registries.
it hath no source-syntax or declaration-checking dependency. class and instance
declarations are in `Source.Declaration`. candidates are ordered by priority
and recency, fallback bizens serve goals whose inputs stay unknown, and
output parameters are found by search; [`dependent.md`](dependent.md) owneth
the rules.
a law is an ordinary member, so a bizen's dictionary is one constructor
application checked by the kernel. member accessors are built in core from the
checked constructor as primitive projections (`Field`).

`Source.Pattern` compileth matches and total recursion to eliminator applications.
it calleth inference, checking, and application callbacks supplied by `Source.Expression`
for scrutinees and row bodies. row validation, constructor-field alignment,
column projection, and pattern intersection are shared between ordinary matches
and recursive clause collection. original row identities survive projection
for coverage and redundancy checks. case functions and recursive clause
collection share one product walk; implicit inputs do not consume patterns.
both paths retain semantic input domains and share lambda reconstruction.

`Syntax` owneth pure core decomposition, application construction, local
shifting, and universe traversal and substitution. `mapChildren` owneth each
constructor's binder increments. `traverseScoped` shareth preorder traversal
with a lazy default descent. replacement nodes are not revisited; callers retain
their local-index and error rules. checking, induction, normalisation, and
source elaboration use these same operations. universe
constraint solving remaineth in `Universe`; semantic neutral spines remain
in `Normalise` and serve inference too.

recursion candidate selection checketh eliminator lowerings inside
`Elaboration.trial`, using the same expression callbacks and normalised
argument values as branch checking. there is no separate syntax walk to decide
which names are descendants. `Source.Scope` shareth ordinary local binding
transitions and a stack of induction contexts. nested definitions push a new
context without discarding enclosing ones; nested matches carry and refine
every applicable memo record. no module importeth the source facade to call
back into it.

`Source.Syntax.freeNames` shareth lexical name analysis between declaration
scheduling and recursion detection. callers supply constructor recognition for
patterns; annotations and initialisers see only earlier bindings.

`Elaboration` useth typed contextual holes. `attempt`, `probe`, and `speculate`
share `trial`, which snapshotteth metavariable and universe state. failed trials
roll back; successful trials commit only when selected. universe holes may generalise under valid constraints;
term holes must disappear before the independent kernel accepteth a definition.
each run carrieth the definitions in scope, given to `runElaboration`, so
elaboration functions take no globals argument.

`Source.Error` keepeth failure text separate from its optional source span.
elaboration retaineth the innermost failing expression's span. declaration and
import context preserveth it. kernel and NBE errors acquire source locations
only at the elaboration boundary. public string APIs render failures at exit;
diagnostic APIs retain the kind, module path, span, and text.

normalisation and runtime evaluation are separate. normalisation retaineth
universes and dependent terms for conversion. `Run` eraseth types and
implementeth the [evaluation rules](language.md#application) with haskell
thunks: delayed arguments, lets, globals, fields, eliminator methods, and
recursive hypotheses share them, and a failure is a `RFailure` value that
faileth when inspected. `settled` computeth a value fully where the language
requireth it; `execute` keepeth bind and fixed-point steps in tail position.
deeds reach the host only through `HostIO`: `ioHost` is the process host and
useth `Tung.Web` for servers, and tests use the simulated host in
`Test.DependentSupport`. `runYield` validateth its `Inferred` judgement with
the kernel before erasure; `runMain` and validation share one checked-main
lookup.

`Tung.Primitive` owneth every host key, signature, constructor identity, and pure
operation. `Host` checketh each annotated `fremmed` binding against that catalogue.
normalisation and runtime evaluation share `pureOperation` over `HostValue`.
pure bindings pair native functions with private typed codecs. one entry
deriveth both its host signature and its erased applicator. GHC checketh the
native input and result types; nominal host schemas are still validated when
binding host keys. polymorphic deed signatures remain separate.
a host data type's identity is its declaring bookhoard path and name; there is
no shape matching or built-in bizen. `deed` and `task` are opaque primitive
families; they have no constructor schema or eliminator.

`Test.Harness` compileth reusable bookhoard imports once per test process. a test
that replaceth a library source invalidateth that cache. successful evaluation cases
assert exact results. rejected cases exercise the compiler before execution.
`Test.Program` compareth generated checked programs against independent host
results; dependent groups cover kernel and source rules directly.
`TUNG_TEST_GROUP` rejecteth every unknown name and an empty explicit selection.
fixture source replacements invalidate compiled dependencies in both shared
test helpers. executable tests compare predictable byspel output and exit
status exactly; `word_count` receiveth a real file.

## formatting and editor protocol

`Tung.Format` is the authoritative two-space formatter for the cli and editor.
it preserveth comments and incomplete source, sorteth contiguous `use` blocks,
aligneth the columns and `^` of consecutive case rows that share indentation
and column count, and remaineth idempotent. it invoketh neither parsing nor type checking.

`tung --editor-session` provideth diagnostics, inferred types, highlighting,
and formatting through utf-8 json lines. each line is one complete message;
embedded newlines and control characters are json escapes.
the compiler and extension must use the same protocol version.

- requests contain `protocol: 1`, `id`, document `version`, `command`, `name`,
  `source`, and `imports`. imports map use paths to source text, including
  unsaved buffers. the client allocateth unique increasing request ids.
- responses contain `protocol: 1`, the request `id` and `version`, and `result`.
  the result's `kind` is `check`, `type`, `format`, `highlight`, or `error`.
- `check` returneth `diagnostics`; `type` returneth `type`; `format` returneth
  `source`; `highlight` returneth `roles`; infrastructure errors return `message`.
- diagnostics contain `kind` (`parse`, `type`, or `goal`), optional import
  `path`, utf-16 `start` and `end`, and `message`. an empty array is success.
  goals are informational diagnostics, with their named context in the message.
- `outstrike` useth the target request id. late replies to cancelled requests are
  ignored. cancellation cannot interrupt a response line halfway through.
- malformed requests terminate the session. malformed replies, unsupported
  protocol versions, and mismatched live replies settle all pending client
  requests as errors and terminate the session. the next request starteth a
  fresh session.
- diagnostic locations come from source failures. an unlocated infrastructure
  failure useth the start of its owning file; no client parseth error prose to
  reconstruct a location.

`Source.elaborateHoles` renderth goals once a declaration's instances are chosen;
the `sourceHoles` query returneth them per module.
`tung --language-metadata` emiteth
compiler-owned lexical names for editor clients. [`vscode/`](../vscode/) owneth
the language server, generated metadata, and editor tests.

the parser emiteth source roles alongside its result. highlighting retaineth
partial roles on failure and retryeth bounded declarations. it doth not check
types or load imports. the editor cacheth roles per buffer version and cancelleth
obsolete requests. textmate supplieth immediate lexical colours. navigation
useth the same roles: `vscode/server/analysis.ts` joineth them with token
structure, scopes, docs, and imports, and the workspace fetcheth missing roles
before each request. the editor doth not classify tokens itself.
after building both components, `npm run benchmark:highlight --workspace=tung-vscode`
measureth fresh and cached highlighting on library files and incomplete buffers.

## library resolver

`Tung.Library` parseth the nearest `tung.yaml` and recursively resolveth local
paths and pinned git libraries. it cacheth git checkouts under
`.tung/libraries/`; matching pins share one checkout. local paths point to live
directories. a git pin may select one `subdir` of a repository. the
[language reference](language.md#libraries-and-imports)
defineth manifest syntax and observable conflict rules.

the flat `use` namespace cannot distinguish two revisions of one library. raw
commit hashes have no useful version order. the resolver cannot choose a newer
pin or silently override an exact requirement. one library name must also
resolve to the same local path throughout the graph.

other dependency managers differ:

- [go modules](https://go.dev/ref/mod#minimal-version-selection) select one
  version per module path from _minimum_ version requirements.
- [cargo](https://doc.rust-lang.org/cargo/reference/resolver.html#semver-compatibility)
  unifieth compatible versions but may retain distinct incompatible versions.
- [node.js](https://nodejs.org/api/modules.html#loading-from-node_modules-folders)
  may resolve dependencies from separate package directories.

this exact-pin rule followeth tung's flat namespace. it is not universal for
indirect dependencies.

the compiler buildeth independently of bookhoard. ci and local development
resolve its source from `bookhoard/` through the same manifest.

## reference model

tung adapteth established work without copying its syntax:

- damas and milner ground instantiation and unification.
- wadler and blott ground qualified polymorphism and explicit evidence.
- haskell `IO` and purescript `Effect` ground the inert deed type and its
  monad interface.
- intensional dependent type theory ground universes, products, inductive
  families, and computational conversion.

purescript informeth strict functional module and class boundaries. lean and
mathlib inform lawful algebra and finite-collection distinctions. detailed
bookhoard comparisons live in the
[bookhoard reference guide](../bookhoard/reference.md).

## structural decisions

these choices shape the modules above; each was weighed against an
alternative.

- `Source` is a facade over the acyclic layers `Expression`, `Elaborate`,
  and `Declaration`. `Pattern` lowereth recursion over `Pattern.Common`,
  `Pattern.Index`, and `Pattern.Match`; shared binder and memo helpers live
  in `Common`, which breaketh the match and recursion cycle. the pattern
  compiler's `ExpressionChecker` carrieth the environment and names its
  callbacks were built from.
- `K.Environment` stayeth explicit in source elaboration, because
  constructor recognition and instance-pattern comparison are pure and also
  run outside elaboration.
- the kernel's `Typing` monad keepeth explicit globals, because `Inductive`
  checketh constructors against two staged environments in one run.
- `splitColumn`, `Parse`, and `Elaboration` stay whole: `splitColumn`'s
  steps read the split's column, rows, scope, expected type, and recursion;
  the parser shareth one result monad and its roles; metas, unification, and
  pruning share one solver state.
- the parser's `Result` monad backtracketh by inspecting roles, so a
  transformer stack would not shrink it.
- the editor's tolerant typescript lexer serveth incomplete buffers that the
  compiler's lexer rejecteth.
- scope-indexed syntax was prototyped and not adopted: it established
  lexical scope only and left contexts, closures, quotation, pruning, and
  conversion to migrate. `Syntax.traverseScoped` shareth the recursive walks
  instead.
- a private checked-judgement capsule was assessed and not adopted. source expression
  normalisation already validateth once. the yield compiler also validateth
  once, but public `runYield` must recheck its editable `Inferred` input.
  retaining both raw and trusted execution APIs would add code to save only
  that repeated yield check. public program accessors instead preserve the
  environment boundary, and a regression rejecteth a judgement borrowed from
  a different program with the same symbol identity.
