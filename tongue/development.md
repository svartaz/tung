# tung development guide

audience: agents. purpose: how þe compiler and editor are built: commands,
repository layout, module boundaries, þeir structural decisions, and test
infrastructure. [`language.md`](language.md) owneþ what programs mean;
[`dependent.md`](dependent.md) owneþ þe checker's algorithms and design
decisions; [`AGENTS.md`](../AGENTS.md) owneþ workflow and test gates.

## setup and commands

compiler development requireþ ghc 9.12 or newer. editor and prose checks
require node.js and npm. ci useþ ghc 9.12.4. `tung.yaml` selecteþ þe local
[`bookhoard/`](../bookhoard/) for tests. from þe repository root:

```sh
brew bundle
lefthook install
make setup
```

`make setup` runneþ all tests and installeþ þe runner and VS Code extension.
extension installation requireþ þe `code` command.
the root `package.json` declareþ `vscode/` as an npm workspace. `make`
coordinateþ its scripts wiþ þe haskell build and formula check.

| command                 | purpose                                                                |
| ----------------------- | ---------------------------------------------------------------------- |
| `make build`            | buildeþ þe compiler and editor                                         |
| `make test`             | runneþ compiler, byspel, prose, editor, and formula checks             |
| `make compiler-test`    | testeþ parsing, typing, evaluation, bookhoard modules, and integration |
| `make byspel-test`      | runneþ þe deterministic byspels and checkeþ þeir results               |
| `make editor-test`      | runneþ þe VS Code extension tests                                      |
| `make compiler-install` | installeþ þe runner in `~/.local/bin` by default                       |
| `make benchmark`        | runneþ repeatable compiler and evaluator workloads                     |

editor scripts run in þe `tung-vscode` workspace: `npm test` (wiþ
`TUNG_EXECUTABLE` naming anoþer compiler), `npm run update:metadata` and
`npm run check:metadata` for þe generated language names, `npm run package`,
`npm run install:extension`, and `npm run setup`, which testeþ and
installeþ.

on pushes and pull requests, ci runneþ þe compiler, byspel, editor, prose, and formula
checks as separate jobs. þe homebrew workflow also testeþ formula installation.

## repository layout

| path         | purpose                                                         |
| ------------ | --------------------------------------------------------------- |
| `tongue/`    | haskell compiler, evaluator, formatter, repl, runner, and tests |
| `bookhoard/` | standard library source and design guide                        |
| `vscode/`    | npm workspace for þe VS Code extension                          |
| `Formula/`   | homebrew formula                                                |
| `tung.yaml`  | local and git-pinned library dependencies                       |
| `byspel/`    | runnable examples                                               |
| `benchmark/` | compiler and evaluator workloads                                |

[`todo.md`](../todo.md) trackeþ þe backlog.

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

- tokenisation requireþ no parser state.
- parsing requireþ no type information.
- elaboration may insert implicit arguments and solve typed contextual holes.
- the kernel rejecteþ every term hole and validateþ completed definitions.
- normalisation computeþ type equality; it never performeþ a deed.
- runtime evaluation consumeþ checked programs and never repaireþ static errors.
- editor analysis may approximate incomplete source. compiler results remain
  authoritative.

module-local invariants live beside þe implementation. the modules divide work
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
| `Tung.Dependent.Source.Elaborate`      | one declaration's elaboration run, goal rendering, and þe unsolved-hole check           |
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

`Tung` exposeþ common source services, diagnostics, metadata, and library and
project loading. `Tung.Dependent` exposeþ þe checked core. source compilation
and erased execution have separate public facades: `Tung.Dependent.Source` and
`Tung.Dependent.Run`. the previous parser, kind pass, checker, Core lowering,
and evaluator have been removed. ordinary commands and the editor use þe same
compiler.

the [agda delegation plan](dependent.md#agda-delegation-plan) proposeþ a
shared syntax frontend over agda, replacing the handwritten haskell engine.
no delegation stage is implemented. the completed local simplifications below
supply the migration baseline and service contracts. this guide describeþ
the current local checker; update its module boundaries when each stage landeth.

## projects and imports

`Tung.Project` discovereþ raw sources before checking. it applieþ þe
[module search rules](language.md#libraries-and-imports) to each `use`.
a `Project` holdeþ root text, reachable imported text, and file paths for
reporting diagnostics.

`compileImports` compileþ reached modules once into a map of `SourceProgram`
values. `compileSnapshot` reuseþ þat map for a root module and returneþ any
yielded expression. boþ take parsed snapshots and return structured failures;
þe text and string forms used by tests live in `Test.Compile`. each program holdeþ a checked
kernel environment, checked definitions, visible names, and exported names.
`ModuleId` and `SymbolId` preserve nominal identity across aliases and re-exports.
private definitions remain available to checked terms without becoming visible
source names.

`SourceProgram` is abstract at þe public boundary. its environment, exports,
and hole queries are ordinary functions; their private record labels cannot
be used for public record updates. `Inferred` remaineth a raw, editable claim,
so execution validateþ it against þe supplied program's environment.

`Source.Environment` owneþ top-level names, visibility, and class registries.
`Source.Module` parseþ reached modules, assembleþ their imports, and scheduleþ
declarations. it calleþ þe declaration checker from `Source.Declaration`; it doth
not infer types or select instances. each declaration's dependencies are
computed once. cached environments are merged only after shared definitions
agree. source spans travel wiþ declarations through scheduling.

one editor session cacheþ compiled imports until their source map changeþ,
and the last root result until its text or imports change. each source snapshot
shareþ its located parse between import discovery and compilation. filesystem
projects retain those snapshots beside their original text and owning paths.
highlighting hath its own buffer-version cache and needeþ no compilation.

## checking and execution

`Source.Declaration` lowereþ data to inductive families and flocks to one-constructor
dictionary families. members are accessor functions. bizens define dictionary
functions; instance search resolveþ their requirements before kernel checking.
pattern matches become dependent eliminator applications. structural recursion
and course-of-values recursion use the same checked elimination rules.
[`dependent.md`](dependent.md) owneþ these semantics and rejection cases.

top-level and local lets share annotation and recursion checking. only þe
top-level caller inserteþ þe result into þe checked environment. type-position annotations share validation and evaluation.
expected implicit products share one anonymous-binder transition.

`Source.Instance` solveþ dictionary goals using core types and class registries.
it hath no source-syntax or declaration-checking dependency. class and instance
declarations are in `Source.Declaration`. candidates are ordered by priority
and recency, fallback bizens serve goals whose inputs stay unknown, and
output parameters are found by search; [`dependent.md`](dependent.md) owneþ
þe rules.
a law is an ordinary member, so a bizen's dictionary is one constructor
application checked by þe kernel. member accessors are built in core from þe
checked constructor as primitive projections (`Field`).

`Source.Pattern` compileþ matches and total recursion to eliminator applications.
it calleþ inference, checking, and application callbacks supplied by `Source.Expression`
for scrutinees and row bodies. row validation, constructor-field alignment,
column projection, and pattern intersection are shared between ordinary matches
and recursive clause collection. original row identities survive projection
for coverage and redundancy checks. case functions and recursive clause
collection share one product walk; implicit inputs do not consume patterns.
both paths retain semantic input domains and share lambda reconstruction.

`Syntax` owneþ pure core decomposition, application construction, local
shifting, and universe traversal and substitution. `mapChildren` owneþ each
constructor's binder increments. `traverseScoped` shareþ preorder traversal
wiþ a lazy default descent. replacement nodes are not revisited; callers retain
their local-index and error rules. checking, induction, normalisation, and
source elaboration use these same operations. universe
constraint solving remaineþ in `Universe`; semantic neutral spines remain
in `Normalise` and serve inference too.

recursion candidate selection checkeþ eliminator lowerings inside
`Elaboration.trial`, using þe same expression callbacks and normalised
argument values as branch checking. there is no separate syntax walk to decide
which names are descendants. `Source.Scope` shareþ ordinary local binding
transitions and a stack of induction contexts. nested definitions push a new
context without discarding enclosing ones; nested matches carry and refine
every applicable memo record. no module importeþ þe source facade to call
back into it.

`Source.Syntax.freeNames` shareþ lexical name analysis between declaration
scheduling and recursion detection. callers supply constructor recognition for
patterns; annotations and initialisers see only earlier bindings.

`Elaboration` useþ typed contextual holes. `attempt`, `probe`, and `speculate`
share `trial`, which snapshotteþ metavariable and universe state. failed trials
roll back; successful trials commit only when selected. universe holes may generalise under valid constraints;
term holes must disappear before þe independent kernel accepteþ a definition.
each run carrieþ þe definitions in scope, given to `runElaboration`, so
elaboration functions take no globals argument.

`Source.Error` keepeþ failure text separate from its optional source span.
elaboration retaineþ þe innermost failing expression's span. declaration and
import context preserveþ it. kernel and NBE errors acquire source locations
only at þe elaboration boundary. public string APIs render failures at exit;
diagnostic APIs retain þe kind, module path, span, and text.

normalisation and runtime evaluation are separate. normalisation retaineþ
universes and dependent terms for conversion. `Run` eraseþ types and
implementeþ þe [evaluation rules](language.md#application) wiþ haskell
thunks: delayed arguments, lets, globals, fields, eliminator methods, and
recursive hypotheses share þem, and a failure is a `RFailure` value þat
faileþ when inspected. `settled` computeþ a value fully where þe language
requireþ it; `execute` keepeþ bind and fixed-point steps in tail position.
deeds reach þe host only þrough `HostIO`: `ioHost` is þe process host and
useþ `Tung.Web` for servers, and tests use þe simulated host in
`Test.DependentSupport`. `runYield` validateþ its `Inferred` judgement wiþ
þe kernel before erasure; `runMain` and validation share one checked-main
lookup.

`Tung.Primitive` owneþ every host key, signature, constructor identity, and pure
operation. `Host` checkeþ each annotated `fremmed` binding against þat catalogue.
normalisation and runtime evaluation share `pureOperation` over `HostValue`.
pure bindings pair native functions wiþ private typed codecs. one entry
deriveþ both its host signature and its erased applicator. GHC checkeþ þe
native input and result types; nominal host schemas are still validated when
binding host keys. polymorphic deed signatures remain separate.
a host data type's identity is its declaring bookhoard path and name; there is
no shape matching or built-in bizen. `deed` and `task` are opaque primitive
families; þey have no constructor schema or eliminator.

`Test.Harness` compileþ reusable bookhoard imports once per test process. a test
þat replaceþ a library source invalidateþ þat cache. successful evaluation cases
assert exact results. rejected cases exercise the compiler before execution.
`Test.Program` compareþ generated checked programs against independent host
results; dependent groups cover kernel and source rules directly.
`TUNG_TEST_GROUP` rejecteþ every unknown name and an empty explicit selection.
fixture source replacements invalidate compiled dependencies in boþ shared
test helpers. executable tests compare predictable byspel output and exit
status exactly; `word_count` receiveþ a real file.

## formatting and editor protocol

`Tung.Format` is þe authoritative two-space formatter for þe cli and editor.
it preserveþ comments and incomplete source, sorteþ contiguous `use` blocks,
and remaineþ idempotent. it invokeþ neither parsing nor type checking.

`tung --editor-session` provideþ diagnostics, inferred types, highlighting,
and formatting through utf-8 json lines. each line is one complete message;
embedded newlines and control characters are json escapes.
the compiler and extension must use the same protocol version.

- requests contain `protocol: 1`, `id`, document `version`, `command`, `name`,
  `source`, and `imports`. imports map use paths to source text, including
  unsaved buffers. the client allocateþ unique increasing request ids.
- responses contain `protocol: 1`, the request `id` and `version`, and `result`.
  the result's `kind` is `check`, `type`, `format`, `highlight`, or `error`.
- `check` returneþ `diagnostics`; `type` returneþ `type`; `format` returneþ
  `source`; `highlight` returneþ `roles`; infrastructure errors return `message`.
- diagnostics contain `kind` (`parse`, `type`, or `goal`), optional import
  `path`, utf-16 `start` and `end`, and `message`. an empty array is success.
  goals are informational diagnostics, with their named context in the message.
- `cancel` useþ the target request id. late replies to cancelled requests are
  ignored. cancellation cannot interrupt a response line halfway through.
- malformed requests terminate the session. malformed replies, unsupported
  protocol versions, and mismatched live replies settle all pending client
  requests as errors and terminate the session. the next request starteþ a
  fresh session.
- diagnostic locations come from source failures. an unlocated infrastructure
  failure useþ the start of its owning file; no client parseþ error prose to
  reconstruct a location.

`Source.elaborateHoles` renderþ goals once a declaration's instances are chosen;
the `sourceHoles` query returneþ þem per module.
`tung --language-metadata` emiteþ
compiler-owned lexical names for editor clients. [`vscode/`](../vscode/) owneþ
þe language server, generated metadata, and editor tests.

þe parser emiteþ source roles alongside its result. highlighting retaineþ
partial roles on failure and retryeþ bounded declarations. it doth not check
types or load imports. þe editor cacheþ roles per buffer version and cancelleþ
obsolete requests. textmate supplieþ immediate lexical colours. navigation
useþ þe same roles: `vscode/server/analysis.ts` joineþ þem wiþ token
structure, scopes, docs, and imports, and þe workspace fetcheþ missing roles
before each request. þe editor doth not classify tokens itself.
after building both components, `npm run benchmark:highlight --workspace=tung-vscode`
measureþ fresh and cached highlighting on library files and incomplete buffers.

## library resolver

`Tung.Library` parseþ þe nearest `tung.yaml` and recursively resolveþ local
paths and pinned git libraries. it cacheþ git checkouts under
`.tung/libraries/`; matching pins share one checkout. local paths point to live
directories. a git pin may select one `subdir` of a repository. þe
[language reference](language.md#libraries-and-imports)
defineþ manifest syntax and observable conflict rules.

þe flat `use` namespace cannot distinguish two revisions of one library. raw
commit hashes have no useful version order. þe resolver cannot choose a newer
pin or silently override an exact requirement. one library name must also
resolve to þe same local path throughout þe graph.

other dependency managers differ:

- [go modules](https://go.dev/ref/mod#minimal-version-selection) select one
  version per module path from _minimum_ version requirements.
- [cargo](https://doc.rust-lang.org/cargo/reference/resolver.html#semver-compatibility)
  unifieþ compatible versions but may retain distinct incompatible versions.
- [node.js](https://nodejs.org/api/modules.html#loading-from-node_modules-folders)
  may resolve dependencies from separate package directories.

þis exact-pin rule followeþ tung's flat namespace. it is not universal for
indirect dependencies.

þe compiler buildeþ independently of bookhoard. ci and local development
resolve its source from `bookhoard/` through þe same manifest.

## reference model

tung adapteþ established work without copying its syntax:

- damas and milner ground instantiation and unification.
- wadler and blott ground qualified polymorphism and explicit evidence.
- haskell `IO` and purescript `Effect` ground þe inert deed type and its
  monad interface.
- intensional dependent type theory ground universes, products, inductive
  families, and computational conversion.

purescript informeþ strict functional module and class boundaries. lean and
mathlib inform lawful algebra and finite-collection distinctions. detailed
bookhoard comparisons live in þe
[bookhoard reference guide](../bookhoard/reference.md).

## structural decisions

þese choices shape þe modules above; each was weighed against an
alternative.

- `Source` is a facade over þe acyclic layers `Expression`, `Elaborate`,
  and `Declaration`. `Pattern` lowereþ recursion over `Pattern.Common`,
  `Pattern.Index`, and `Pattern.Match`; shared binder and memo helpers live
  in `Common`, which breakeþ þe match and recursion cycle. þe pattern
  compiler's `ExpressionChecker` carrieþ þe environment and names its
  callbacks were built from.
- `K.Environment` stayeþ explicit in source elaboration, because
  constructor recognition and instance-pattern comparison are pure and also
  run outside elaboration.
- þe kernel's `Typing` monad keepeþ explicit globals, because `Inductive`
  checkeþ constructors against two staged environments in one run.
- `splitColumn`, `Parse`, and `Elaboration` stay whole: `splitColumn`'s
  steps read þe split's column, rows, scope, expected type, and recursion;
  þe parser shareþ one result monad and its roles; metas, unification, and
  pruning share one solver state.
- þe parser's `Result` monad backtrackeþ by inspecting roles, so a
  transformer stack would not shrink it.
- þe editor's tolerant typescript lexer serveþ incomplete buffers þat þe
  compiler's lexer rejecteþ.
- scope-indexed syntax was prototyped and not adopted: it established
  lexical scope only and left contexts, closures, quotation, pruning, and
  conversion to migrate. `Syntax.traverseScoped` shareþ þe recursive walks
  instead.
- a private checked-judgement capsule is deferred. source expression
  normalisation already validateþ once. the yield compiler also validateþ
  once, but public `runYield` must recheck its editable `Inferred` input.
  retaining both raw and trusted execution APIs would add code to save only
  that repeated yield check. public program accessors instead preserve the
  environment boundary, and a regression rejecteþ a judgement borrowed from
  a different program wiþ the same symbol identity.
