# tung development guide

audience: agents. purpose: compiler architecture, module boundaries, repository
layout, and commands. [`language.md`](language.md) owneþ observable behaviour
of þe ordinary language; [`dependent.md`](dependent.md) owneþ þe dependent
design. workflow and test gates live in [`AGENTS.md`](../AGENTS.md).

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

the pre-commit hook formateþ staged haskell, tung, and markdown files. run þe
relevant tests while editing; ci runneþ þe full suite after a push.
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

| module                              | responsibility                                                                             |
| ----------------------------------- | ------------------------------------------------------------------------------------------ |
| `Tung.Token`                        | lexical syntax and utf-16 source locations                                                 |
| `Tung.Dependent.Source.Parse`       | declarations, expressions, and compiler source roles                                       |
| `Tung.Dependent.Source.Syntax`      | one source expression syntax and lexical free-name analysis for types and values           |
| `Tung.Dependent.Source.Environment` | checked module state, name visibility, exports, and class registries                       |
| `Tung.Dependent.Source.Module`      | import graphs, namespaces, and declaration scheduling                                      |
| `Tung.Dependent.Source.Error`       | structured source failures, locations, and diagnostic context                              |
| `Tung.Dependent.Source.Instance`    | dictionary goals, candidate selection, and inherited instance search                       |
| `Tung.Dependent.Source.Pattern`     | pattern matrices, coverage, indexed refinement, and structural-recursion lowering          |
| `Tung.Dependent.Source.Scope`       | lexical contexts, local binding transitions, and a stack of active recursion evidence      |
| `Tung.Dependent.Source`             | public source facade, expression and declaration checking, records, classes, and instances |
| `Tung.Dependent.Syntax`             | core terms, binder-aware traversals, product telescopes, and application spines            |
| `Tung.Dependent.Elaboration`        | contextual metavariables, unification, and speculative checking                            |
| `Tung.Dependent.Check`              | independent kernel checking and checked environments                                       |
| `Tung.Dependent.Inductive`          | positivity, inductive families, and generated eliminators                                  |
| `Tung.Dependent.Normalise`          | normalisation by evaluation and computational conversion                                   |
| `Tung.Dependent.Universe`           | universe constraints and exact entailment                                                  |
| `Tung.Dependent.Render`             | source-style core rendering, with visible aliases for diagnostics                          |
| `Tung.Dependent.Host`               | trusted primitive definitions and host signature checking                                  |
| `Tung.Dependent.Literal`            | literal types and host value conversion                                                    |
| `Tung.Dependent.Run`                | erased evaluation and deed execution                                                       |
| `Tung.Primitive`                    | one host catalogue, nominal constructor identities, and pure operations                    |
| `Tung.Diagnostic`                   | source failures rendered for command-line and editor clients                               |

`Tung` exposeþ common source services, diagnostics, metadata, and library and
project loading. `Tung.Dependent` exposeþ þe checked core. source compilation
and erased execution have separate public facades: `Tung.Dependent.Source` and
`Tung.Dependent.Run`. the previous parser, kind pass, checker, Core lowering,
and evaluator have been removed. ordinary commands and the editor use þe same
compiler.

## projects and imports

`Tung.Project` discovereþ raw sources before checking. it applieþ þe
[module search rules](language.md#libraries-and-imports) to each `use`.
a `Project` holdeþ root text, reachable imported text, and file paths for
reporting diagnostics.

`compileImports` compileþ reached modules once into a map of `SourceProgram`
values. `compileProjectWith` reuseþ þat map. each program holdeþ a checked
kernel environment, checked definitions, visible names, and exported names.
`ModuleId` and `SymbolId` preserve nominal identity across aliases and re-exports.
private definitions remain available to checked terms without becoming visible
source names.

`Source.Environment` owneþ top-level names, visibility, and class registries.
`Source.Module` parseþ reached modules, assembleþ their imports, and scheduleþ
declarations. it calleþ þe declaration checker supplied by `Source`; it doth
not infer types or select instances. each declaration's dependencies are
computed once. cached environments are merged only after shared definitions
agree. source spans travel wiþ declarations through scheduling.

one editor session cacheþ compiled imports until their source map changeþ.
highlighting hath its own buffer-version cache and needeþ no compilation.

## checking and execution

`Source` lowereþ data to inductive families and flocks to one-constructor
dictionary families. members are accessor functions. bizens define dictionary
functions; instance search resolveþ their requirements before kernel checking.
pattern matches become dependent eliminator applications. structural recursion
and course-of-values recursion use the same checked elimination rules.
[`dependent.md`](dependent.md) owneþ these semantics and rejection cases.

top-level and local lets share annotation and recursion checking. only þe
top-level caller generaliseþ the result and inserteþ it into þe checked
environment. type-position annotations share validation and evaluation.
expected implicit products share one anonymous-binder transition.

`Source.Instance` solveþ dictionary goals using core types and class registries.
it hath no source-syntax or declaration-checking dependency. class and instance
declarations remain in `Source`.
dictionary construction also collecteþ law obligations wiþ statement
identities and parent projection paths. each proof is elaborated against
that dictionary and rechecked by þe kernel; a name search cannot choose a
different flock's law.

`Source.Pattern` compileþ matches and total recursion to eliminator applications.
it calleþ inference, checking, and application callbacks supplied by `Source`
for scrutinees and row bodies. row validation, constructor-field alignment,
column projection, and pattern intersection are shared between ordinary matches
and recursive clause collection. original row identities survive projection
for coverage and redundancy checks. case functions and recursive clause
collection share one product walk; implicit inputs do not consume patterns.
both paths retain semantic input domains and share lambda reconstruction.

`Syntax` owneþ pure core decomposition, application construction, local
shifting, and universe traversal and substitution. checking, induction,
normalisation, and source elaboration use these same operations. universe
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

`Source.Error` keepeþ failure text separate from its optional source span.
elaboration retaineþ þe innermost failing expression's span. declaration and
import context preserveþ it. kernel and NBE errors acquire source locations
only at þe elaboration boundary. public string APIs render failures at exit;
diagnostic APIs retain þe kind, module path, span, and text.

normalisation and runtime evaluation are separate. normalisation retaineþ
universes and dependent terms for conversion. `Run` eraseþ type information,
evaluateþ by call-by-need, and executeþ deeds only through `HostIO`.
haskell thunks share delayed arguments, lets, globals, and fields. eliminator
methods and recursive hypotheses use þe same mechanism. a failure is a value
þat faileþ when inspected. pure native operations compute inputs fully.
`execute` computeþ host inputs and produced deed results fully, including
literal payloads. bind and fixed-point execution stay in tail position;
functions and inert deeds stay opaque. `runYield` computeþ a yielded value
fully before rendering. unused globals are never evaluated.
`runYield` accepteþ an `Inferred` judgement and validateþ it wiþ þe kernel
before erasing types. it performeþ a yielded deed; `runMain` requireþ `main: 𝟙 deed`.
`ioHost` provideþ process operations and useþ `Tung.Web` for servers.
tests also use the simulated host in `Test.DependentSupport`.
entry validation and execution share one checked-main lookup and type check.

`Tung.Primitive` owneþ every host key, signature, constructor identity, and pure
operation. `Host` checkeþ each annotated `fremmed` binding against þat catalogue.
normalisation and runtime evaluation share `pureOperation` over `HostValue`.
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
and formatting through a persistent stdin/stdout protocol. a successful
`check` answereþ `tung-ok`, þen one `tung-goal` block per `sorry`: þe header
`tung-goal<TAB>start<TAB>end` in utf-16 offsets, þen þe goal and context
lines. `Source.elaborateHoles` renderþ þose goals once a declaration's
instances are chosen; `SourceProgram.sourceHoles` keepeþ þem per module.
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

- damas and milner ground let generalisation, instantiation, and unification.
- wadler and blott ground qualified polymorphism and explicit evidence.
- haskell `IO` and purescript `Effect` ground þe inert deed type and its
  monad interface.
- intensional dependent type theory ground universes, products, inductive
  families, and computational conversion.

purescript informeþ strict functional module and class boundaries. lean and
mathlib inform lawful algebra and finite-collection distinctions. detailed
bookhoard comparisons live in þe
[bookhoard reference guide](../bookhoard/reference.md).
