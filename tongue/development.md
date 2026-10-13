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
mise install
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
| `make check`            | runneth `make test`, `make neaten-check`, and `git diff --check`        |
| `make neaten-check`     | checketh ormolu and canonical tung neatening without changing files     |
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

| path         | purpose                                                          |
| ------------ | ---------------------------------------------------------------- |
| `tongue/`    | haskell compiler, evaluator, neatener, repl, runner, and tests   |
| `bookhoard/` | standard library source and design guide                         |
| `vscode/`    | npm workspace for the VS Code extension                          |
| `Formula/`   | homebrew formula                                                 |
| `tung.yaml`  | local and git-pinned library dependencies                        |
| `byspel/`    | checked examples, including the walkthrough and checker fixtures |
| `benchmark/` | compiler and evaluator workloads                                 |

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

| module                                 | responsibility                                                                                      |
| -------------------------------------- | --------------------------------------------------------------------------------------------------- |
| `Tung.Token`                           | lexical syntax and utf-16 source locations                                                          |
| `Tung.Dependent.Source.Parse`          | declarations, expressions, and compiler source roles                                                |
| `Tung.Dependent.Source.Syntax`         | one source expression syntax and lexical free-name analysis for types and values                    |
| `Tung.Dependent.Source.Environment`    | checked module state, checking references, name visibility, exports, and class registries           |
| `Tung.Dependent.Source.Proof`          | theorem dependency closure, assumption auditing, and axiom policy checking                          |
| `Tung.Dependent.Source.Render`         | type-directed field names in source types, goals, and proof audits                                  |
| `Tung.Dependent.Source.Module`         | import graphs, namespaces, and declaration scheduling                                               |
| `Tung.Dependent.Source.Error`          | structured source failures, locations, and diagnostic context                                       |
| `Tung.Dependent.Source.Instance`       | dictionary goals, candidate selection, and inherited instance search                                |
| `Tung.Dependent.Source.Pattern`        | structural and course-of-values recursion lowering; facade for pattern compilation                  |
| `Tung.Dependent.Source.Pattern.Match`  | pattern matrices, coverage, row splitting, and literal rows                                         |
| `Tung.Dependent.Source.Pattern.Index`  | index unification and refined motives for indexed splits                                            |
| `Tung.Dependent.Source.Pattern.Common` | match types, family splits, binder walks, and memo records                                          |
| `Tung.Dependent.Source.Scope`          | lexical contexts, local binding transitions, and a stack of active recursion evidence               |
| `Tung.Dependent.Source.Expression`     | bidirectional expression checking, application, field access, matches, and local definitions        |
| `Tung.Dependent.Source.Elaborate`      | one declaration's elaboration run, checking references, goal rendering, and the unsolved-hole check |
| `Tung.Dependent.Source.Declaration`    | lets, host bindings, ilks, flocks, bizens, and law proofs                                           |
| `Tung.Dependent.Source`                | public source facade: snapshot compilation and expression queries                                   |
| `Tung.Dependent.Syntax`                | core terms, binder-aware traversals, product telescopes, and application spines                     |
| `Tung.Dependent.Elaboration`           | contextual metavariables, unification, and speculative checking                                     |
| `Tung.Dependent.Check`                 | independent kernel checking and checked environments                                                |
| `Tung.Dependent.Inductive`             | positivity, nested specialisation, and checked eliminator rules                                     |
| `Tung.Dependent.Normalise`             | glued normalisation by evaluation, conversion and display quotation                                 |
| `Tung.Dependent.Universe`              | universe constraints and exact entailment                                                           |
| `Tung.Dependent.Render`                | source-style core rendering, with visible aliases for diagnostics                                   |
| `Tung.Dependent.Host`                  | trusted primitive definitions and host signature checking                                           |
| `Tung.Dependent.Literal`               | literal types and host value conversion                                                             |
| `Tung.Dependent.Run`                   | erased evaluation and deed execution                                                                |
| `Tung.Primitive`                       | one host catalogue, nominal constructor identities, and pure operations                             |
| `Tung.Diagnostic`                      | source failures rendered for command-line and editor clients                                        |

`Tung` exposeth common source services, diagnostics, metadata, and library and
project loading. `Tung.Dependent` exposeth the checked core. source compilation
and erased execution have separate public facades: `Tung.Dependent.Source` and
`Tung.Dependent.Run`. ordinary commands and the editor use the same compiler.

## projects and imports

`Tung.Project` discovereth raw sources before checking. it applieth the
[module search rules](language.md#libraries-and-imports) to each `bring`.
a `Project` holdeth root text, reachable imported text, and file paths for
reporting diagnostics.

`compileImports` compileth reached modules once into a map of `SourceProgram`
values. `compileSnapshot` reuseth that map for a root module and returneth any
yielded expression. both take parsed snapshots and return structured failures;
test adapters live in `Test.Compile`. each program holdeth a checked kernel
environment, visible names, and exported names.
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

`Source.Module` groupeth strongly connected declarations. all-ilk components
are checked atomically; other declaration cycles are rejected. `Inductive`
owneth the joint and nested-family certificates described in
[dependent.md](dependent.md#inductive-declarations-and-proofs).

`Identity.internSymbols` reuseth definition keys through a pure table that
holdeth only identities. `Source.Environment` interneth a newly checked module's
own bodies, metadata, checking references, names, and class registries.
recorded checking results
share those rewritten bodies. imported definitions are not walked again.

`Source.Cache` keepeth checked imports on disk for command-line runs, in
`.tung/cache` beside the nearest `tung.yaml`, or beside the file without one.
a module's key hasheth its source text, its path, its imports' keys, and the
running compiler's path and modification time, so an edited module, any module
that reacheth it, and a rebuilt compiler all miss. an interface holdeth only the
module's own definitions, exports, and resolved checking references; loading
rebuildeth each environment from its imports' interfaces and the primitives,
sharing them. loading first
interneth identities across the decoded interfaces and primitives, before
rebuilding those environments. the binary format still storeth module and name;
pointer sharing is an optimisation, never the meaning of equality. a module whose
imports are missing or unparsed hath no key. an unreadable interface is
ignored, and a failed write leaveth the cache as it was. an older interface
without checking references is rejected. reference keys must belong to the
module, and every referenced symbol must exist in the rebuilt environment.
loading reuseth trusted checked output; it doth not repeat kernel validation.

one editor session reuseth compiled imports by their transitive interface
keys. editing an import invalidateth its dependants; unchanged imports remain
reusable. the session cacheth the last root result, including an import
failure, until the root text or imports change. each source snapshot shareth
its located parse between import discovery and compilation. filesystem
projects retain those snapshots beside their original text and owning paths.
highlighting needeth no compilation.

## checking and execution

inductive metadata storeth target-labelled recursive fields and checked core
computation rules. `Inductive` generateth and checketh the rules once;
`Normalise` and `Run` execute the same terms. nested specialisation is temporary:
only the restored public families, their constructors and recursors, and private
transparent target aliases enter the environment. interfaces preserve this
metadata and the aliases, while source exports contain only declared names.

`Source.Declaration` lowereth data to inductive families and flocks to one-constructor
dictionary families. members are accessor functions. a bizen's named members
lower to ordinary local bindings and dictionary constructor applications.
instance search resolveth requirements before kernel checking.
pattern matches become dependent eliminator applications. structural recursion
and course-of-values recursion use the same checked elimination rules.
[`dependent.md`](dependent.md) owneth these semantics and rejection cases.

`Elaboration` collecteth resolved references before inference or evaluation can
erase them. `Source.Elaborate` returneth them with each checked result, and
`Source.Declaration` attacheth them to the inserted symbols in `SourceProgram`.
`Source.Module` and `Source.Cache` preserve this graph across imports.
`Source.Proof.auditProof` traverseth it beside checked types and bodies;
`verifyProof` applieth the orsetting policy and, when strict, refuseth `sorry`.
`Main` rendereth one report for both `--name` and the editor; the editor's
`proof` command is always strict. proof auditing addeth no kernel typing or conversion rule.

`Source.recoverSnapshotHoles` provideth diagnostic goals after a checking error.
`Parse.recoverSnapshot` retaineth complete declarations at unindented heads
outside balanced delimiters. unfinished delimiters, strings, and comments
may limit recovery. only fully checked imports provide names.

`Elaboration.recover` retaineth inference state so encountered holes can show
their goals and named contexts after failure. speculative attempts still
restore their state on failure. `Source.Declaration.recoverDeclarations`
returneth goals separately from its checked result. failed declaration groups
and their dependants never enter the private recovery environment; independent
root goals may still use primitives and checked imports. the cli and editor
show these goals beside the original diagnostic. proof auditing, type queries,
and execution retain strict compilation.

`Source.Instance` solveth dictionary goals from core types and class registries;
it hath no source-syntax or declaration-checking dependency.
`Source.Declaration` lowereth the named syntax to ordinary dictionary terms.
`Source.Pattern` lowereth matching and recursion through the expression callbacks
in its `ExpressionChecker`. the algorithms and rejection rules belong to
[dependent.md](dependent.md#pattern-matching-and-recursion).

`Syntax` owneth pure core decomposition, application construction, local
shifting, and universe traversal and substitution. `mapChildren` owneth each
constructor's binder increments. `traverseScoped` shareth preorder traversal
with a lazy default descent. replacement nodes are not revisited; callers retain
their local-index and error rules. checking, induction, normalisation, and
source elaboration use these same operations. universe
constraint solving remaineth in `Universe`; semantic neutral spines remain
in `Normalise` and serve inference too.

`Source.Scope` owneth local transitions and the active induction contexts.
`Source.Syntax.freeNames` serveth declaration scheduling and recursion detection.
`Elaboration.trial` snapshotteth holes, universes, and resolved references;
failed trials restore all three. no lower layer importeth the source facade.

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
that replaceth a library source invalidateth that cache. the runner forceth each
outcome before starting the next test, so successful checks do not retain
deferred work. successful evaluation cases
assert exact results. rejected cases exercise the compiler before execution.
`Test.Program` compareth generated checked programs against independent host
results; dependent groups cover kernel and source rules directly.
`TUNG_TEST_GROUP` rejecteth every unknown name and an empty explicit selection.
fixture source replacements invalidate compiled dependencies in both shared
test helpers. executable tests compare predictable byspel output and exit
status exactly; `word_rime` receiveth a real file.

## neatening and editor protocol

`Tung.Format` is the canonical two-space neatener for the cli and editor. it
parseth the source first and refuseth source that doth not parse, reporting
the parse error and changing nothing. its output followeth only the tokens,
their brackets, and the comments between them, so two sources with one
concrete syntax tree have one neat form: whitespace never changeth it, and
neatening is idempotent. a final check refuseth any output whose tokens differ
from the source's.

- a comment on the line of the token before it trails that token; any other
  comment leadeth the next token and standeth at its item's indentation. these
  two attachments are the only layout the neatener readeth from the source.
- one blank line parteth top-level declarations; consecutive `bring`s stay
  together, sorted by path; no other blank line surviveth.
- each bracket either fitteth on its line or breaketh. a broken brace or
  parenthesis putteth each item on its own line, two columns in, and closeth on
  its own line; a broken square bracket filleth its slots and wrappeth between
  them. a broken block is indented from the line it beginneth on and closeth
  at that line's indentation, even when that line continueth a wrapped head.
  a declaration body of more than one item, a body holding declarations,
  and a case block of more than one row always break. a declaration body and a
  `match` body are padded, as `{ … }`; other braces are not.
- an item beginneth after a `,` or `;`, or at a declaration keyword. a `,`
  between a row's patterns before its `^`, or between `match` scrutinees, doth
  not end an item.
- a `let` or `orsetting` that fitteth stayeth on one line. otherwise its
  `≔ body` taketh a line of its own, two columns in, and its `: annotation`
  stayeth beside its name unless the two do not fit together, when it too
  taketh a line two columns in. a body that openeth a brace, a block of
  declarations, or a `match` openeth it on the `≔` line, and the binding need
  fit only up to that opening.
- a row's `^`, and a `≔` outside a declaration, keep their left side on the
  line and break before the right side, two columns in, unless the right side
  openeth a block. other terms fill their line and continue two columns in; a
  `match` head and a brace opening a block stay on the line before them.
- consecutive case rows of one indentation and column count align their
  columns and `^` when the aligned rows still fit 80 characters.
- no line passeth 80 characters while a break remaineth: quoted text is never
  broken, and a wide `#` or `##` comment wrappeth at its last fitting space.

the layout is a wadler–leijen document: groups lie flat when their content to
the next possible break fitteth, a comment endeth its line without breaking
its group, and consecutive line breaks merge. range neatening is not offered,
since a canonical form doth not keep the source's lines.

`tung --editor-session` provideth diagnostics, inferred ilks, highlighting,
and neatening through utf-8 json lines. each line is one complete message;
embedded newlines and control characters are json escapes.
the compiler and extension must use the same protocol version.

- requests contain `protocol: 1`, `id`, document `version`, `command`, `name`,
  `source`, and `imports`. imports map use paths to source text, including
  unsaved buffers. the client allocateth unique increasing request ids. a
  request for a file document also carrieth its `path`.
- the session keepeth checked imports by interface key, so a change to one
  import rechecketh only its dependants. a request with `path` also loadeth
  and saveth interfaces in that project's `.tung/cache`, shared with
  command-line runs.
- responses contain `protocol: 1`, the request `id` and `version`, and `result`.
  the result's `kind` is `check`, `ilk`, `proof`, `format`, `highlight`, or `error`.
- `check` returneth `diagnostics`; `ilk` returneth `ilk`; `format` returneth
  `source`; `highlight` returneth `roles`; infrastructure errors return `message`.
- `proof` taketh `name` and optional `allowedOrsettings`; an absent policy useth
  the nearest project manifest. it returneth `audit` (`name`, `ilk`, and
  `dependencies`), `verified`, `message`, and the shared cli `report`.
  each dependency hath a nominal `symbol` (`module`, `name`), display `name`,
  `ilk`, and `kind` (`sorry`, `orsetting`, or `host`); host entries also contain
  their catalogue key in `host`. checking errors return `error`; a completed
  audit that faileth its policy still returneth its dependencies and
  `verified: false`. clients never reconstruct dependency graphs from source.
  the language server discardeth a proof result if the root version or text,
  or any captured import text, changeth during the request.
- diagnostics contain `kind` (`parse`, `ilk`, or `goal`), optional import
  `path`, utf-16 `start` and `end`, and `message`. an empty array is success.
  goals are informational diagnostics, with their named context in the message.
  a failed check may return the original error beside recoverable root goals.
- `cancel` useth the target request id. late replies to cancelled requests are
  ignored. cancellation cannot interrupt a response line halfway through.
- malformed requests terminate the session. malformed replies, unsupported
  protocol versions, and mismatched live replies settle all pending client
  requests as errors and terminate the session. the next request starteth a
  fresh session.
- diagnostic locations come from source failures. an unlocated infrastructure
  failure useth the start of its owning file; no client parseth error prose to
  reconstruct a location.

`Source.Elaborate.elaborateHoles` rendereth successful goals after instance
selection. diagnostic recovery also rendereth encountered goals after failure;
`sourceHoles` returneth goals from a checked module.
`tung --language-metadata` emiteth
compiler-owned lexical names for editor clients. [`vscode/`](../vscode/) owneth
the language server, generated metadata, and editor tests.

the parser emiteth source roles alongside its result. highlighting retaineth
partial roles on failure and retryeth bounded declarations. it doth not check
types or load imports. `WorkspaceIndex` owneth one pending or resolved role
request per document text and version. navigation and highlighting share that
request; edits cancel it, and obsolete replies cannot repopulate the cache.
textmate supplieth immediate lexical colours. `vscode/server/analysis.ts`
joineth compiler roles with token structure, scopes, docs, and imports; the
workspace fetcheth missing roles before navigation. the editor doth not
classify tokens itself. one builder createth definitions from those roles;
pattern arms supply narrower scopes rather than a second set of definitions.
after building both components, `npm run benchmark:highlight --workspace=tung-vscode`
measureth fresh and cached highlighting on library files and incomplete buffers.

## library resolver

`Tung.Library` parseth the nearest `tung.yaml` and recursively resolveth local
paths and pinned git libraries. it cacheth git checkouts under
`.tung/libraries/`; matching pins share one checkout. local paths point to live
directories. a git pin may select one `subdir` of a repository. the
[language reference](language.md#libraries-and-imports)
defineth manifest syntax and observable conflict rules.

the flat `bring` namespace cannot distinguish two revisions of one library. raw
commit hashes have no useful version order. the resolver cannot choose a newer
pin or silently override an exact requirement. one library name must also
resolve to the same local path throughout the graph.

the compiler buildeth independently of bookhoard. ci and local development
resolve its source from `bookhoard/` through the same manifest.

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
