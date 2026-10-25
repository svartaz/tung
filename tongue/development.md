# tung development guide

audience: agents. purpose: how the compiler and editor are built: commands,
repository layout, module boundaries, structural decisions, and test
machinery. [`language.md`](language.md) owneth what programs mean,
[`dependent.md`](dependent.md) the checker's algorithms, and
[`AGENTS.md`](../AGENTS.md) workflow and test gates.

## setup and commands

compiler development requireth ghc 9.12 or newer (ci useth 9.12.4); editor and
prose checks require node.js and npm. `tung.yaml` selecteth the local
[`library/`](../library/) for tests. from the repository root:

```sh
mise install
lefthook install
make setup
```

`make setup` runneth all tests and installeth the runner and, with the `code`
command, the VS Code extension. the root `package.json` declareth `vscode/` as
an npm workspace, and `make` coordinateth its scripts with the haskell build
and formula check.

| command                 | purpose                                                               |
| ----------------------- | --------------------------------------------------------------------- |
| `make build`            | buildeth the compiler and editor                                      |
| `make test`             | runneth compiler, byspel, prose, editor, and formula checks           |
| `make check`            | runneth `make test`, `make tidy-check`, and `git diff --check`        |
| `make tidy-check`       | checketh ormolu and canonical tung tidying without changing files     |
| `make compiler-test`    | testeth parsing, typing, evaluation, library modules, and integration |
| `make byspel-test`      | runneth the deterministic byspels and checketh their results          |
| `make editor-test`      | runneth the VS Code extension tests                                   |
| `make compiler-install` | installeth the runner in `~/.local/bin` by default                    |
| `make benchmark`        | runneth repeatable compiler and evaluator workloads                   |

the `tung-vscode` workspace hath `npm test` (`TUNG_EXECUTABLE` nameth another
compiler), `npm run update:metadata` and `npm run check:metadata` for the
generated language names, `npm run package`, `npm run install:extension`, and
`npm run setup`, which testeth and installeth. ci runneth the compiler, byspel,
editor, prose, and formula checks as separate jobs on pushes and pull
requests; the homebrew workflow also testeth formula installation.

## repository layout

| path         | purpose                                                          |
| ------------ | ---------------------------------------------------------------- |
| `tongue/`    | haskell compiler, evaluator, tidier, repl, runner, and tests     |
| `library/`   | standard library source and design guide                         |
| `vscode/`    | npm workspace for the VS Code extension                          |
| `Formula/`   | homebrew formula                                                 |
| `tung.yaml`  | local and git-pinned library dependencies                        |
| `byspel/`    | checked examples, including the walkthrough and checker fixtures |
| `benchmark/` | compiler and evaluator workloads                                 |

## compiler stages

```text
source text
  -> lossless pieces with utf-16 spans
  -> one expression parser for types and values, and the concrete tree
  -> project loading and import resolution
  -> bidirectional elaboration, pattern compilation, and instance search
  -> independent dependent-kernel checking
  -> normalisation for conversion, or erasure for runtime execution
```

- lexing needeth no parser state, and parsing no type information.
- elaboration may insert implicit arguments and solve typed contextual holes;
  the kernel rejecteth every term hole and validateth completed definitions.
- normalisation computeth type equality and never performeth an effect. runtime
  evaluation consumeth checked programs and never repaireth static errors.
- editor analysis may approximate incomplete source; compiler results stay
  authoritative.

| module                                 | responsibility                                                                                      |
| -------------------------------------- | --------------------------------------------------------------------------------------------------- |
| `Tung.Token`                           | lexical syntax, lossless pieces, and utf-16 source locations                                        |
| `Tung.Concrete`                        | the lossless concrete syntax tree from pieces and parser marks                                      |
| `Tung.Highlight`                       | roles, tokens, declarations, imports, and rows of one parse for editors                             |
| `Tung.Dependent.Source.Parse`          | declarations, expressions, source roles, node marks, and recovery                                   |
| `Tung.Dependent.Source.Syntax`         | one source expression syntax and lexical free-name analysis for types and values                    |
| `Tung.Dependent.Source.Environment`    | checked module state, checking references, name visibility, exports, and class registries           |
| `Tung.Dependent.Source.Proof`          | dependency closure, assumption auditing, and axiom policy checking                                  |
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
| `Tung.Dependent.Source.Declaration`    | lets, host bindings, types, classes, bizens, and law proofs                                         |
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
| `Tung.Dependent.Run`                   | erased evaluation and effect execution                                                              |
| `Tung.Primitive`                       | one host catalogue, nominal constructor identities, and pure operations                             |
| `Tung.Diagnostic`                      | source failures rendered for command-line and editor clients                                        |

`Tung` exposeth source services, diagnostics, metadata, and library and
project loading; `Tung.Dependent` the checked core. source compilation and
erased execution have separate facades, `Tung.Dependent.Source` and
`Tung.Dependent.Run`. commands and the editor use one compiler. module-local
invariants live beside the code.

## projects and imports

`Tung.Project` discovereth raw sources before checking, applying the
[module search rules](language.md#libraries-and-imports) to each `bring`. a
`Project` holdeth the root text, reachable imported text, and file paths for
diagnostics. each snapshot shareth its located parse between import discovery
and compilation, and filesystem projects keep snapshots beside their text and
owning paths. `loadEditorProject` readeth unsaved texts, keyed by canonical
path, before files, and leaveth out a missing or ambiguous bring, so checking
reporteth it at its span; the command line refuseth both.

`compileImports` compileth reached modules once into a map of `SourceProgram`
values; `compileSnapshot` reuseth it for a root module and returneth any
yielded expression. both take parsed snapshots and return structured failures;
test adapters live in `Test.Compile`. a program holdeth a checked kernel
environment and its visible and exported names; private definitions serve
checked terms without becoming visible. `SourceProgram` is abstract: its
environment, exports, and hole queries are functions, and its record labels
cannot be used for updates. `Inferred` stayeth a raw, editable claim, so
execution validateth it against the program's environment.

`Source.Environment` owneth top-level names, visibility, and class registries.
`Source.Module` parseth reached modules, assembleth imports, and scheduleth
declarations, calling `Source.Declaration` to check them; it inferreth no
types and selecteth no instances. dependencies are computed once per
declaration, source spans travel with declarations, and cached environments
merge only after shared definitions agree. strongly connected declarations are
grouped: all-type components are checked atomically, other cycles rejected, and
`Inductive` owneth the joint and nested certificates of
[inductive declarations](dependent.md#inductive-declarations-and-proofs).

`Identity.internSymbols` reuseth definition keys through a pure table of
identities. `Source.Environment` interneth a newly checked module's own bodies,
metadata, checking references, names, and registries, and recorded results
share those bodies; imported definitions are not walked again.

### interface cache

`Source.Cache` keepeth checked imports for command-line runs in `.tung/cache`
beside the nearest `tung.yaml`, or beside the file without one.

- a module's key hasheth its source text, path, imports' keys, and the running
  compiler's path and modification time, so an edited module, every module
  reaching it, and a rebuilt compiler all miss. a module whose imports are
  missing or unparsed hath no key.
- an interface holdeth only the module's own definitions, exports, and
  resolved checking references. loading interneth identities across decoded
  interfaces and primitives, then rebuildeth each environment from its
  imports' interfaces, sharing them. the format still storeth module and
  name: sharing is an optimisation, never the meaning of equality.
- an unreadable interface is ignored, and a failed write leaveth the cache
  unchanged. an interface without checking references is rejected; reference
  keys must belong to the module and every referenced symbol must exist in the
  rebuilt environment. loading trusteth checked output and doth not rerun the
  kernel.

an editor session reuseth compiled imports by transitive interface key: an
edited import invalidateth its dependants only. the session cacheth the last
root result, an import failure included, until the root text or imports
change, and each manifest's module roots until its text changeth, so a pinned
checkout is not verified per request. highlighting needeth no compilation.

## elaboration and checking

`Source.Declaration` lowereth types to inductive families and classes to
one-constructor dictionary families with accessor members; a bizen's members
become local bindings and a dictionary constructor application. instance
search resolveth requirements before kernel checking. matches become
dependent eliminator applications, and structural and course-of-values
recursion share the checked elimination rules. inductive metadata storeth
target-labelled recursive fields and checked computation rules, generated and
checked once by `Inductive` and executed by `Normalise` and `Run`. nested
specialisation is temporary: only restored public families, their
constructors and recursors, and private transparent target aliases enter the
environment. interfaces keep the metadata and aliases, while exports keep only
declared names.

- `Source.Instance` solveth goals from core types and class registries, with
  no dependency on source syntax or declaration checking.
- `Source.Pattern` lowereth matching and recursion through the callbacks in
  its `ExpressionChecker`; [dependent.md](dependent.md#pattern-matching-and-recursion)
  owneth the algorithms.
- `Source.Scope` owneth local transitions and active induction contexts.
  `Source.Syntax.freeNames` serveth scheduling and recursion detection.
- `Syntax` owneth pure core decomposition, application building, local
  shifting, and universe traversal and substitution. `mapChildren` owneth each
  constructor's binder increments; `traverseScoped` shareth preorder traversal
  with a lazy default descent and doth not revisit replacements, leaving
  local-index and error rules to callers. checking, induction, normalisation,
  and elaboration share these; constraint solving stayeth in `Universe` and
  semantic neutral spines in `Normalise`.
- `Elaboration.trial` snapshotteth holes, universes, and resolved references,
  and a failed trial restoreth all three. no lower layer importeth the source
  facade.
- `Source.Error` keepeth failure text apart from its optional span.
  elaboration keepeth the innermost failing expression's span, declaration and
  import context preserve it, and kernel and NBE errors gain locations only at
  the elaboration boundary. string APIs render failures at exit; diagnostic
  APIs keep kind, module path, span, and text.

### checking references and audits

`Elaboration` collecteth resolved references before inference or evaluation
can erase them. `Source.Elaborate` returneth them with each checked result,
`Source.Declaration` attacheth them to inserted symbols, and `Source.Module`
and `Source.Cache` preserve them across imports. `Source.Proof.auditProof`
traverseth them beside checked types and bodies; `verifyProof` applieth the
axiom policy and, when strict, refuseth `sorry`. `Main` rendereth one
report for `--name` and the editor, whose `proof` command is always strict.
auditing addeth no kernel typing or conversion rule.

### concrete tree and recovery

`Token.lexPieces` covereth the source with pieces: tokens, spaces, comments,
and unlexed runs, whose texts join to the source. a comment on the line of the
token before it traileth that token; any other leadeth the next. where no rule
accepteth a character, the rest of its line is one unlexed piece, or the rest
of the source for an unfinished block comment, and lexing resumeth; the strict
lexer and recovery read only the tokens before the first unlexed piece. the
parser's side channel carrieth roles and node marks: declarations, bracket
items, case rows, and members. `Concrete.concreteTree` pairth brackets
lexically and nesteth each mark that covereth whole siblings, so the tree's
text is the source's.

`Parse.recover` is the one walk for diagnostics, highlighting, and the tree:
it keepeth complete declarations at unindented heads outside balanced
delimiters, and a region between them is a broken node whose lines are parsed
one by one for roles and marks only. unfinished delimiters, strings, and
comments may limit it. `Elaboration.recover` keepeth inference state so encountered holes
show goals and contexts after failure, while speculative attempts still
restore theirs. `Source.Declaration.recoverDeclarations` returneth goals apart
from its checked result: failed groups and their dependants never enter the
private recovery environment, and only fully checked imports provide names.
`Source.recoverSnapshotHoles` provideth these goals after an error, and the
cli and editor show them beside the original diagnostic. proof auditing, type
queries, and execution keep strict compilation.
`Source.Elaborate.elaborateHoles` rendereth goals after instance selection,
and `sourceHoles` returneth a checked module's goals.

## runtime and host catalogue

normalisation keepeth universes and dependent terms for conversion. `Run`
eraseth types and implementeth the [evaluation rules](language.md#application)
with haskell thunks shared by delayed arguments, lets, globals, fields,
eliminator methods, and recursive hypotheses; a failure is an `RFailure` value
that faileth when inspected. `settled` computeth a value fully where the
language requireth it, and `execute` keepeth bind and `fast` unfoldings in
tail position. a fixpoint's global entry nameth itself through the lazy
table; a full application of it is a `DFast` effect, so its body unfoldeth only
when performed. effects reach the host only through `HostIO`: `ioHost` is the
process host and useth `Tung.Web` for servers, and tests use the simulated
host in `Test.DependentSupport`. `runYield` validateth its `Inferred`
judgement with the kernel before erasure; `runMain` and validation share one
checked-main lookup.

`Tung.Primitive` owneth every host key, signature, constructor identity, and
pure operation, and `Host` checketh each `foreign` binding against it.
normalisation and runtime share `pureOperation` over `HostValue`. a pure
binding paireth a native function with private typed codecs, so one entry
deriveth its signature and its erased applicator and GHC checketh native types;
nominal schemas are still validated when keys are bound. polymorphic effect
signatures stay separate. a host data type's identity is its library path
and name, with no shape matching or built-in bizen.

## test machinery

- a full run checketh the library once in the parent process and saveth its
  interfaces in `dist-newstyle/test-interfaces`; each group process beginneth
  from them, and a single selected group checketh what it needeth. their keys
  hash the compiler library's sources rather than the test executable, so a
  later run reuseth every interface whose module and library are unchanged,
  and removeth the rest. a module whose private names a test readeth is
  checked again from source.
- `Test.Harness` compileth further library imports once per process; a test
  replacing a library source invalidateth that cache and its compiled
  dependants in both shared helpers.
- the runner forceth each outcome before the next test, so checks keep no
  deferred work.
- successful evaluation cases assert exact results; rejected cases exercise
  the compiler before execution.
- `Test.Program` compareth generated checked programs with independent host
  results; dependent groups test kernel and source rules directly.
- `TUNG_TEST_GROUP` rejecteth unknown names and an empty explicit selection.
- executable tests compare byspel output and exit status exactly; `word_count`
  receiveth a real file. one check first fileth the interfaces of every
  library module the byspels bring, then the byspels run side by side, each
  within its own time limit.

## tidying

`Tung.Format` is the canonical two-space tidier for the cli and editor. it
parseth first and refuseth unparseable source, reporting the error and
changing nothing. it then shorteneth each redundant η-expansion, droppeth
redundant parentheses, and flatteneth nested products; layout
followeth only the tokens, their brackets, and the comments between them, so
sources with one concrete syntax tree share one tidy form: whitespace never
changeth it and tidying is idempotent. a final check refuseth output whose
tokens differ from the shortened source's.

- a lambda whose binders are its body's last arguments, in order, is
  η-expanded: `{a₁, …, aₙ ^ a₁ f a₂ … aₙ}` becometh `f`, and `{b ^ m tweak b}`
  becometh `(m tweak)`, parenthesised unless the lambda is a whole expression, as a let's body or a
  row's. its binders are distinct, bare, and not `_`; the rest is names
  and literals that never name a binder; no comment standeth inside; and the
  brace is not a `match`'s rows. a binder that is the first argument, as in
  `{b ^ b tweak m}`, is not shortened. conversion hath function η, so the two
  are one function, and a shortening may complete an outer one.
- redundant parentheses are dropped where the parse cannot change: around
  one atom (a name, literal, `*`, `sorry`, or bracketed group), unless `@(…)`
  writeth an implicit argument or a `:` or `.` followeth; and around a run of
  atoms that is a whole expression, as a let's body, a row's, or an item. a
  pair holding `:`, `$`, a keyword, a projection, or a comment is kept.
- a product whose last item is a product of bare slots is that product's
  rest: `[a: α, [β, γ]]` becometh `[a: α, β, γ]`, and `[[ℕ, *]]` becometh
  `[ℕ, *]`. an inner slot that is named or implicit keepeth the brackets: in a
  let's annotation it would bind its name in the body, and in a type's header
  a named slot may be a parameter where a nested one is an index. a product
  in any earlier position, as `[[ℤ, ℤ], ℤ]`, is a function input and is kept,
  as is one holding a comment. the three shortenings repeat until none
  applieth.
- an annotated or implicit binder keepeth its expansion, which may guide
  elaboration, as when `f`'s implicit inputs follow an explicit one; annotate
  a binder to keep an expansion.
- the tidier readeth no names, so a binder may be a constructor. a one-row
  match on a constructor checketh only when it is its type's sole, nullary one,
  where `f` agreeth with the match on every input.

- it walketh the concrete tree: declarations and a bracket's items are the
  nodes the parser marked, each with its separator; an unmarked inside is one
  item, and a row's `;` endeth each alternative.
- a blank line standeth between declarations, except between `bring`s, and
  between a class's or a bizen's members; a block's lets stand on consecutive
  lines. no other break leaveth an empty line.
- a comment keepeth the lexer's attachment, a leading one at its item's
  indentation; this is the only layout read from the source.
- one blank line parteth top-level declarations; consecutive `bring`s stay
  together, sorted by path; no other blank line surviveth.
- a bracket fitteth its line or breaketh. a broken brace or parenthesis putteth
  each item on its own line two columns in and closeth on its own line; a
  broken square bracket filleth its slots and wrappeth between them. a broken
  block is indented from the line it beginneth on and closeth at that line's
  indentation, even when that line continueth a wrapped head.
- a declaration body of several items or holding declarations, and a case
  block of several rows, always break. declaration and `match` bodies are
  padded, `{ … }`; other braces are not.
- a `let` or `axiom` that fitteth stayeth on one line. otherwise `≔ body`
  taketh its own line two columns in, and `: annotation` stayeth beside the
  name unless they do not fit together. a body opening a brace, a declaration
  block, or a `match` openeth it on the `≔` line, and the binding need fit only
  to that opening.
- a row's `^`, and a `≔` outside a declaration, keep the left side and break
  before the right two columns in, unless it openeth a block. other terms fill
  their line and continue two columns in; a `match` head and a block-opening
  brace stay on the line before.
- consecutive case rows of one indentation and column count align their
  columns and `^` when the result still fitteth. zero-width tags in the laid
  out lines mark a row's start, its column ends, and its `^` or `;`; a row
  whose patterns wrap is not aligned.
- no line passeth 80 characters while a break remaineth; quoted text never
  breaketh, and a wide `#` or `##` comment wrappeth at its last fitting space.

the layout is a wadler–leijen document: a group lieth flat when its content to
the next possible break fitteth, a comment endeth its line without breaking
its group, and consecutive line breaks merge. range tidying is not offered,
since a canonical form keepeth no source lines.

## editor protocol

`tung --editor-session` serveth diagnostics, inferred types, highlighting, and
tidying over utf-8 json lines, one complete message per line with embedded
newlines and control characters escaped. compiler and extension must share the
protocol version.

- requests carry `protocol: 1`, `id`, document `version`, `command`, `name`,
  `source`, and `texts`, which map open files' paths to their unsaved text; a
  file document also carrieth `path`. the session resolveth the document's
  brings by the command line's rules from `path`, or from its working
  directory, reading `texts` before files. the client allocateth unique
  increasing ids.
- the session keepeth checked imports by interface key, rechecking only an
  edited import's dependants; a request with `path` also loadeth and saveth
  interfaces in that project's `.tung/cache`.
- responses carry `protocol: 1`, the request's `id` and `version`, and a
  `result` whose `kind` is `check`, `type`, `proof`, `format`, `highlight`, or
  `error`: `check` returneth `diagnostics`, `type` `type`, `format` `source`,
  and infrastructure errors `message`.
- `highlight` returneth one parse's `roles`, `[start, end, role, modifiers]`;
  `tokens`, `[start, end, kind]`; `declarations`, each `let`, `fast`, `type`, `class`,
  `bizen`, or `axiom` with its keyword's `start`, `end`, `headerEnd` where
  the body beginneth, `shown`, and its last doc comment as `doc`; `imports`
  with `path`, `alias`, and the path's `start` and `end`; and `scopes`,
  `[start, end, scopeStart, scopeEnd]` for each local binder: a slot is seen
  by the later slots and the body, a declaration's header by the whole
  declaration, a block's let by the rest of its block, and a row's pattern by
  its row. offsets are utf-16 and cover broken regions too.
- `names` returneth `files`, the canonical file of each bring path the
  document reacheth; `resolved`, `[start, end, module, name, type]` for each
  written name checking resolved to a
  global, from every declaration that checketh, even beside an error; and
  `visible`, `[written, module, name, constructor]` for each name the module
  may write at top level, from its own declarations and its imports'
  interfaces, without checking. `module` is `<root>`, `<primitive>`, or a
  bring path. `type` is whether the global's type, after its inputs, is a
  sort. elaboration recordeth a name where it resolveth one, and speculative
  trials roll the record back.
- `proof` taketh `name` and optional `allowedAxioms`; without it the
  nearest manifest decideth. it returneth `audit` (`name`, `type`,
  `dependencies`), `verified`, `message`, and the cli `report`. a dependency
  hath a nominal `symbol` (`module`, `name`), display `name`, `type`, and
  `kind` (`sorry`, `axiom`, or `host`, with its catalogue key in `host`).
  checking errors return `error`; an audit failing its policy still returneth
  its dependencies with `verified: false`. clients never rebuild dependency
  graphs from source, and the language server discardeth a result if the root
  version or text, or the text of any module its names reached, changeth
  meanwhile.
- diagnostics carry `kind` (`parse`, `type`, or `goal`), optional import
  `path`, utf-16 `start` and `end`, and `message`; an empty array is success.
  goals are informational, with their context in the message, and a failed
  check may return its error beside recoverable root goals.
- locations come from source failures; an unlocated infrastructure failure
  useth the start of its file, and no client parseth error prose for one.
- `cancel` nameth the target id; late replies to cancelled requests are
  ignored, and a response line is never interrupted.
- a malformed request endeth the session. a malformed reply, unsupported
  version, or mismatched live reply settleth every pending request as an error
  and endeth it; the next request starteth a fresh session.

## editor client

[`vscode/`](../vscode/) owneth the language server, generated metadata, and
editor tests; `tung --language-metadata` emitteth the compiler-owned lexical
names. the editor neither lexeth nor parseth tung: highlighting returneth the
compiler's syntax, which neither checketh types nor loadeth imports.
`WorkspaceIndex` owneth one pending or resolved syntax request per document
text and version, shared by navigation, checks, and highlighting; edits cancel
it and obsolete replies cannot refill the cache, and every request awaiteth
the syntax it needeth. textmate supplieth immediate lexical colours.
`vscode/server/syntax.ts` placeth the compiler's tokens by line and pairth
brackets; `vscode/server/analysis.ts` joineth roles with those tokens,
declarations, docs, imports, and local scopes into definitions and
ownership; a local the parser could not scope, in broken source, keepeth to
its declaration. the editor resolveth no global itself: a written name is what
checking resolved it to, else a local binder in scope, else the module's
visible name; a pattern binder that nameth a visible constructor is that
constructor, and a field `type.field` is the named slot of its type's
constructor. navigation fetcheth names for open documents, and references
and rename for every document. a bring path's module is the file its
document's names report, matched to a document by real path; the editor
resolveth no bring itself. colouring taketh the parser's roles, except that a
checked name is a type exactly when its `type` saith so: a value written in an
annotation, as `zero` in `(zero · a) = zero`, is no type, which syntax
cannot tell. an edit forgetteth the names of documents that
reached the edited file, and a created or deleted file forgetteth all. lsp role names stay in the protocol;
`roleLabel` showeth them to people as tung terms.
`npm run benchmark:highlight --workspace=tung-vscode`, after both components
are built, measureth fresh and cached highlighting.

## library resolver

`Tung.Library` parseth the nearest `tung.yaml` and resolveth local paths and
pinned git libraries recursively, caching checkouts under `.tung/libraries/`;
matching pins share one checkout and local paths stay live. a pin may select
one `subdir`. [libraries and imports](language.md#libraries-and-imports)
defineth manifest syntax and conflict rules.

the flat `bring` namespace cannot tell two revisions of a library apart, and
raw hashes have no version order, so the resolver never chooseth a newer pin or
overrideth an exact one, and a library name resolveth to one local path
throughout the graph. the compiler buildeth without the library; ci and local
development resolve `library/` through the same manifest.

## structural decisions

each choice was weighed against an alternative.

- `Source` is a facade over the acyclic layers `Expression`, `Elaborate`, and
  `Declaration`. `Pattern` lowereth recursion over `Pattern.Common`,
  `Pattern.Index`, and `Pattern.Match`; `Common` holdeth shared binder and
  memo helpers, breaking the match–recursion cycle. `ExpressionChecker`
  carrieth the environment and names its callbacks were built from.
- `K.Environment` stayeth explicit in elaboration, because constructor
  recognition and instance-pattern comparison are pure and run outside it.
- the kernel's `Typing` monad keepeth explicit globals, because `Inductive`
  checketh constructors against two staged environments in one run.
- `splitColumn`, `Parse`, and `Elaboration` stay whole: `splitColumn`'s steps
  share the column, rows, scope, expected type, and recursion; the parser
  shareth one result monad and its roles; metas, unification, and pruning share
  one solver state.
- the parser's `Result` monad backtracketh by inspecting roles, so a
  transformer stack would not shrink it.
- the concrete tree is built from the parser's marks rather than by a second
  grammar: the tidier, highlighting, and the editor read the one parse, and
  the abstract syntax stayeth the parser's own result.
