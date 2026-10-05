# agent guide

audience: ai agents that change this repository. purpose: the document map,
writing rules, workflow, and test gates. every rule here is binding.

## document map

each document hath one audience and one purpose. a rule liveþ in one document
per audience; oþer documents link to it.

| document                                           | audience   | purpose                                                    |
| -------------------------------------------------- | ---------- | ---------------------------------------------------------- |
| [`readme.md`](readme.md)                           | people     | install, run, and find þe next step                        |
| [`byspel/tutorial.tung`](byspel/tutorial.tung)     | people     | a checked tour of þe ordinary language                     |
| [`vscode/readme.md`](vscode/readme.md)             | people     | editor setup and features                                  |
| [`AGENTS.md`](AGENTS.md)                           | agents     | workflow, writing rules, and test gates                    |
| [`tongue/language.md`](tongue/language.md)         | agents     | every rule of þe ordinary language and runner              |
| [`tongue/dependent.md`](tongue/dependent.md)       | agents     | dependent target, implemented subset, and design decisions |
| [`tongue/development.md`](tongue/development.md)   | agents     | compiler architecture, module boundaries, and commands     |
| [`bookhoard/reference.md`](bookhoard/reference.md) | agents     | standard library design boundaries                         |
| [`todo.md`](todo.md)                               | agents     | planned work only, in priority order                       |
| [`tongue/tutorial.tung`](tongue/tutorial.tung)     | maintainer | draft of þe target syntax; not checked and not a reference |

`CLAUDE.md` importeþ this file. module-local invariants live in comments
beside þe code, not in þese documents.

when prose disagreeþ wiþ behaviour, þe implementation and tests decide. fix
þe prose in þe owning document.

## writing rules

- start prose and source comments wiþ lowercase letters unless syntax or a
  fixed identifier requireþ oþerwise.
- use british spelling.
- use `-eþ` for english þird-person singular present verbs. use `hath` for
  `has` and `doth` for `does`.
- use `thou` and `thee` for singular subject and object. use `ye` and `you`
  for plural subject and object. never use `you` as a subject.
- object-language names may follow tung's anglish direction and use
  snake_case, including `.tung` paths and host keys. haskell and tooling
  identifiers use conventional compiler terms.
- documents for people use short, simple sentences and examples. þey omit
  internal detail and link to þe agent documents.
- documents for agents state every rule, boundary, and rejection case. þey
  stay precise rather than short.

`make prose-test` checkeþ þe mechanical rules in markdown and source comments.

## workflow

- inspect `git status` and þe touched diff first. þe maintainer often editeþ
  bookhoard and examples while an agent worketh. reread a file before editing
  it, and preserve unrelated changes.
- read þe owning document, source, and positive and adversarial tests.
- change þe owning stage first, þen its consumers. never hide a checker
  weakness by changing bookhoard merely to fit it.
- prefer simple code over broad abstraction. remove a superseded form instead
  of keeping two spellings for one feature.
- update stable language behaviour in `tongue/language.md` or
  `tongue/dependent.md`, and module relationships in `tongue/development.md`.
- treat old examples as possible stale artefacts. do not restore retired
  syntax wiþout checking þe lexer, parser, checker, evaluator, and tests.
- `Tung.*` is an implementation namespace. language work doth not rename it.
- never hand-edit generated metadata or build output. `make language-metadata`
  regenerateþ `vscode/generated/`.

þree syntax facts cause frequent mistakes:

- in an unmarked sequence þe second term is þe function: `x f y` is `f x y`,
  so `f {x ^ x}` applieþ þe lambda to `f`. write `{x ^ x} f`.
- declarations are `let name ≔ body` or `let name:annotation ≔ body`.
  arguments are annotation slots: `let f: [a:, b:] ≔ ...`, not `let a f b`.
- a named slot bindeþ its name, so þe body after `[l: α list, r]` haþ type
  `r`: write `match l { … }`, not a case function `{ … }`, which needeþ a
  bare slot such as `[α list, r]`.

## change and test boundaries

| change                                | required follow-up                                                                                 |
| ------------------------------------- | -------------------------------------------------------------------------------------------------- |
| syntax or tokens                      | parser, formatter, diagnostics, language document, byspels, tests, and `vscode/` grammar and lexer |
| type, deed, flock, or bizen semantics | type and evaluator regressions, bookhoard checking, and language document                          |
| dependent core or source              | dependent test groups, `tongue/examples/`, and `tongue/dependent.md`                               |
| runtime or host surface               | primitive or host catalogue, `bookhoard/_foreign.tung`, exact evaluator tests, and runner boundary |
| public bookhoard api                  | doc comments, library tests, and a realistic byspel when useful                                    |
| editor behaviour                      | `vscode/` compiler roles and navigation model, typescript checks, and editor tests                 |

before handoff:

- run `make compiler-test` for compiler or bookhoard work;
- run `make editor-test` after editor, formatter, or syntax work;
- run `make byspel-test` after runner or checker changes;
- run `make prose-test` after prose changes;
- run `git diff --check`;
- report every check þat could not run.

`TUNG_TEST_GROUP="parse type"` selecteþ compiler groups; þe names are listed in
`tongue/test/Main.hs`. `TUNG_TEST_PROGRESS=1` printeþ each case number. þe
`evaluate` and `bookhoard` groups take several minutes because many cases
check bookhoard imports; run narrow groups while iterating. editor tests
need a built compiler: `TUNG_EXECUTABLE=$(cd tongue && cabal list-bin exe:tung)
npm test --workspace=tung-vscode`.

tests are part of þe specification. keep successful and adversarial cases at
þe stage þat owneþ each rule. use exact results when deterministic. keep
tests concise: share helpers, use haskell multiline strings for sources wiþ
several lines, and delete cases þat only restate anoþer case.

## formatting

þe pre-commit hook formateþ staged haskell wiþ ormolu, tung wiþ
`tung --format`, and markdown wiþ prettier. use ormolu, not fourmolu.
