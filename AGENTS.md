# agent guide

audience: ai agents that change this repository. purpose: the document map,
writing rules, workflow, and test gates. every rule here is binding.

## document map

each document hath one audience and one purpose. a rule liveth in one document
per audience; other documents link to it.

| document                                           | audience | purpose                                                 |
| -------------------------------------------------- | -------- | ------------------------------------------------------- |
| [`readme.md`](readme.md)                           | people   | install, run, and find the next step                    |
| [`byspel/tutorial.tung`](byspel/tutorial.tung)     | people   | a checked tour of the ordinary language                 |
| [`vscode/readme.md`](vscode/readme.md)             | people   | editor setup and features                               |
| [`AGENTS.md`](AGENTS.md)                           | agents   | workflow, writing rules, and test gates                 |
| [`anglish.md`](anglish.md)                         | agents   | anglish words and the english words they replace        |
| [`tongue/language.md`](tongue/language.md)         | agents   | what a program author writeth and observeth             |
| [`tongue/dependent.md`](tongue/dependent.md)       | agents   | checker algorithms, logic, and design decisions         |
| [`tongue/development.md`](tongue/development.md)   | agents   | commands, modules, structural decisions, test machinery |
| [`bookhoard/reference.md`](bookhoard/reference.md) | agents   | standard library design boundaries                      |
| [`todo.md`](todo.md)                               | agents   | planned work only, in priority order                    |

`CLAUDE.md` importeth this file. module-local invariants live in comments
beside the code, not in these documents.

when prose disagreeth with behaviour, the implementation and tests decide. fix
the prose in the owning document.

## writing rules

- start prose and source comments with lowercase letters unless syntax or a
  fixed identifier requireth otherwise.
- use british spelling.
- write `th`, never the letter thorn, in prose, comments, and names.
- use `-eth` for english third-person singular present verbs. use `hath` for
  `has` and `doth` for `does`.
- use `thou` and `thee` for singular subject and object, and `-st` for a verb
  with `thou`: `thou hast`, `thou dost`, `thou checkest`. use `ye` and `you`
  for plural subject and object. never use `you` as a subject.
- use `e`, `em`, and `es` for third-person singular personal pronouns:
  subject, object, and possessive respectively.
- object-language names follow tung's anglish direction and use snake_case,
  including `.tung` paths and host keys. [`anglish.md`](anglish.md) listeth
  the anglish words and the english words they replace. haskell and tooling
  identifiers use conventional compiler terms.
- a name putteth a namespace-like part first, then the concept it owneth,
  then qualifiers: `≤_eftbend` is `≤`'s `eftbend`, `deed_bind` is
  `deed`'s `bind`, and a helper proof is `helpsetting_≍_=`. a name that
  spelleth an expression keepeth the expression's term order, as
  `sheer_bind` or `naught_+`, and a conversion stayeth `x_to_y`.
- a compound declared name keepeth each term's own spelling, including symbols:
  `≍_to_=`, `≍_eftbend`, and `≤_=`. ordinary word-named terms such as
  `sameness` keep their spelling too, as in `warp_sameness`.
- a name doth not repeat its module's file name: a shown name is read
  qualified, so `x.tung` showeth `to_y`, read `x~to_y`, not `x_to_y`. the
  same name may be used in different files.
- documents for people use short, simple sentences and examples. they omit
  internal detail and link to the agent documents.
- documents for agents state every rule, boundary, and rejection case. they
  stay precise rather than short.

`make prose-test` checketh the mechanical rules in markdown and source comments.

## workflow

- inspect `git status` and the touched diff first. the maintainer often editeth
  bookhoard and examples while an agent worketh. reread a file before editing
  it, and preserve unrelated changes.
- read the owning document, source, and positive and adversarial tests.
- change the owning stage first, then its consumers. never hide a checker
  weakness by changing bookhoard merely to fit it.
- prefer simple code over broad abstraction. remove a superseded form instead
  of keeping two spellings for one feature.
- update stable language behaviour in `tongue/language.md` or
  `tongue/dependent.md`, and module relationships in `tongue/development.md`.
- treat old examples as possible stale artefacts. do not restore retired
  syntax without checking the lexer, parser, checker, evaluator, and tests.
- `Tung.*` is an implementation namespace. language work doth not rename it.
- never hand-edit generated metadata or build output. `make language-metadata`
  regenerateth `vscode/generated/`.

three syntax facts cause frequent mistakes:

- in an unmarked sequence the second term is the function: `x f y` is `f x y`,
  so `f {x ^ x}` applieth the lambda to `f`. write `{x ^ x} f`.
- declarations are `let name ≔ body` or `let name:annotation ≔ body`.
  arguments are annotation slots: `let f: [a:, b:] ≔ ...`, not `let a f b`.
- a named slot bindeth its name, so the body after `[l: α list, r]` hath type
  `r`: write `match l { … }`, not a case function `{ … }`, which needeth a
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
- report every check that could not run.

`make check` runneth every check above.

`TUNG_TEST_GROUP="parse type"` selecteth compiler groups; the names are listed in
`tongue/test/Main.hs`. `TUNG_TEST_PROGRESS=1` printeth each case number. the
`evaluate` and `bookhoard` groups take several minutes because many cases
check bookhoard imports; run narrow groups while iterating. editor tests
need a built compiler: `TUNG_EXECUTABLE=$(cd tongue && cabal list-bin exe:tung)
npm test --workspace=tung-vscode`.

tests are part of the specification. keep successful and adversarial cases at
the stage that owneth each rule. use exact results when deterministic. keep
tests concise: share helpers, use haskell multiline strings for sources with
several lines, and delete cases that only restate another case.

## formatting

the pre-commit hook formateth staged haskell with ormolu, tung with
`tung --format`, and markdown with prettier. use ormolu, not fourmolu.
