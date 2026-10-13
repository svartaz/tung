# tung

tung is a lazily evaluating functional programming language equipped with predicative intensional martin-löf type system.

## a first program

```tung
use ground.tung

let double: [x:, ℤ] ≔ x + x

let main: 𝟙 deed ≔ +21 double $ to_string $ write_line
```

save it as `double.tung` and run `tung double.tung`. it printeth `42`.

- the second item of a call is the function: `+21 double` meaneth `double(+21)`.
- `$` endeth a call and passeth its value on.
- `let name: type ≔ worth` annotateth a declaration.
- `𝟙 deed` is an action, like haskell `IO`. the runner performeth `main`.

## install

```sh
brew tap svartaz/tung https://github.com/svartaz/tung.git
brew install svartaz/tung/tung
```

homebrew installeth the pinned release. for the current syntax and proof
checker, build from this checkout with ghc 9.12 or newer and cabal:

```sh
mise install
make compiler-install
```

the command is installed at `~/.local/bin/tung`. set `PREFIX` or `BIN_DIR` to
choose another place.

## run

| command                                  | purpose                                      |
| ---------------------------------------- | -------------------------------------------- |
| `tung forewrit.tung [arguments...]`      | runneth `main` with the remaining arguments  |
| `tung --check forewrit.tung`             | checketh a program with `main`               |
| `tung --check-module module.tung`        | checketh a file without `main`               |
| `tung --no-sorry --check-module m.tung`  | also faileth when a proof assumeth `sorry`   |
| `tung --type-of name forewrit.tung`      | printeth the inferred type of a name         |
| `tung --check-proof name module.tung`    | checketh one declaration and its assumptions |
| `tung --format file.tung [more.tung...]` | formateth files in place                     |

proof checking rejecteth reachable `sorry`. the
[proof checking guide](tongue/language.md#proof-checking) describeth axiom
allowlists and editor support. try it on a proof in the
[walkthrough](byspel/walkthrough.tung):

```sh
tung --no-axioms --check-proof naught_+ byspel/walkthrough.tung
```

## libraries

the standard library, bookhoard, liveth in [`bookhoard/`](bookhoard/). a
`tung.yaml` file nameth the libraries a project useth:

```yaml
dependencies:
  bookhoard:
    path: bookhoard
```

## next steps

- read and run the [walkthrough](byspel/walkthrough.tung): `tung byspel/walkthrough.tung`.
- try the other examples in [`byspel/`](byspel/).
- set up the [editor extension](vscode/readme.md).
- some keywords are anglish words:

  | tung    | meaning    | tung        | meaning          |
  | ------- | ---------- | ----------- | ---------------- |
  | `ilk`   | data type  | `fremmed`   | foreign binding  |
  | `flock` | type class | `orsetting` | axiom            |
  | `bizen` | instance   | `fallback`  | default instance |
  | `deed`  | io action  | `fall`      | function         |

  the [keyword table](tongue/language.md#nonstandard-keywords) listeth all
  of them.

- tung useth dependent types. the [design](tongue/dependent.md)
  explaineth its rules.

contributors and agents start at [`AGENTS.md`](AGENTS.md).

## licence

tung is free software under the GNU LGPL, version 3 or later.
[`COPYING.LESSER`](COPYING.LESSER) holdeth its terms, and
[`COPYING`](COPYING) the GNU GPL they build on.
