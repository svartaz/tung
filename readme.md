# tung

tung is a lazy functional language. this page helpeth thee install it, run a
program, and find the next step.

## a first program

```tung
use ground.tung

let double: [x:, ℤ] ≔ x + x

let main: 𝟙 deed ≔ +21 double $ to_text $ write_line
```

save it as `double.tung` and run `tung double.tung`. it printeth `42`.

- the second item of a call is the function: `+21 double` meaneth `double +21`.
- `$` endeth a call and passeth its value on.
- `let name: type ≔ worth` annotateth a declaration.
- `𝟙 deed` is an action, like haskell `IO`. the runner performeth `main`.

## install

```sh
brew tap jukisima/tung https://github.com/jukisima/tung.git
brew install jukisima/tung/tung
```

or build from this checkout with ghc 9.12 or newer and cabal:

```sh
brew bundle
make compiler-install
```

the command is installed at `~/.local/bin/tung`. set `PREFIX` or `BIN_DIR` to
choose another place.

## run

| command                                  | purpose                                     |
| ---------------------------------------- | ------------------------------------------- |
| `tung forewrit.tung [arguments...]`      | runneth `main` with the remaining arguments |
| `tung --check forewrit.tung`             | checketh a program with `main`              |
| `tung --check-module module.tung`        | checketh a file without `main`              |
| `tung --no-sorry --check-module m.tung`  | also faileth when a proof assumeth `sorry`  |
| `tung --type-of name forewrit.tung`      | printeth the inferred type of a name        |
| `tung --format file.tung [more.tung...]` | formateth files in place                    |

## libraries

the standard library, bookhoard, liveth in [`bookhoard/`](bookhoard/). a
`tung.yaml` file nameth the libraries a project useth:

```yaml
dependencies:
  bookhoard:
    path: bookhoard
```

## next steps

- read and run the [tutorial](byspel/tutorial.tung): `tung byspel/tutorial.tung`.
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
