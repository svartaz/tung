# tung

tung is a lazy functional language. this page helpeþ thee install it, run a
program, and find the next step.

## a first program

```tung
use ground.tung

let double: [x:, ℤ] ≔ x + x

let main: 𝟙 deed ≔ +21 double $ to_text $ write_line
```

save it as `double.tung` and run `tung double.tung`. it printeþ `42`.

- the second item of a call is the function: `+21 double` meaneþ `double +21`.
- `$` endeþ a call and passeþ its value on.
- `let name: type ≔ value` annotateþ a declaration.
- `𝟙 deed` is an action, like haskell `IO`. the runner performeþ `main`.

## install

```sh
brew tap jukisima/tung https://github.com/jukisima/tung.git
brew install jukisima/tung/tung
```

or build from this checkout wiþ ghc 9.12 or newer and cabal:

```sh
brew bundle
make compiler-install
```

the command is installed at `~/.local/bin/tung`. set `PREFIX` or `BIN_DIR` to
choose anoþer place.

## run

| command                                  | purpose                                   |
| ---------------------------------------- | ----------------------------------------- |
| `tung program.tung [arguments...]`       | runneþ `main` wiþ the remaining arguments |
| `tung --check program.tung`              | checkeþ a program wiþ `main`              |
| `tung --check-module module.tung`        | checkeþ a file wiþout `main`              |
| `tung --no-sorry --check-module m.tung`  | also faileþ when a proof assumeþ `sorry`  |
| `tung --type-of name program.tung`       | printeþ the inferred type of a name       |
| `tung --format file.tung [more.tung...]` | formateþ files in place                   |

## libraries

the standard library, bookhoard, liveþ in [`bookhoard/`](bookhoard/). a
`tung.yaml` file nameþ the libraries a project useþ:

```yaml
dependencies:
  bookhoard:
    path: bookhoard
```

## next steps

- read and run the [tutorial](byspel/tutorial.tung): `tung byspel/tutorial.tung`.
- try the oþer examples in [`byspel/`](byspel/).
- set up the [editor extension](vscode/readme.md).
- some keywords are anglish words:

  | tung    | meaning    | tung       | meaning          |
  | ------- | ---------- | ---------- | ---------------- |
  | `ilk`   | data type  | `fremmed`  | foreign binding  |
  | `flock` | type class | `orsend`   | axiom            |
  | `bizen` | instance   | `fallback` | default instance |
  | `deed`  | io action  | `fall`     | function         |

  the [keyword table](tongue/language.md#nonstandard-keywords) listeþ all
  of them.

- tung useþ dependent types. the [design](tongue/dependent.md)
  explaineþ its rules.

contributors and agents start at [`AGENTS.md`](AGENTS.md).
