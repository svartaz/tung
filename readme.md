# tung

tung is a functional programming with

- infix notation,
- anglish keywords,
- lazy evaluation,
- inductive type family
- inductive types, and
- predicative intensional dependent types.

## install

```sh
brew tap svartaz/tung https://github.com/svartaz/tung.git
brew install svartaz/tung/tung
```

it installeth the command at `~/.local/bin/tung`.
set `PREFIX` or `BIN_DIR` to choose another place.

## run

| command                                  | purpose                                        |
| ---------------------------------------- | ---------------------------------------------- |
| `tung file.tung [arguments...]`          | runneth `main` with the arguments              |
| `tung --check file.tung`                 | checketh a module, or a program and its `main` |
| `tung --check --no-sorry file.tung`      | also faileth when a proof assumeth `sorry`     |
| `tung --name name file.tung`             | printeth a name's ilk and its assumptions      |
| `tung --neaten file.tung [more.tung...]` | neateneth files in place                       |

`--no-sorry` before any command turneth reachable `sorry` into failure. to
check a proof, add `--no-sorry` and, to refuse orsettings, `--no-orset`. the
[proof checking guide](tongue/language.md#proof-checking) describeth orsetting
allowlists and editor support. try it on a proof in the
[walkthrough](byspel/walkthrough.tung):

```sh
tung --no-sorry --no-orset --name naught_+ byspel/walkthrough.tung
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
- set up the [editor extension](vscode/readme.md).
- some keywords are anglish words:

  | tung    | meaning    | tung        | meaning          |
  | ------- | ---------- | ----------- | ---------------- |
  | `ilk`   | data type  | `fremmed`   | foreign binding  |
  | `flock` | type class | `orsetting` | axiom            |
  | `bizen` | instance   | `fallback`  | default instance |
  | `deed`  | io action  | `fall`      | function         |
  | `fast`  | io loop    |             |                  |

  the [keyword table](tongue/language.md#keywords) listeth all
  of them.

- tung useth dependent types. the [design](tongue/dependent.md)
  explaineth its rules.

contributors and agents start at [`AGENTS.md`](AGENTS.md).

## licence

tung is free software under the GNU LGPL, version 3 or later.
[`COPYING.LESSER`](COPYING.LESSER) holdeth its terms, and
[`COPYING`](COPYING) the GNU GPL they build on.
