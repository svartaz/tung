# tung

tung is a functional programming with

- infix notation,
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

| command                                | purpose                                        |
| -------------------------------------- | ---------------------------------------------- |
| `tung file.tung [arguments...]`        | runneth `main` with the arguments              |
| `tung --check file.tung`               | checketh a module, or a program and its `main` |
| `tung --check --no-sorry file.tung`    | also faileth when a proof assumeth `sorry`     |
| `tung --name name file.tung`           | printeth a name's type and its assumptions     |
| `tung --tidy file.tung [more.tung...]` | tidieth files in place                         |

`--no-sorry` before any command turneth reachable `sorry` into failure. to
check a proof, add `--no-sorry` and, to refuse axioms, `--no-axiom`. the
[proof checking guide](tongue/language.md#proof-checking) describeth axiom
allowlists and editor support. try it on a proof in the
[walkthrough](byspel/walkthrough.tung):

```sh
tung --no-sorry --no-axiom --name zero_+ byspel/walkthrough.tung
```

## libraries

the standard library liveth in [`library/`](library/). a
`tung.yaml` file nameth the libraries a project useth:

```yaml
dependencies:
  library:
    path: library
```

## next steps

- read and run the [walkthrough](byspel/walkthrough.tung): `tung byspel/walkthrough.tung`.
- set up the [editor extension](vscode/readme.md).
- a few keywords differ from other languages:

  | tung      | meaning      | tung       | meaning             |
  | --------- | ------------ | ---------- | ------------------- |
  | `bring`   | import       | `bizen`    | instance            |
  | `show`    | export       | `fallback` | default instance    |
  | `yield`   | local result | `fast`     | self-calling effect |
  | `unbuild` | eliminator   | `foreign`  | host binding        |

  the [keyword table](tongue/language.md#keywords) listeth all
  of them.

- tung useth dependent types. the [design](tongue/dependent.md)
  explaineth its rules.

contributors and agents start at [`AGENTS.md`](AGENTS.md).

## licence

tung is free software under the GNU LGPL, version 3 or later.
[`COPYING.LESSER`](COPYING.LESSER) holdeth its terms, and
[`COPYING`](COPYING) the GNU GPL they build on.
