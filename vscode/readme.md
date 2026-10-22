# tung language support

this page helpeth thee set up and use the VS Code extension for `.tung` files.
the extension liveth beside the compiler in `../tongue`.

## setup

from the repository root, build and install the extension with the `code`
command available:

```sh
npm ci
make compiler-build
npm run setup --workspace tung-vscode
```

## configuration

the extension useth `tung.executablePath` when set. otherwise, it seeketh a
built compiler in `tung.tonguePath` or the repository's `tongue` folder,
then `tung` on `PATH`. `tung.tonguePath` accepteth either the repository root
or its `tongue` folder.

the extension useth the workspace's `tung.yaml` for pinned libraries.
`tung.libraryPaths` addeth absolute local module roots. `TUNG_PATH` addeth
further roots. checking and running use the same roots.

## features

the extension provideth:

- syntax and semantic highlighting, folding, and selection ranges;
- compiler-backed diagnostics and inferred ilks in hover;
- the goal and named context of each `sorry`, as information and in hover;
- `Tung: Check Proof`, with the selected declaration's assumptions and project
  orsetting policy;
- completion, signature help, and doc comments in hover;
- declaration, definition, type-definition, implementation, and reference
  navigation;
- document and workspace symbols, highlights, and checked rename;
- document links for `bring`, whole-document tidying, and supported quick
  fixes; and
- a `Run Tung File` command and editor play button.

completion and navigation follow local and declared-library imports. unsaved
imported files are checked with their current contents. navigation and
highlighting work while a file is incomplete. compiler results remain
authoritative for diagnostics, inferred ilks, and tidying.
recoverable `sorry` goals and named contexts appear beside checking errors.
failed declarations and their dependants remain unavailable; broken imports
provide no partial names. unfinished delimiters or strings may limit recovery
(see "equality and holes" in `tongue/language.md`). proof checking,
type queries, and execution still require strict checking.

to check a proof, place the cursor in its top-level `let`, or select its name,
then run `Tung: Check Proof`. the `Tung Proof` output showeth the compiler's
report. unsaved changes are included. "proof checking" in
`tongue/language.md` explaineth assumptions
and the optional `tung.yaml` orsetting policy.

to run a file, open a saved `.tung` file and select the editor's play button.
ye can also run `Tung: Run Tung File` from the command palette. the command
saveth the file and useth a dedicated terminal.

the [development guide](https://github.com/svartaz/tung/blob/main/tongue/development.md)
covereth building and testing the extension.
