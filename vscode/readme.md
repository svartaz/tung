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
- compiler-backed diagnostics and inferred types in hover;
- the goal and named context of each `sorry`, as information and in hover;
- completion, signature help, and doc comments in hover;
- declaration, definition, type-definition, implementation, and reference
  navigation;
- document and workspace symbols, highlights, and checked rename;
- document links for `use`, formatting, and supported quick fixes; and
- a `Run Tung File` command and editor play button.

completion and navigation follow local and declared-library imports. unsaved
imported files are checked with their current contents. navigation and
highlighting work while a file is incomplete. compiler results remain
authoritative for diagnostics, inferred types, and formatting.

to run a file, open a saved `.tung` file and select the editor's play button.
ye can also run `Tung: Run Tung File` from the command palette. the command
saveth the file and useth a dedicated terminal.

the [development guide](https://github.com/jukisima/tung/blob/main/tongue/development.md)
covereth building and testing the extension.
