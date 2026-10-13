import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import test, { type TestContext } from "node:test";
import { pathToFileURL } from "node:url";
import { WorkspaceIndex } from "../server/workspace.ts";
import { compiler } from "./compiler.ts";

const fixture = async (context: TestContext, files: Record<string, string>) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-workspace-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  for (const [name, source] of Object.entries(files)) {
    const file = path.join(root, name);
    fs.mkdirSync(path.dirname(file), { recursive: true });
    fs.writeFileSync(file, source);
  }
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    compiler,
  );
  workspace.configure([root]);
  await workspace.ready();
  const model = (name = "main.tung") =>
    workspace.model(pathToFileURL(path.join(root, name)).href);
  return { root, workspace, model };
};
test("changing an import retaineth unchanged role snapshots", async () => {
  const requests = [];
  let imported = "show let old ≔ +1";
  const documents = [
    { uri: "main", version: 1, getText: () => "bring dep.tung" },
    { uri: "dep", version: 1, getText: () => imported },
  ];
  const workspace = new WorkspaceIndex(
    {
      get: (uri) => documents.find((document) => document.uri === uri),
      all: () => documents,
    },
    {
      highlight: (source, version) => {
        requests.push([source, version]);
        return { result: Promise.resolve([]), cancel() {} };
      },
    },
  );
  await Promise.all([
    workspace.ready(),
    workspace.ready(),
    workspace.roles("main", documents[0].getText(), 1),
  ]);
  assert.equal(requests.length, 2);
  imported = "show let new ≔ +2";
  documents[1].version++;
  workspace.invalidate("dep");
  workspace.invalidateFiles();
  await workspace.ready();
  assert.deepEqual(requests, [
    ["bring dep.tung", 1],
    ["show let old ≔ +1", 1],
    [imported, 2],
  ]);
});
test("requirements resolve imported types and declared parameters", async (context) => {
  const {
    root,
    workspace,
    model: getModel,
  } = await fixture(context, {
    "dep.tung": "show ilk box: * { box: box }",
    "main.tung":
      "bring dep.tung flock child:[@:box hath_≍, a:*, @:a hath_≍, *] {let f:[a, a]}",
  });
  const model = getModel();
  const box = model.tokens.find((token) => token.text === "box");
  const resolved = workspace.resolveAt(model.uri, {
    line: box.line,
    character: box.char,
  }).definition;
  assert.equal(resolved?.role, "type");
  assert.equal(resolved?.uri, pathToFileURL(path.join(root, "dep.tung")).href);
  const uses = model.tokens.filter((token) => token.text === "a");
  const binder = workspace.resolveAt(model.uri, {
    line: uses.at(-1).line,
    character: uses.at(-1).char,
  }).definition;
  assert.equal(binder?.token.offset, uses[0].offset);
});
test("imports expose shown names under explicit and basename aliases", async (context) => {
  const cases = [
    ["default.tung", "data/dep.tung", "", "dep", "ilk/dep"],
    ["explicit.tung", "data/dep.tung", "d", "d", "dep"],
    ["dotted.tung", "pkg.one/query.tung", "", "query", "pkg"],
  ];
  const { root, workspace, model } = await fixture(context, {
    "data/dep.tung": "show let answer:ℤ ≔ +42 let hidden ≔ +0",
    "pkg.one/query.tung": "show let answer:ℤ ≔ +42 let hidden ≔ +0",
    ...Object.fromEntries(
      cases.map(([file, imported, alias, namespace]) => [
        file,
        `use ${imported}${alias ? ` ${alias}` : ""} yield ${namespace}~answer`,
      ]),
    ),
  });
  for (const [file, imported, , namespace, wrong] of cases) {
    const current = model(file);
    for (const [name, count] of [
      ["answer", 1],
      ["hidden", 0],
      [`${namespace}~answer`, 1],
      [`${wrong}~answer`, 0],
    ] as const) {
      assert.equal(workspace.resolveVisible(current, name).length, count, file);
    }
    assert.equal(
      workspace.importModel(current, imported)?.uri,
      pathToFileURL(path.join(root, imported)).href,
    );
    const labels = new Set(
      workspace
        .completions(current.uri, {
          line: 0,
          character: current.text.length,
        })
        .map(({ completionName, bareName }) => completionName || bareName),
    );
    assert(labels.has(`${namespace}~answer`), file);
    assert(!labels.has(`${wrong}~answer`), file);
  }
});
test("workspace leaveth duplicate imported bare names ambiguous", async (context) => {
  const { workspace, model } = await fixture(context, {
    "left.tung": "show let worth ≔ +1",
    "right.tung": "show let worth ≔ +2",
    "main.tung": "bring left.tung bring right.tung let answer ≔ worth",
  });
  assert.equal(workspace.resolveVisible(model(), "worth").length, 2);
  assert.equal(workspace.resolveVisible(model(), "left~worth").length, 1);
});
test("workspace re-exports every same-spelled role", async (context) => {
  const { workspace, model } = await fixture(context, {
    "both.tung": "let token:* ≔ ℤ let token ≔ +1 show token",
  });
  const shown = workspace.publicDefinitions(model("both.tung"));
  assert.deepEqual(shown.map(({ role }) => role).sort(), ["type", "variable"]);
});
test("library modules do not become an implicit prelude", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-often-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const library = path.join(root, "library");
  fs.mkdirSync(library);
  fs.writeFileSync(
    path.join(library, "often.tung"),
    "show let offered ≔ +1 let hidden ≔ +2",
  );
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    compiler,
  );
  workspace.configure([], [library]);
  await workspace.ready();
  const completions = workspace.primitiveCompletions();
  const labels = new Set(
    completions.map(
      ({ completionName, bareName }) => completionName || bareName,
    ),
  );
  assert(!labels.has("offered"));
  assert(!labels.has("hidden"));
  assert(labels.has("ℤ"));
});
test("library module paths keep their exact file names", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-module-paths-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const library = path.join(root, "library");
  fs.mkdirSync(library, { recursive: true });
  fs.writeFileSync(path.join(library, "_fremmed.tung"), "show let worth ≔ +1");
  const main = path.join(root, "main.tung");
  fs.writeFileSync(main, "bring foreign.tung");
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    compiler,
  );
  workspace.configure([root], [library]);
  await workspace.ready();
  const model = workspace.model(pathToFileURL(main).href);
  assert(workspace.modulePaths(model.uri).includes("_fremmed.tung"));
  assert(!workspace.modulePaths(model.uri).includes("foreign.tung"));
  assert.equal(workspace.resolveImport(model, model.imports[0]), undefined);
});
test("library roots resolve exact paths and duplicate names stay ambiguous", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-library-roots-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const project = path.join(root, "forthcast");
  const first = path.join(root, "first");
  const second = path.join(root, "second");
  for (const directory of [project, first, second]) fs.mkdirSync(directory);
  const main = path.join(project, "main.tung");
  const module = path.join(first, "extra.tung");
  fs.writeFileSync(main, "bring extra.tung yield extra~worth");
  fs.writeFileSync(module, "show let worth ≔ +1");
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    compiler,
  );
  workspace.configure([project], [first, second]);
  await workspace.ready();
  const model = workspace.model(pathToFileURL(main).href);
  assert.equal(
    workspace.resolveImport(model, model.imports[0])?.uri,
    pathToFileURL(module).href,
  );
  assert(workspace.modulePaths(model.uri).includes("extra.tung"));
  fs.writeFileSync(path.join(second, "extra.tung"), "show let worth ≔ +2");
  workspace.invalidateFiles();
  assert.equal(workspace.resolveImport(model, model.imports[0]), undefined);
  fs.writeFileSync(path.join(project, "extra.tung"), "show let worth ≔ +3");
  workspace.invalidateFiles();
  assert.equal(
    workspace.resolveImport(model, model.imports[0])?.uri,
    pathToFileURL(path.join(project, "extra.tung")).href,
  );
});
