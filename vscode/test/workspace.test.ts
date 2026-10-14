import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import test, { type TestContext } from "node:test";
import { pathToFileURL } from "node:url";
import { CompilerBridge, emptySyntax } from "../server/checker.ts";
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
  await workspace.ready(true);
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
        return { result: Promise.resolve(emptySyntax), cancel() {} };
      },
    },
  );
  await Promise.all([
    workspace.ready(),
    workspace.ready(),
    workspace.syntax("main", documents[0].getText(), 1),
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
    "dep.tung": "show ilk box: * { boxed: box }",
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
        `bring ${imported}${alias ? ` ${alias}` : ""} yield ${namespace}~answer`,
      ]),
    ),
  });
  for (const [file, imported, , namespace, wrong] of cases) {
    const current = model(file);
    const { visible } = workspace.namesOf(current.uri);
    for (const [name, count] of [
      ["answer", 1],
      ["hidden", 0],
      [`${namespace}~answer`, 1],
      [`${wrong}~answer`, 0],
    ] as const) {
      assert.equal(
        visible.filter(([written]) => written === name).length,
        count,
        `${file} ${name}`,
      );
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
test("importers bring an open document's unsaved text, and an edit refresheth them", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-unsaved-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  fs.writeFileSync(path.join(root, "dep.tung"), "show let saved ≔ +1");
  fs.writeFileSync(path.join(root, "main.tung"), "bring dep.tung");
  let text = "show let unsaved ≔ +2";
  const dep = {
    uri: pathToFileURL(path.join(root, "dep.tung")).href,
    version: 1,
    getText: () => text,
  };
  const workspace = new WorkspaceIndex(
    { get: (uri) => (uri === dep.uri ? dep : undefined), all: () => [dep] },
    compiler,
  );
  workspace.configure([root]);
  const main = pathToFileURL(path.join(root, "main.tung")).href;
  const written = async () => {
    await workspace.ready(true);
    return workspace.namesOf(main).visible.map(([name]) => name);
  };
  const first = await written();
  assert(first.includes("unsaved"));
  assert(!first.includes("saved"));
  text = "show let edited ≔ +3";
  dep.version++;
  workspace.invalidate(dep.uri);
  assert((await written()).includes("edited"));
});
test("an ambiguous bare import resolveth to nothing; its qualified names do", async (context) => {
  const { root, workspace, model } = await fixture(context, {
    "left.tung": "show let worth ≔ +1",
    "right.tung": "show let worth ≔ +2",
    "main.tung": "bring left.tung bring right.tung let answer ≔ left~worth",
  });
  const { visible } = workspace.namesOf(model().uri);
  assert(!visible.some(([written]) => written === "worth"));
  const qualified = model().tokens.find(({ text }) => text === "left~worth");
  const resolved = workspace.resolveAt(model().uri, {
    line: qualified.line,
    character: qualified.char,
  }).definition;
  assert.equal(resolved?.uri, pathToFileURL(path.join(root, "left.tung")).href);
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
  assert.equal(workspace.importModel(model, "foreign.tung"), undefined);
});
test("the compiler resolveth brings: exact library paths, ambiguous duplicates, and local files first", async (context) => {
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
  const rooted = new CompilerBridge();
  rooted.configure(compiler.tongue, [first, second], compiler.executablePath);
  context.after(() => rooted.dispose());
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    rooted,
  );
  workspace.configure([project], [first, second]);
  const target = async () => {
    workspace.invalidateFiles();
    await workspace.ready(true);
    const model = workspace.model(pathToFileURL(main).href);
    return workspace.importModel(model, "extra.tung")?.uri;
  };
  assert.equal(await target(), pathToFileURL(module).href);
  const model = workspace.model(pathToFileURL(main).href);
  assert(workspace.modulePaths(model.uri).includes("extra.tung"));
  fs.writeFileSync(path.join(second, "extra.tung"), "show let worth ≔ +2");
  assert.equal(await target(), undefined);
  fs.writeFileSync(path.join(project, "extra.tung"), "show let worth ≔ +3");
  assert.equal(
    await target(),
    pathToFileURL(path.join(project, "extra.tung")).href,
  );
});
test("a field resolveth to its constructor's slot", async (context) => {
  const { root, workspace, model } = await fixture(context, {
    "dep.tung":
      "show ilk pair: * { pair_of: [left: ℕ, right: ℕ, pair] }\nlet sum: [p: pair, ℕ] ≔ p.right",
    "main.tung": "bring dep.tung\nlet first: [p: pair, ℕ] ≔ p.left",
  });
  const read = model().tokens.find(({ text }) => text === "left");
  const field = workspace.resolveAt(model().uri, {
    line: read.line,
    character: read.char,
  }).definition;
  const dependency = pathToFileURL(path.join(root, "dep.tung")).href;
  assert.equal(field?.uri, dependency);
  assert.equal(field?.bareName, "left");
  assert.deepEqual(
    workspace.references(field, false).map(({ uri }) => uri),
    [model().uri],
  );
});
