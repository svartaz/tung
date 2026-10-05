import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import test from "node:test";
import { pathToFileURL } from "node:url";
import { WorkspaceIndex } from "../server/workspace.ts";
import { compiler } from "./compiler.ts";
test("requirements resolve imported types and declared parameters", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-requirement-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  fs.writeFileSync(path.join(root, "dep.tung"), "show ilk box: * { box: box }");
  const main = path.join(root, "main.tung");
  fs.writeFileSync(
    main,
    "use dep.tung flock child:[@:box same, a:*, @:a same, *] {let f:[a, a]}",
  );
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    compiler,
  );
  workspace.configure([root]);
  await workspace.ready();
  const model = workspace.model(pathToFileURL(main).href);
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
test("workspace resolveþ only shown names across an import", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-workspace-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const dep = path.join(root, "dep.tung");
  const main = path.join(root, "main.tung");
  fs.writeFileSync(dep, "show let answer:ℤ ≔ +42 let hidden ≔ +0");
  fs.writeFileSync(main, "use dep.tung let value:ℤ ≔ answer");
  const documents = { get: () => undefined, all: () => [] };
  const workspace = new WorkspaceIndex(documents, compiler);
  workspace.configure([root]);
  await workspace.ready();
  const model = workspace.model(pathToFileURL(main).href);
  assert.equal(workspace.resolveVisible(model, "answer").length, 1);
  assert.equal(workspace.resolveVisible(model, "hidden").length, 0);
  assert.equal(workspace.resolveVisible(model, "dep~answer").length, 1);
  assert.equal(
    workspace.importModel(model, "dep.tung")?.uri,
    pathToFileURL(dep).href,
  );
});
test("workspace explicit import alias replaceeþ the default namespace", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-use-alias-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const dep = path.join(root, "data", "dep.tung");
  const main = path.join(root, "main.tung");
  fs.mkdirSync(path.dirname(dep), { recursive: true });
  fs.writeFileSync(dep, "show let answer:ℤ ≔ +42");
  fs.writeFileSync(main, "use data/dep.tung d yield d~answer");
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    compiler,
  );
  workspace.configure([root]);
  await workspace.ready();
  const model = workspace.model(pathToFileURL(main).href);
  assert.equal(workspace.resolveVisible(model, "d~answer").length, 1);
  assert.equal(workspace.resolveVisible(model, "dep~answer").length, 0);
  const labels = new Set(
    workspace
      .completions(model.uri, { line: 0, character: 40 })
      .map(({ completionName, bareName }) => completionName || bareName),
  );
  assert(labels.has("d~answer"));
  assert(!labels.has("dep~answer"));
});
test("workspace resolveþ and completeþ a default basename alias", async (context) => {
  const root = fs.mkdtempSync(
    path.join(os.tmpdir(), "tung-default-use-alias-"),
  );
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const dep = path.join(root, "data", "dep.tung");
  const main = path.join(root, "main.tung");
  fs.mkdirSync(path.dirname(dep), { recursive: true });
  fs.writeFileSync(dep, "show let answer:ℤ ≔ +42");
  fs.writeFileSync(main, "use data/dep.tung yield dep~answer");
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    compiler,
  );
  workspace.configure([root]);
  await workspace.ready();
  const model = workspace.model(pathToFileURL(main).href);
  assert.equal(workspace.resolveVisible(model, "dep~answer").length, 1);
  assert.equal(workspace.resolveVisible(model, "ilk/dep~answer").length, 0);
  const labels = new Set(
    workspace
      .completions(model.uri, { line: 0, character: 40 })
      .map(({ completionName, bareName }) => completionName || bareName),
  );
  assert(labels.has("dep~answer"));
  assert(!labels.has("ilk/dep~answer"));
});
test("workspace default alias ignoreþ dots in import directories", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-dotted-use-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const dep = path.join(root, "pkg.one", "query.tung");
  const main = path.join(root, "main.tung");
  fs.mkdirSync(path.dirname(dep), { recursive: true });
  fs.writeFileSync(dep, "show let answer:ℤ ≔ +42");
  fs.writeFileSync(main, "use pkg.one/query.tung yield query~answer");
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    compiler,
  );
  workspace.configure([root]);
  await workspace.ready();
  const model = workspace.model(pathToFileURL(main).href);
  assert.equal(workspace.resolveVisible(model, "query~answer").length, 1);
  assert.equal(workspace.resolveVisible(model, "pkg~answer").length, 0);
});
test("workspace leaveþ duplicate imported bare names ambiguous", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-ambiguous-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  fs.writeFileSync(path.join(root, "left.tung"), "show let value ≔ +1");
  fs.writeFileSync(path.join(root, "right.tung"), "show let value ≔ +2");
  const main = path.join(root, "main.tung");
  fs.writeFileSync(main, "use left.tung use right.tung let answer ≔ value");
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    compiler,
  );
  workspace.configure([root]);
  await workspace.ready();
  const model = workspace.model(pathToFileURL(main).href);
  assert.equal(workspace.resolveVisible(model, "value").length, 2);
  assert.equal(workspace.resolveVisible(model, "left~value").length, 1);
});
test("workspace re-exports every same-spelled role", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-namespaces-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  fs.writeFileSync(
    path.join(root, "both.tung"),
    "let token:* ≔ ℤ let token ≔ +1 show token",
  );
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    compiler,
  );
  workspace.configure([root]);
  await workspace.ready();
  const shown = workspace.publicDefinitions(
    workspace.model(pathToFileURL(path.join(root, "both.tung")).href),
  );
  assert.deepEqual(shown.map(({ role }) => role).sort(), ["type", "variable"]);
});
test("library modules do not become an implicit prelude", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-ground-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const library = path.join(root, "library");
  fs.mkdirSync(library);
  fs.writeFileSync(
    path.join(library, "ground.tung"),
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
  fs.writeFileSync(path.join(library, "_foreign.tung"), "show let value ≔ +1");
  const main = path.join(root, "main.tung");
  fs.writeFileSync(main, "use foreign.tung");
  const workspace = new WorkspaceIndex(
    { get: () => undefined, all: () => [] },
    compiler,
  );
  workspace.configure([root], [library]);
  await workspace.ready();
  const model = workspace.model(pathToFileURL(main).href);
  assert(workspace.modulePaths(model.uri).includes("_foreign.tung"));
  assert(!workspace.modulePaths(model.uri).includes("foreign.tung"));
  assert.equal(workspace.resolveImport(model, model.imports[0]), undefined);
});
test("library roots resolve exact paths and duplicate names stay ambiguous", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-library-roots-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const project = path.join(root, "project");
  const first = path.join(root, "first");
  const second = path.join(root, "second");
  for (const directory of [project, first, second]) fs.mkdirSync(directory);
  const main = path.join(project, "main.tung");
  const module = path.join(first, "extra.tung");
  fs.writeFileSync(main, "use extra.tung yield extra~value");
  fs.writeFileSync(module, "show let value ≔ +1");
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
  fs.writeFileSync(path.join(second, "extra.tung"), "show let value ≔ +2");
  workspace.invalidateFiles();
  assert.equal(workspace.resolveImport(model, model.imports[0]), undefined);
  fs.writeFileSync(path.join(project, "extra.tung"), "show let value ≔ +3");
  workspace.invalidateFiles();
  assert.equal(
    workspace.resolveImport(model, model.imports[0])?.uri,
    pathToFileURL(path.join(project, "extra.tung")).href,
  );
});
