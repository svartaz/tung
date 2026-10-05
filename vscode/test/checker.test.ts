import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import test from "node:test";
import { compiler } from "./compiler.ts";
import {
  CompilerBridge,
  haskellString,
  parseCompilerDiagnostic,
  parseCompilerGoals,
  sessionRequest,
  sourceBundle,
} from "../server/checker.ts";
test("checker bundle preserveþ unicode, quotes, slashes, and control characters", () => {
  assert.equal(haskellString('𝟙\n"\\\t'), '"𝟙\\n\\"\\\\\\t"');
  assert.equal(
    sourceBundle("main", [["dep.tung", "source"]]),
    '("main",[("dep.tung","source")])',
  );
  assert.equal(
    sessionRequest(7, 4, "check", "", "main", [["dep.tung", "source"]]),
    '(7,4,"check","",("main",[("dep.tung","source")]))\n',
  );
});
test("checker protocol carrieþ an exact source range", () => {
  assert.deepEqual(
    parseCompilerDiagnostic(
      "tung-diagnostic\ttype\tdep.tung\t4\t9\ntype error: in 'value'",
    ),
    {
      kind: "type",
      path: "dep.tung",
      start: 4,
      end: 9,
      message: "type error: in 'value'",
    },
  );
  assert.equal(parseCompilerDiagnostic("tung-ok\n"), undefined);
});
test("a successful check carrieþ each sorry goal wiþ its span and context", async () => {
  const source = "let twice:[x:ℤ, ℤ] ≔ sorry\nlet value:ℤ ≔ +1";
  const output = await compiler.check({ text: source }, []).result;
  assert.equal(parseCompilerDiagnostic(output), undefined);
  const start = source.indexOf("sorry");
  assert.deepEqual(parseCompilerGoals(output), [
    { start, end: start + 5, message: "goal: ℤ\n  x: ℤ" },
  ]);
  assert.deepEqual(
    parseCompilerGoals("tung-diagnostic\ttype\t\t0\t1\nbad"),
    [],
  );
});
test("checker findeþ a built executable without cabal list-bin", (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-checker-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const executable = path.join(
    root,
    "dist-newstyle",
    "build",
    "arch",
    "ghc",
    "pkg",
    "x",
    "tung",
    "build",
    "tung",
    "tung",
  );
  fs.mkdirSync(path.dirname(executable), { recursive: true });
  fs.writeFileSync(executable, "");
  const bridge = new CompilerBridge();
  bridge.configure(root);
  bridge.findCabalExecutable = () => undefined;
  assert.equal(bridge.findExecutable(), executable);
});
test("checker useþ a configured executable without a compiler checkout", (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-checker-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const executable = path.join(root, "tung");
  fs.writeFileSync(executable, "");
  const bridge = new CompilerBridge();
  bridge.configure(undefined, [], executable);
  assert.equal(bridge.findExecutable(), executable);
  bridge.configure(undefined, [], path.join(root, "missing"));
  assert.equal(bridge.findExecutable(), undefined);
});
test("checker reuseþ one versioned session and cancellable requests", async (context) => {
  const bridge = new CompilerBridge();
  bridge.configure(undefined, [], process.env.TUNG_EXECUTABLE);
  context.after(() => bridge.dispose());
  assert(bridge.findExecutable(), "install tung or set TUNG_EXECUTABLE");
  const model = { text: "let value:ℤ ≔ +1" };
  const checked = bridge.check(model, [], 3);
  const typed = bridge.typeOf(model, [], "value", 3);
  const formatted = bridge.format("show ilk box: [a:*, *] { box: a box }\n", 3);
  assert.equal(checked.process, typed.process);
  assert.equal(checked.process, formatted.process);
  assert.equal(checked.version, 3);
  assert.equal((await checked.result).trim(), "tung-ok");
  assert.equal((await typed.result).trim(), "type: ℤ");
  assert.equal(
    await formatted.result,
    "show ilk box: [a: *, *] { box: a box }\n",
  );
  const cancelled = bridge.check(model, [], 4);
  cancelled.cancel();
  assert.equal(await cancelled.result, "checker request cancelled");
  assert.equal((await bridge.check(model, [], 5).result).trim(), "tung-ok");
});
