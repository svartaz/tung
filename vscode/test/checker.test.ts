import assert from "node:assert/strict";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import { pathToFileURL } from "node:url";
import test, { type TestContext } from "node:test";
import { compiler } from "./compiler.ts";
import { CompilerBridge, sessionRequest } from "../server/checker.ts";
test("checker requests preserve unicode, quotes, slashes, and control characters", () => {
  const source = '𝟙\n"\\\t\r\u0000';
  const request = sessionRequest(7, 4, "check", "", source, [
    ["/project/dep.tung", source],
  ]);
  assert.equal(request.split("\n").length, 2);
  assert.deepEqual(JSON.parse(request), {
    protocol: 1,
    id: 7,
    version: 4,
    command: "check",
    name: "",
    source,
    texts: { "/project/dep.tung": source },
  });
});
test("a file request nameth its path", () => {
  const request = sessionRequest(8, 1, "check", "", "", [], "/project/a.tung");
  assert.equal(JSON.parse(request).path, "/project/a.tung");
});
test("proof requests distinguish inherited and empty orsetting policies", () => {
  const inherited = JSON.parse(sessionRequest(9, 2, "proof", "proved", "", []));
  const restricted = JSON.parse(
    sessionRequest(10, 2, "proof", "proved", "", [], undefined, []),
  );
  assert.equal(inherited.allowedOrsettings, undefined);
  assert.deepEqual(restricted.allowedOrsettings, []);
});
test("proof checking reporteth the selected closure and its policy verdict", async () => {
  const model = {
    text: "ilk =:[@α:*, x:α, α,*] { eftbend:x = @α x }\nilk one:* { only:one }\nlet proved:only = only ≔ eftbend\nlet unfinished:one ≔ sorry\norsetting assumed:only = only\nlet dependent:only = only ≔ assumed",
  };
  const proved = await compiler.proof(model, [], "proved", 0, []).result;
  assert.equal(proved.kind, "proof");
  if (proved.kind !== "proof") return;
  assert.equal(proved.verified, true);
  assert.deepEqual(proved.audit, {
    name: "proved",
    ilk: "only = only",
    dependencies: [],
  });
  assert.equal(
    proved.report,
    "name: proved\nilk: only = only\ndependencies: none\nname ok\n",
  );
  for (const [allowed, verified] of [
    [[], false],
    [["assumed"], true],
  ] as const) {
    const result = await compiler.proof(model, [], "dependent", 0, [...allowed])
      .result;
    assert.equal(result.kind, "proof");
    if (result.kind !== "proof") continue;
    assert.equal(result.verified, verified);
    assert.deepEqual(result.audit.dependencies, [
      {
        symbol: { module: "<root>", name: "assumed" },
        name: "assumed",
        ilk: "only = only",
        kind: "orsetting",
      },
    ]);
    assert.match(result.report, /orsetting: assumed: only = only/);
  }
  const unfinished = await compiler.proof(model, [], "unfinished").result;
  assert.equal(unfinished.kind, "proof");
  if (unfinished.kind === "proof") {
    assert.equal(unfinished.verified, false);
    assert.match(unfinished.message, /unfinished proof: sorry/);
    assert.equal(
      unfinished.audit.dependencies.some(({ kind }) => kind === "sorry"),
      true,
    );
  }
});
test("a successful check carrieth each sorry goal with its span and context", async () => {
  const source = "# 𝟙\nlet twice:[x:ℤ, ℤ] ≔ sorry\nlet worth:ℤ ≔ +1";
  const output = await compiler.check({ text: source }, []).result;
  const start = source.indexOf("sorry");
  assert.deepEqual(output, {
    kind: "check",
    diagnostics: [
      { kind: "goal", start, end: start + 5, message: "goal: ℤ\n  x: ℤ" },
    ],
  });
});
test("checker findeth a built executable without cabal list-bin", (context) => {
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
test("checker useth a configured executable without a compiler checkout", (context) => {
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
test("checker reuseth one versioned session and cancellable requests", async (context) => {
  const bridge = new CompilerBridge();
  bridge.configure(undefined, [], process.env.TUNG_EXECUTABLE);
  context.after(() => bridge.dispose());
  assert(bridge.findExecutable(), "install tung or set TUNG_EXECUTABLE");
  const model = { text: "let worth:ℤ ≔ +1" };
  const checked = bridge.check(model, [], 3);
  const typed = bridge.ilkOf(model, [], "worth", 3);
  const formatted = bridge.format("show ilk box: [a:*, *] { box: a box }\n", 3);
  assert.equal(checked.process, typed.process);
  assert.equal(checked.process, formatted.process);
  assert.equal(checked.version, 3);
  assert.deepEqual(await checked.result, { kind: "check", diagnostics: [] });
  assert.deepEqual(await typed.result, { kind: "ilk", ilk: "ℤ" });
  assert.equal(
    await formatted.result,
    "show ilk box: [a: *, *] { box: a box }\n",
  );
  const cancelled = bridge.check(model, [], 4);
  cancelled.cancel();
  assert.deepEqual(await cancelled.result, {
    kind: "error",
    message: "checker request cancelled",
  });
  assert.deepEqual(await bridge.check(model, [], 5).result, {
    kind: "check",
    diagnostics: [],
  });
});

// a document beside a saved dep.tung, whose unsaved text a request supplieth.
const besideDep = (context: TestContext) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-unsaved-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  fs.writeFileSync(path.join(root, "dep.tung"), "show let saved ≔ +0");
  const uri = pathToFileURL(path.join(root, "main.tung")).href;
  return {
    model: (text: string) => ({ uri, text }),
    dep: (text: string): [string, string][] => [
      [path.join(root, "dep.tung"), text],
    ],
  };
};
test("source and unsaved import changes invalidate the compiled cache", async (context) => {
  const { model, dep } = besideDep(context);
  const imported = "bring dep.tung\nlet worth ≔ exported";
  for (const [source, annotation, value, expected] of [
    [imported, "ℤ", "+1", "ℤ"],
    [imported, "string", "'new'", "string"],
    ["bring dep.tung\nlet worth ≔ +2", "string", "'new'", "ℤ"],
  ]) {
    const texts = dep(`show let exported:${annotation} ≔ ${value}`);
    assert.deepEqual(
      await compiler.ilkOf(model(source), texts, "worth").result,
      {
        kind: "ilk",
        ilk: expected,
      },
    );
  }
});

test("a corrected import cleareth a cached failure", async (context) => {
  const { model, dep } = besideDep(context);
  const source = "bring dep.tung\nlet worth ≔ exported";
  const broken = dep("show let exported ≔ missing");
  const first = await compiler.check(model(source), broken).result;
  assert(first.kind === "check");
  assert.equal(first.diagnostics.length, 1);
  assert.equal(first.diagnostics[0].path, "dep.tung");
  assert.match(first.diagnostics[0].message, /unknown name 'missing'/);
  assert.deepEqual(await compiler.check(model(source), broken).result, first);
  const corrected = dep("show let exported:ℤ ≔ +3");
  assert.deepEqual(
    await compiler.ilkOf(model(source), corrected, "worth").result,
    { kind: "ilk", ilk: "ℤ" },
  );
  const edited = await compiler.check(
    model("bring dep.tung\nlet worth ≔ missing"),
    corrected,
  ).result;
  assert(edited.kind === "check");
  assert.equal(edited.diagnostics[0].path, undefined);
  assert.match(edited.diagnostics[0].message, /unknown name 'missing'/);
});

// actual subprocesses exercise stream decoding and session teardown together.
const fixtureBridge = (context: TestContext, body: string) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-protocol-"));
  const executable = path.join(root, "tung");
  fs.writeFileSync(
    executable,
    `#!${process.execPath}
const readline = require("node:readline");
const requests = [];
const reply = (request, result = {kind:"check", diagnostics:[]}) =>
  process.stdout.write(JSON.stringify({protocol:1, id:request.id, version:request.version, result}) + "\\n");
readline.createInterface({input:process.stdin}).on("line", line => {
  const request = JSON.parse(line);
  if (request.command === "cancel") return;
  ${body}
});
`,
    { mode: 0o755 },
  );
  const bridge = new CompilerBridge();
  bridge.configure(undefined, [], executable);
  context.after(() => {
    bridge.dispose();
    fs.rmSync(root, { recursive: true, force: true });
  });
  return bridge;
};

test(
  "JSON responses survive fragmented unicode and multiline source",
  { timeout: 5000 },
  async (context) => {
    const bridge = fixtureBridge(
      context,
      `
    const bytes = Buffer.from(JSON.stringify({protocol:1, id:request.id, version:request.version,
      result:{kind:"format", source:request.source}}) + "\\n");
    let position = 0;
    const write = () => {
      if (position === bytes.length) return;
      process.stdout.write(bytes.subarray(position, ++position));
      setImmediate(write);
    };
    write();
  `,
    );
    const source = '𝟙\n"\\\t\r\u0000';
    assert.equal(await bridge.format(source, 4).result, source);
  },
);

test(
  "out-of-order responses retain their request and document versions",
  { timeout: 5000 },
  async (context) => {
    const bridge = fixtureBridge(
      context,
      `
    requests.push(request);
    if (requests.length === 2) {
      for (const request of requests.reverse()) reply(request, {kind:"ilk", ilk:request.name});
    }
  `,
    );
    const first = bridge.ilkOf({ text: "" }, [], "ℤ", 3);
    const second = bridge.ilkOf({ text: "" }, [], "string", 4);
    assert.deepEqual(await Promise.all([first.result, second.result]), [
      { kind: "ilk", ilk: "ℤ" },
      { kind: "ilk", ilk: "string" },
    ]);
  },
);

test(
  "invalid responses settle pending requests and restart the session",
  { timeout: 5000 },
  async (context) => {
    const corruptions = [
      "'not-json'",
      "JSON.stringify({})",
      "JSON.stringify({...response, protocol:2})",
      "JSON.stringify({...response, version:0})",
      'JSON.stringify({...response, result:{kind:"ilk", ilk:"ℤ"}})',
      'JSON.stringify({...response, result:{kind:"check", diagnostics:[{kind:"ilk", start:9, end:2, message:"bad"}]}})',
    ];
    for (const corrupted of corruptions) {
      const bridge = fixtureBridge(
        context,
        `
      if (request.version === 1) {
        const response = {protocol:1, id:request.id, version:request.version, result:{kind:"check", diagnostics:[]}};
        process.stdout.write(${corrupted} + "\\n");
      } else reply(request);
    `,
      );
      const first = bridge.check({ text: "" }, [], 1);
      const second = bridge.check({ text: "" }, [], 1);
      for (const result of await Promise.all([first.result, second.result])) {
        assert.equal(result.kind, "error", corrupted);
      }
      assert.equal(bridge.pending.size, 0);
      const restarted = bridge.check({ text: "" }, [], 2);
      assert.notEqual(restarted.process, first.process);
      assert.deepEqual(await restarted.result, {
        kind: "check",
        diagnostics: [],
      });
      bridge.dispose();
    }
  },
);
