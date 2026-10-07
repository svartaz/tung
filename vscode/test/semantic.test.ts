import assert from "node:assert/strict";
import * as path from "node:path";
import test from "node:test";
import { CompilerBridge, SourceRole } from "../server/checker.ts";
import { buildHighlightRanges, HighlightCache } from "../server/highlight.ts";
import { WorkspaceIndex } from "../server/workspace.ts";

const compiler = new CompilerBridge();
compiler.configure(
  path.resolve(__dirname, "../../../tongue"),
  [],
  process.env.TUNG_EXECUTABLE,
);
test.after(() => compiler.dispose());
const labels = async (source: string, name: string) => {
  const uri = "file:///highlight_test.tung";
  const document = { uri, getText: () => source };
  const workspace = new WorkspaceIndex(
    {
      get: () => document,
      all: () => [document],
    },
    compiler,
  );
  await workspace.ready();
  const model = workspace.model(uri);
  const roles = await compiler.highlight(source).result;
  assert(roles, "the compiler must support the highlight request");
  const ranges = buildHighlightRanges(
    source,
    roles,
    (token) =>
      workspace.resolveAt(uri, { line: token.line, character: token.char })
        .definition,
  );
  return model.tokens
    .filter((token) => token.text === name)
    .map((token) => {
      const range = ranges.find(
        (range) => range.line === token.line && range.char === token.char,
      );
      return range && `${range.type}:${range.modifiers.join(".")}`;
    });
};
test("compiler roles keep types, header binders and application positions consistent", async () => {
  const source = "show let constant:[@a:*, @b:*, x:a, _:b, a] ≔ x\n" +
    "show let read:[text path:_path, (text ∑ text) deed] ≔ text read_file\n" +
    "show let join:[text₀ path:_path, text₁ path:_path, _path] ≔ text₀ · '/' $ · text₁ $ path";
  assert.deepEqual(await labels(source, "a"), [
    "typeParameter:declaration",
    "type:",
    "type:",
  ]);
  assert.deepEqual(await labels(source, "x"), [undefined, undefined]);
  assert.deepEqual(await labels(source, "_"), [undefined]);
  assert.deepEqual(await labels(source, "text"), [
    undefined,
    "type:",
    "type:",
    undefined,
  ]);
  assert.deepEqual(await labels(source, "text₀"), [undefined, undefined]);
  assert.deepEqual(await labels(source, "·"), ["call:applied", "call:applied"]);
  assert.deepEqual(await labels(source, "@"), ["keyword:", "keyword:"]);
  assert.deepEqual(await labels(source, "*"), ["keyword:", "keyword:"]);
  assert((await labels(source, ":")).every((label) => label === undefined));
});
test("names bound by worth slots stay terms inside later types", async () => {
  const source = "ilk =:[@α:*, a:α, α, *] { eftbend:a = a }\n" +
    "let leibnitz:[@α:*, @β:*, @a:α, @b:α, f:[α, β], eftbend:a = b, (a f) = (b f)] ≔ reflect\n" +
    "let other:[@a:*, a] ≔ sorry";
  assert.deepEqual(await labels(source, "a"), [
    undefined,
    undefined,
    undefined,
    undefined,
    undefined,
    undefined,
    "typeParameter:declaration",
    "type:",
  ]);
  assert.deepEqual(await labels(source, "f"), [
    undefined,
    "call:applied",
    "call:applied",
  ]);
  assert.deepEqual(await labels(source, "α"), [
    "typeParameter:declaration",
    "type:",
    "type:",
    "typeParameter:declaration",
    "type:",
    "type:",
    "type:",
  ]);
});
test("ilk-returning let declarations have type roles", async () => {
  const source = "show let powerset:[a:*, *] ≔ a → 𝟚\n" +
    "let predicate:ℤ powerset ≔ {_ ^ yea}";
  assert.deepEqual(await labels(source, "powerset"), [
    "type:declaration.typeFunction",
    "type:applied",
  ]);
  assert.deepEqual(await labels(source, "a"), [
    "typeParameter:declaration",
    "type:",
  ]);
});
test("declaration annotations retain compiler roles for prefixed names and greek parameters", async () => {
  const source = "let count:* ≔ ℤ\n" +
    "let sameness:[@α:*, x:α, α] ≔ x\n" +
    "let answer:count ≔ +42 sameness @count";
  assert.deepEqual(await labels(source, "count"), [
    "type:declaration",
    "type:",
    "type:",
  ]);
  assert.deepEqual(await labels(source, "α"), [
    "typeParameter:declaration",
    "type:",
    "type:",
  ]);
  assert.deepEqual(await labels(source, "x"), [undefined, undefined]);
  assert.deepEqual(await labels(source, "≔"), [
    undefined,
    undefined,
    undefined,
  ]);
  assert.deepEqual(await labels(source, "sameness"), [
    "function:declaration.applied",
    "call:applied",
  ]);
});
test("right composition useth ordinary function roles", async () => {
  const source = "let values:ℤ list ≔ >{cons, +1, empty}";
  assert.deepEqual(await labels(source, "values"), ["variable:declaration"]);
  assert.deepEqual(await labels(source, "list"), ["type:applied"]);
  assert.deepEqual(await labels(source, "cons"), ["call:applied"]);
  assert.deepEqual(await labels(source, ">{"), [undefined]);
  assert.deepEqual(await labels(source, "}"), [undefined]);
});
test("nested polymorphic binders use compiler type roles", async () => {
  const source = "let twice:[f:[@a:*, a, a], ℤ] ≔ +1 f";
  assert.deepEqual(await labels(source, "a"), [
    "typeParameter:declaration",
    "type:",
    "type:",
  ]);
  assert.deepEqual(await labels(source, "@"), ["keyword:"]);
  assert.deepEqual(await labels(source, "f"), [undefined, "call:applied"]);
});
test("explicit type arguments retain type roles among worth arguments", async () => {
  const source =
    "let f:[@a:*, @b:*, x:a, _:b, a] ≔ x\nyield 'x' f @text @(text list) empty";
  assert.deepEqual(await labels(source, "text"), ["type:", "type:"]);
  assert.deepEqual(await labels(source, "list"), ["type:applied"]);
  assert.deepEqual(await labels(source, "@"), [
    "keyword:",
    "keyword:",
    "keyword:",
    "keyword:",
  ]);
  assert.deepEqual(await labels(source, "f"), [
    "function:declaration.applied",
    "call:applied",
  ]);
});
test("compiler roles use GADT, flock and pattern grammar", async () => {
  const source = "show ilk tag: [a:*, *] { integer: ℤ tag, boolean: 𝟚 tag }\n" +
    "show flock functor:[f:[*, *], *] { let warp:[@a:*, @b:*, a f, [a, b], b f] let warp_sameness:[@a:*, af:a f, (af warp sameness) = af] }\n" +
    "show let void:[@f:[*, *], @:f functor, @a:*, af:a f, 𝟙 f] ≔ af warp {_ ^ only}\n" +
    "let read:[ℤ tag, ℤ] ≔ { x integer ^ x }";
  assert.deepEqual(await labels(source, "tag"), [
    "type:declaration.typeFunction",
    "type:applied",
    "type:applied",
    "type:applied",
  ]);
  assert.deepEqual(await labels(source, "functor"), [
    "class:declaration.typeFunction",
    "class:applied",
  ]);
  assert.deepEqual(await labels(source, "integer"), [
    "enumMember:declaration",
    "enumMember:",
  ]);
  assert.deepEqual(await labels(source, "_"), [undefined]);
  assert.deepEqual(await labels(source, "warp"), [
    "call:declaration.applied",
    "call:applied",
    "call:applied",
  ]);
});
test("local polymorphic binders have compiler roles in declarations", async () => {
  const source = "ilk packed: * { pack: [@a:*, a, packed] }\n" +
    "flock hath_≍:[a:*, *] { let rule:[@b:*, x:b, x = x] }\n" +
    "bizen:[@a:*, a hath_≍] {}";
  assert.deepEqual(await labels(source, "@"), [
    "keyword:",
    "keyword:",
    "keyword:",
  ]);
  assert.deepEqual(await labels(source, "a"), [
    "typeParameter:declaration",
    "type:",
    "typeParameter:declaration",
    "typeParameter:declaration",
    "type:",
  ]);
  assert.deepEqual(await labels(source, "hath_≍"), [
    "class:declaration.typeFunction",
    "class:applied",
  ]);
});
test("compiler highlighting recovereth incomplete syntax without accepting it", async () => {
  const source = "let before:ℤ ≔ +1\nlet broken [x:ℤ\nlet after:text ≔ 'ok'";
  assert.deepEqual(await labels(source, "ℤ"), ["type:", undefined]);
  assert.deepEqual(await labels(source, "text"), ["type:"]);
  assert.deepEqual(
    await labels("let before:ℤ ≔ +1\nlet broken ≔ 'unfinished", "ℤ"),
    ["type:"],
  );
  const result = await compiler.check({ text: source }, []).result;
  assert.equal(result.kind, "check");
  if (result.kind === "check") {
    assert.equal(result.diagnostics[0]?.kind, "parse");
  }
});
test("compiler spans warp unicode and line endings without eager name resolution", () => {
  const resolve = () => {
    throw new Error("navigation analysis was unnecessary");
  };
  assert.deepEqual(
    buildHighlightRanges(
      "𝟙\r\nℤ",
      [
        [0, 2, "type", []],
        [4, 5, "type", []],
      ],
      resolve,
    ),
    [
      { line: 0, char: 0, length: 2, type: "type", modifiers: [] },
      { line: 1, char: 0, length: 1, type: "type", modifiers: [] },
    ],
  );
  assert.deepEqual(
    buildHighlightRanges(
      "f x",
      [
        [0, 1, "call", ["applied"]],
        [2, 3, "term", []],
      ],
      resolve,
    ),
    [{ line: 0, char: 0, length: 1, type: "call", modifiers: ["applied"] }],
  );
});
test("highlight cache shareth requests and discardeth obsolete results", async () => {
  const requests = [];
  const cache = new HighlightCache({
    highlight: (text, version) => {
      let resolve;
      const result = new Promise<SourceRole[]>(
        (resolveResult) => (resolve = resolveResult),
      );
      const request = {
        text,
        version,
        result,
        resolve,
        cancelled: false,
        cancel() {
          this.cancelled = true;
        },
      };
      requests.push(request);
      return request;
    },
  });
  const first = cache.get("uri", "old", 1);
  const same = cache.get("uri", "old", 1);
  assert.equal(requests.length, 1);
  const latest = cache.get("uri", "new", 2);
  assert.equal(requests[0].cancelled, true);
  requests[0].resolve([[0, 3, "type", []]]);
  assert.deepEqual(await first, []);
  assert.deepEqual(await same, []);
  requests[1].resolve([[0, 3, "call", ["applied"]]]);
  assert.deepEqual(await latest, [[0, 3, "call", ["applied"]]]);
  assert.deepEqual(await cache.get("uri", "new", 2), await latest);
  assert.equal(requests.length, 2);
  cache.clear();
  assert.equal(requests[1].cancelled, true);
});
