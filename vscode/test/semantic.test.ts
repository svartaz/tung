import assert from "node:assert/strict";
import * as path from "node:path";
import test from "node:test";
import {
  CompilerBridge,
  emptySyntax,
  SourceRole,
  SourceSyntax,
} from "../server/checker.ts";
import { buildHighlightRanges } from "../server/highlight.ts";
import { WorkspaceIndex } from "../server/workspace.ts";

const withRoles = (roles: SourceRole[]): SourceSyntax => ({
  ...emptySyntax,
  roles,
});

const compiler = new CompilerBridge();
compiler.configure(
  path.resolve(__dirname, "../../../tongue"),
  [],
  process.env.TUNG_EXECUTABLE,
);
test.after(() => compiler.dispose());
const sourceLabels = async (source: string) => {
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
  const { roles } = await workspace.syntax(uri, source);
  const ranges = buildHighlightRanges(
    source,
    roles,
    (token) =>
      workspace.resolveAt(uri, { line: token.line, character: token.char })
        .definition,
  );
  return (name: string) =>
    model.tokens
      .filter((token) => token.text === name)
      .map((token) => {
        const range = ranges.find(
          (range) => range.line === token.line && range.char === token.char,
        );
        return range && `${range.type}:${range.modifiers.join(".")}`;
      });
};
test("compiler roles keep types, header binders and application positions consistent", async () => {
  const source =
    "show let constant:[@a:*, @b:*, x:a, _:b, a] ≔ x\n" +
    "show let read:[string path:_path, (string ∑ string) deed] ≔ string read_file\n" +
    "show let yoke:[string₀ path:_path, string₁ path:_path, _path] ≔ string₀ · '/' $ · string₁ $ path";
  const labels = await sourceLabels(source);
  assert.deepEqual(labels("a"), [
    "typeParameter:declaration",
    "type:",
    "type:",
  ]);
  assert.deepEqual(labels("x"), [undefined, undefined]);
  assert.deepEqual(labels("_"), [undefined]);
  assert.deepEqual(labels("string"), [undefined, "type:", "type:", undefined]);
  assert.deepEqual(labels("string₀"), [undefined, undefined]);
  assert.deepEqual(labels("·"), ["call:applied", "call:applied"]);
  assert.deepEqual(labels("@"), ["keyword:", "keyword:"]);
  assert.deepEqual(labels("*"), ["keyword:", "keyword:"]);
  assert(labels(":").every((label) => label === undefined));
});
test("names bound by worth slots stay terms inside later types", async () => {
  const source =
    "ilk =:[@α:*, a:α, α, *] { eftbend:a = a }\n" +
    "let leibnitz:[@α:*, @β:*, @a:α, @b:α, f:[α, β], eftbend:a = b, (a f) = (b f)] ≔ reflect\n" +
    "let other:[@a:*, a] ≔ sorry";
  const labels = await sourceLabels(source);
  assert.deepEqual(labels("a"), [
    undefined,
    undefined,
    undefined,
    undefined,
    undefined,
    undefined,
    "typeParameter:declaration",
    "type:",
  ]);
  assert.deepEqual(labels("f"), [undefined, "call:applied", "call:applied"]);
  assert.deepEqual(labels("α"), [
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
  const source =
    "show let powerset:[a:*, *] ≔ a → 𝟚\n" +
    "let predicate:ℤ powerset ≔ {_ ^ yea}";
  const labels = await sourceLabels(source);
  assert.deepEqual(labels("powerset"), [
    "type:declaration.typeFunction",
    "type:applied",
  ]);
  assert.deepEqual(labels("a"), ["typeParameter:declaration", "type:"]);
});
test("declaration annotations retain compiler roles for prefixed names and greek parameters", async () => {
  const source =
    "let rime:* ≔ ℤ\n" +
    "let sameness:[@α:*, x:α, α] ≔ x\n" +
    "let answer:rime ≔ +42 sameness @rime";
  const labels = await sourceLabels(source);
  assert.deepEqual(labels("rime"), ["type:declaration", "type:", "type:"]);
  assert.deepEqual(labels("α"), [
    "typeParameter:declaration",
    "type:",
    "type:",
  ]);
  assert.deepEqual(labels("x"), [undefined, undefined]);
  assert.deepEqual(labels("≔"), [undefined, undefined, undefined]);
  assert.deepEqual(labels("sameness"), [
    "function:declaration.applied",
    "call:applied",
  ]);
});
test("right composition useth ordinary function roles", async () => {
  const source = "let values:ℤ list ≔ >{cons, +1, empty}";
  const labels = await sourceLabels(source);
  assert.deepEqual(labels("values"), ["variable:declaration"]);
  assert.deepEqual(labels("list"), ["type:applied"]);
  assert.deepEqual(labels("cons"), ["call:applied"]);
  assert.deepEqual(labels(">{"), [undefined]);
  assert.deepEqual(labels("}"), [undefined]);
});
test("nested polymorphic binders use compiler type roles", async () => {
  const source = "let twice:[f:[@a:*, a, a], ℤ] ≔ +1 f";
  const labels = await sourceLabels(source);
  assert.deepEqual(labels("a"), [
    "typeParameter:declaration",
    "type:",
    "type:",
  ]);
  assert.deepEqual(labels("@"), ["keyword:"]);
  assert.deepEqual(labels("f"), [undefined, "call:applied"]);
});
test("explicit type arguments retain type roles among worth arguments", async () => {
  const source =
    "let f:[@a:*, @b:*, x:a, _:b, a] ≔ x\nyield 'x' f @string @(string list) empty";
  const labels = await sourceLabels(source);
  assert.deepEqual(labels("string"), ["type:", "type:"]);
  assert.deepEqual(labels("list"), ["type:applied"]);
  assert.deepEqual(labels("@"), [
    "keyword:",
    "keyword:",
    "keyword:",
    "keyword:",
  ]);
  assert.deepEqual(labels("f"), [
    "function:declaration.applied",
    "call:applied",
  ]);
});
test("compiler roles use GADT, flock and pattern grammar", async () => {
  const source =
    "show ilk tag: [a:*, *] { integer: ℤ tag, boolean: 𝟚 tag }\n" +
    "show flock functor:[f:[*, *], *] { let value_type:* let typed:value_type let warp:[@a:*, @b:*, a f, [a, b], b f] let warp_sameness:[@a:*, af:a f, (af warp sameness) = af] }\n" +
    "show let void:[@f:[*, *], @:f functor, @a:*, af:a f, 𝟙 f] ≔ af warp {_ ^ only}\n" +
    "let read:[ℤ tag, ℤ] ≔ { x integer ^ x }";
  const labels = await sourceLabels(source);
  assert.deepEqual(labels("tag"), [
    "type:declaration.typeFunction",
    "type:applied",
    "type:applied",
    "type:applied",
  ]);
  assert.deepEqual(labels("functor"), [
    "class:declaration.typeFunction",
    "class:applied",
  ]);
  assert.deepEqual(labels("integer"), [
    "enumMember:declaration",
    "enumMember:",
  ]);
  assert.deepEqual(labels("_"), [undefined]);
  assert.deepEqual(labels("warp"), [
    "call:declaration.applied",
    "call:applied",
    "call:applied",
  ]);
  assert.deepEqual(labels("value_type"), ["call:declaration.applied", "type:"]);
});
test("local polymorphic binders have compiler roles in declarations", async () => {
  const source =
    "ilk packed: * { pack: [@a:*, a, packed] }\n" +
    "flock hath_≍:[a:*, *] { let rule:[@b:*, x:b, x = x] }\n" +
    "bizen:[@a:*, a hath_≍] {}";
  const labels = await sourceLabels(source);
  assert.deepEqual(labels("x"), [undefined, undefined, undefined]);
  assert.deepEqual(labels("@"), ["keyword:", "keyword:", "keyword:"]);
  assert.deepEqual(labels("a"), [
    "typeParameter:declaration",
    "type:",
    "typeParameter:declaration",
    "typeParameter:declaration",
    "type:",
  ]);
  assert.deepEqual(labels("hath_≍"), [
    "class:declaration.typeFunction",
    "class:applied",
  ]);
});
test("compiler highlighting recovereth incomplete syntax without accepting it", async () => {
  const source = "let before:ℤ ≔ +1\nlet broken [x:ℤ\nlet after:string ≔ 'ok'";
  const labels = await sourceLabels(source);
  assert.deepEqual(labels("ℤ"), ["type:", undefined]);
  assert.deepEqual(labels("string"), ["type:"]);
  assert.deepEqual(
    (await sourceLabels("let before:ℤ ≔ +1\nlet broken ≔ 'unfinished"))("ℤ"),
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
test("navigation and colouring share requests and discard obsolete results", async () => {
  const requests = [];
  let source = "old";
  const document = { uri: "uri", version: 1, getText: () => source };
  const cache = new WorkspaceIndex(
    { get: () => document, all: () => [document] },
    {
      highlight: (text, version) => {
        let resolve;
        const result = new Promise<SourceSyntax>(
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
    },
  );
  const first = cache.syntax("uri", source, document.version);
  const same = cache.syntax("uri", source, document.version);
  const navigation = cache.ready();
  assert.equal(requests.length, 1);
  source = "new";
  document.version = 2;
  cache.invalidate("uri");
  const latest = cache.syntax("uri", source, document.version);
  assert.equal(requests[0].cancelled, true);
  requests[0].resolve(withRoles([[0, 3, "type", []]]));
  assert.deepEqual(await first, emptySyntax);
  assert.deepEqual(await same, emptySyntax);
  await navigation;
  requests[1].resolve(withRoles([[0, 3, "call", ["applied"]]]));
  assert.deepEqual((await latest).roles, [[0, 3, "call", ["applied"]]]);
  assert.deepEqual(
    await cache.syntax("uri", source, document.version),
    await latest,
  );
  await cache.ready();
  assert.equal(requests.length, 2);
  document.version++;
  const pending = cache.syntax("uri", source, document.version);
  assert.equal(requests[1].cancelled, true);
  document.version++;
  cache.invalidate("uri");
  const current = cache.syntax("uri", source, document.version);
  assert.equal(requests[2].cancelled, true);
  requests[2].resolve(withRoles([[0, 3, "type", ["declaration"]]]));
  assert.deepEqual(await pending, emptySyntax);
  cache.clearSyntax();
  requests[3].resolve(withRoles([[0, 3, "type", ["declaration"]]]));
  assert.deepEqual(await current, emptySyntax);
  assert.equal(cache.model("uri").definitions.length, 0);
});
