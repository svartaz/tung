import assert from "node:assert/strict";
import test from "node:test";
import { findDefinition, tokenAtPosition } from "../server/analysis.ts";
import { analyzed } from "./compiler.ts";
test("declaration annotations expose definitions and scoped parameters in incomplete buffers", async () => {
  const source = [
    "show let count:* ≔ ℤ",
    "show let selfness:[@α:*, x:α, α] ≔ x",
    "let hath_+: [x:, y:ℤ, ℤ] ≔ x + y",
    "let answer:count ≔ +42",
    "let outside ≔ x",
  ].join("\n");
  const model = await analyzed(source, "file:///annotations.tung");
  for (const [name, role] of [
    ["count", "type"],
    ["selfness", "function"],
    ["hath_+", "function"],
    ["answer", "variable"],
  ]) {
    assert(
      model.definitions.some(
        (definition) => definition.name === name && definition.role === role,
      ),
      name,
    );
  }
  const occurrences = model.tokens.filter(({ text }) => text === "x");
  assert.equal(
    findDefinition(model, occurrences[1])?.token.offset,
    occurrences[0].offset,
  );
  assert.equal(
    findDefinition(model, occurrences[3])?.token.offset,
    occurrences[2].offset,
  );
  assert.equal(findDefinition(model, occurrences.at(-1)), undefined);
});
test("analysis recordeth shown owners, members, parameters, and imports", async () => {
  const source =
    "use ground.tung show flock order_half:[a:*, @:a hath_≍, *] { let ≤:[a, a, 𝟚] } let <: [a:, b:] ≔ a ≤ b";
  const model = await analyzed(source, "file:///model.tung");
  assert.deepEqual(
    model.imports.map(({ path }) => path),
    ["ground.tung"],
  );
  assert(
    model.definitions.some(
      ({ name, role, exported }) =>
        name === "order_half" && role === "class" && exported,
    ),
  );
  assert(
    model.definitions.some(
      ({ name, role, exported, containerName }) =>
        name === "≤" &&
        role === "method" &&
        exported &&
        containerName === "order_half",
    ),
  );
  assert(
    model.definitions.some(
      ({ name, role, local }) => name === "a" && role === "parameter" && local,
    ),
  );
});
test("class parameters resolve inside the braced body", async () => {
  const source = "flock hath_+:[a:*, *] { let +:[a, a, a] } let outside ≔ a";
  const model = await analyzed(source, "file:///flock.tung");
  const occurrences = model.tokens.filter(({ text }) => text === "a");
  const inside = findDefinition(model, occurrences[1], occurrences[1].offset);
  assert.equal(inside?.role, "typeParameter");
  assert.equal(inside?.token.offset, occurrences[0].offset);
  assert.equal(
    findDefinition(model, occurrences.at(-1), occurrences.at(-1).offset),
    undefined,
  );
});
test("instance parameters resolve in requirements, the head, and members", async () => {
  const source = [
    "bizen:[@a:*, @:a parent, [a, a] selfness] {",
    "  let selfness:[[a, a], [a, a]] ≔ { x ^ x }",
    "}",
    "let outside ≔ a",
  ].join("\n");
  const model = await analyzed(source, "file:///instance.tung");
  const occurrences = model.tokens.filter(({ text }) => text === "a");
  for (const token of occurrences.slice(1, -1)) {
    const definition = findDefinition(model, token);
    assert.equal(definition?.role, "typeParameter");
    assert.equal(definition?.token.offset, occurrences[0].offset);
  }
  assert.equal(findDefinition(model, occurrences.at(-1)), undefined);
  assert.deepEqual(
    model.instances.map(({ className }) => className),
    ["selfness"],
  );
  assert.equal(
    model.definitions.find(({ name }) => name === "selfness")?.role,
    "method",
  );
});
test("instances without parameter brackets retain their class and members", async () => {
  const model = await analyzed(
    "bizen:[ℤ, ℤ] ring { let -: [f:, g:, x:] ≔ (x f) - (x g) }",
    "file:///instance.tung",
  );
  assert.deepEqual(
    model.instances.map(({ className }) => className),
    ["ring"],
  );
  assert.equal(
    model.definitions.find(({ name }) => name === "-")?.role,
    "method",
  );
});
test("requirement parameters respect nested types and owner scope", async () => {
  const source =
    "flock child:[a:*, b:*, @:[a, b] parent, *] { let f:[@:a hath_≍, a, b] }";
  const model = await analyzed(source);
  for (const name of ["a", "b"]) {
    const uses = model.tokens.filter((token) => token.text === name);
    const binders = model.definitions.filter(
      (definition) => definition.name === name,
    );
    assert.equal(binders.length, 1);
    for (const token of uses)
      assert.equal(findDefinition(model, token)?.token.offset, uses[0].offset);
  }
});
test("analysis recordeth foreign import paths", async () => {
  const source = "use _foreign.tung\nuse flock/algebra/arithmetic/field.tung";
  const model = await analyzed(source, "file:///imports.tung");
  assert.deepEqual(
    model.imports.map(({ path }) => path),
    ["_foreign.tung", "flock/algebra/arithmetic/field.tung"],
  );
});
test("analysis recordeth an optional import alias separately from its path", async () => {
  const model = await analyzed(
    "use ilk/list.tung list yield list~empty",
    "file:///imports.tung",
  );
  assert.deepEqual(
    model.imports.map(({ path, namespace, alias }) => ({
      path,
      namespace,
      alias,
    })),
    [
      {
        path: "ilk/list.tung",
        namespace: "list",
        alias: "list",
      },
    ],
  );
});
test("analysis defaulteth an import namespace to its last path segment", async () => {
  const model = await analyzed(
    "use ilk/list.tung yield list~empty",
    "file:///imports.tung",
  );
  assert.deepEqual(
    model.imports.map(({ namespace, alias }) => ({ namespace, alias })),
    [
      {
        namespace: "list",
        alias: undefined,
      },
    ],
  );
});
test("analysis ignoreth dots in directories when defaulting a namespace", async () => {
  const model = await analyzed(
    "use pkg.one/query.tung yield query~answer",
    "file:///imports.tung",
  );
  assert.equal(model.imports[0].namespace, "query");
});
test("analysis recordeth each re-exported name", async () => {
  const model = await analyzed("show first, second", "file:///exports.tung");
  assert.deepEqual(model.reexports, [{ name: "first" }, { name: "second" }]);
});
test("analysis attacheth doc comments to following shown declarations", async () => {
  const source = [
    "## selfness worth.",
    "show let selfness:[@a:*, @:a hath_≍, x: a, a] ≔ x",
    "",
    "/**",
    " * boxed data.",
    " */",
    "show ilk box: [a:*, *] { box: [a, a box] }",
  ].join("\n");
  const model = await analyzed(source, "file:///docs.tung");
  assert.equal(
    model.definitions.find(({ name }) => name === "selfness").documentation,
    "selfness worth.",
  );
  assert.equal(
    model.definitions.find(
      ({ name, role }) => name === "box" && role === "type",
    ).documentation,
    "boxed data.",
  );
});
test("local resolution preferreth the narrowest binder scope", async () => {
  const source = "let keep:[x: ℤ, ℤ] ≔ match x { x ^ x }";
  const model = await analyzed(source, "file:///scope.tung");
  const use = model.tokens.filter(({ text }) => text === "x").at(-1);
  const definition = findDefinition(model, use, use.offset);
  assert.equal(definition.role, "parameter");
  assert.equal(
    definition.token.offset,
    model.tokens.filter(({ text }) => text === "x").at(-2).offset,
  );
});
test("inferred and annotated slots resolve in one function body", async () => {
  const source = "let hath_+: [a:, b: ℤ, ℤ] ≔ a + b";
  const model = await analyzed(source, "file:///mixed_header.tung");
  for (const name of ["a", "b"]) {
    const occurrences = model.tokens.filter(({ text }) => text === name);
    const use = occurrences.at(-1);
    const definition = findDefinition(model, use, use.offset);
    assert.equal(definition.role, "parameter");
    assert.equal(definition.token.offset, occurrences[0].offset);
  }
});
test("an unfinished lambda scopeth its binders to the end of the buffer", async () => {
  const source = "let choose ≔ { left, right ^ right";
  const model = await analyzed(source, "file:///incomplete_pattern.tung");
  const occurrences = model.tokens.filter(({ text }) => text === "right");
  const use = occurrences.at(-1);
  const definition = findDefinition(model, use, use.offset);
  assert.equal(definition.token.offset, occurrences[0].offset);
  assert.equal(definition.scopeEnd, source.length);
});
test("an unmatched inner delimiter doth not leak a pattern scope", async () => {
  const source = "let choose ≔ ({ left, right ^ right ) let outside ≔ right";
  const model = await analyzed(source, "file:///recovered_pattern.tung");
  const occurrences = model.tokens.filter(({ text }) => text === "right");
  const innerDefinition = findDefinition(
    model,
    occurrences[1],
    occurrences[1].offset,
  );
  assert.equal(innerDefinition.token.offset, occurrences[0].offset);
  assert.equal(innerDefinition.scopeEnd, source.indexOf(")"));
  assert.equal(
    findDefinition(model, occurrences[2], occurrences[2].offset),
    undefined,
  );
});
test("token lookup excludeth the character after a token", async () => {
  const model = await analyzed("let answer ≔ +42", "file:///token.tung");
  assert.equal(
    tokenAtPosition(model, { line: 0, character: 4 }).text,
    "answer",
  );
  assert.equal(tokenAtPosition(model, { line: 0, character: 10 }), undefined);
});
