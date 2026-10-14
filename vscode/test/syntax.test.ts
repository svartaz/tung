import assert from "node:assert/strict";
import test from "node:test";
import { findMatching, findOpening, tokenDepths } from "../server/syntax.ts";
import { analyzed } from "./compiler.ts";

test("token depths recover from an unmatched close", async () => {
  const { tokens } = await analyzed("} { (worth) }");
  assert.deepEqual(tokenDepths(tokens), [0, 0, 1, 2, 2, 1]);
});

test("right composition participateth in delimiter navigation", async () => {
  const { tokens } = await analyzed(">{cons, >{cons, worth, empty}, empty}");
  const opening = tokens.filter(({ text }) => text === ">{");
  const closing = tokens.filter(({ text }) => text === "}");
  assert.deepEqual(
    opening.map(({ index }) => findMatching(tokens, index)),
    [closing[1].index, closing[0].index],
  );
  assert.deepEqual(
    closing.map(({ index }) => findOpening(tokens, index)),
    [opening[1].index, opening[0].index],
  );
});

test("bracket lookups agree for nested and unmatched delimiters", async () => {
  const { tokens } = await analyzed("(<{worth} { unmatched ) } )");
  const opening = tokens.filter(({ text }) => ["(", "<{", "{"].includes(text));
  const closing = tokens.filter(({ text }) => [")", "}"].includes(text));

  assert.deepEqual(
    opening.map(({ index }) => findMatching(tokens, index)),
    [closing.at(-1)?.index, closing[0].index, closing[2].index],
  );
  assert.deepEqual(
    closing.map(({ index }) => findOpening(tokens, index)),
    [opening[1].index, -1, opening[2].index, opening[0].index],
  );
});
