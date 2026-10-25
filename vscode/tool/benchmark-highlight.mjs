// run after building the compiler and editor. timings include protocol transport,
// document analysis, name refinement, and token mapping, without type checking.
import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";

const require = createRequire(import.meta.url);
const { CompilerBridge } = require("../out/server/checker.js");
const { buildHighlightRanges } = require("../out/server/highlight.js");
const { WorkspaceIndex } = require("../out/server/workspace.js");
const root = fileURLToPath(new URL("../../", import.meta.url));
const compiler = new CompilerBridge();
compiler.configure(`${root}/tongue`, [], process.env.TUNG_EXECUTABLE);
const samples = [
  ["path", readFileSync(`${root}/library/type/path.tung`, "utf8")],
  ["mockingbird", readFileSync(`${root}/library/mockingbird.tung`, "utf8")],
  ...[1000, 5000].flatMap((size) =>
    [false, true].map((broken) => [
      `${size} ${broken ? "incomplete" : "complete"}`,
      Array.from(
        { length: size },
        (_, i) => `let value${i}${broken ? ":[ℤ" : ":ℤ ≔ +1"}`,
      ).join("\n"),
    ]),
  ),
  [
    "1000 functions",
    Array.from({ length: 1000 }, (_, i) => `let f${i}:[x:ℤ, ℤ] ≔ x`).join("\n"),
  ],
];
const median = (values) =>
  values.sort((a, b) => a - b)[Math.floor(values.length / 2)].toFixed(1);
try {
  const started = performance.now();
  if (!(await compiler.highlight("").result))
    throw new Error("build a compiler with highlighting support");
  console.log(
    `compiler discovery and startup: ${(performance.now() - started).toFixed(1)} ms`,
  );
  for (const [name, source] of samples) {
    const uri = `file://${root}/library/type/benchmark.tung`;
    const document = { uri, version: 0, getText: () => source };
    const workspace = new WorkspaceIndex(
      {
        get: (key) => (key === uri ? document : undefined),
        all: () => [document],
      },
      compiler,
    );
    workspace.configure([root], [`${root}/library`]);
    await workspace.ready();
    const elapsed = [],
      cached = [];
    let count = 0;
    for (let version = 1; version <= 3; version++) {
      document.version = version;
      workspace.invalidate(uri);
      const start = performance.now();
      const { roles } = await workspace.syntax(uri, source, version);
      const resolve = (token) =>
        workspace.resolveAt(uri, { line: token.line, character: token.char })
          .definition;
      count = buildHighlightRanges(source, roles, resolve).length;
      elapsed.push(performance.now() - start);
      const cacheStart = performance.now();
      buildHighlightRanges(
        source,
        (await workspace.syntax(uri, source, version)).roles,
        resolve,
      );
      cached.push(performance.now() - cacheStart);
    }
    console.log(
      `${name}: ${source.length} UTF-16 units, ${count} roles; fresh ${median(elapsed)} ms, cached ${median(cached)} ms`,
    );
  }
} finally {
  compiler.dispose();
}
