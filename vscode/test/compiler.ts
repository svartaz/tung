// one compiler session per test file; models take its source syntax.
import * as path from "node:path";
import test from "node:test";
import { analyzeDocument } from "../server/analysis.ts";
import { CompilerBridge } from "../server/checker.ts";

const compiler = new CompilerBridge();
compiler.configure(
  path.resolve(__dirname, "../../../tongue"),
  [],
  process.env.TUNG_EXECUTABLE,
);
test.after(() => compiler.dispose());

const analyzed = async (source: string, uri = "") =>
  analyzeDocument(source, uri, await compiler.highlight(source).result);

export { analyzed, compiler };
