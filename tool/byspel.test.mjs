import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import test from "node:test";
import { fileURLToPath } from "node:url";

// every byspel checketh as a runnable file. predictable output is compared
// exactly, including examples whose task delays are random.
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const executable = process.env.TUNG_EXECUTABLE;
const byspels = fs
  .readdirSync(path.join(root, "byspel"))
  .filter((name) => name.endsWith(".tung"))
  .map((name) => name.slice(0, -".tung".length));
const outputs = {
  asynchronous: "async\n42\n",
  fizzbuzz:
    Array.from({ length: 32 }, (_, n) =>
      n % 15 === 0
        ? "fizzbuzz"
        : n % 3 === 0
          ? "fizz"
          : n % 5 === 0
            ? "buzz"
            : String(n),
    ).join("\n") + "\n",
  lambda: "!\n",
  scoreboard: `launching match jobs

results
north 3 - 1 south
east 2 - 2 west
south - east:cancelled:a score cannot be negative
west 1 - 2 north

standings
north:6 points from 2 games
south:0 points from 1 game
east:1 points from 1 game
west:1 points from 2 games
`,
};

function run(args, input = "") {
  assert.ok(executable, "TUNG_EXECUTABLE nameth the built compiler");
  const result = spawnSync(executable, args, {
    cwd: root,
    input,
    encoding: "utf8",
    timeout: 30000,
  });
  assert.ifError(result.error);
  return { output: result.stdout, error: result.stderr, status: result.status };
}

// this byspel useth bookhoard bizens whose laws are still `sorry` (text and
// set), so its `main` dependeth on that assumption.
const assuming = new Set(["word_count"]);

for (const byspel of byspels) {
  const file = path.join("byspel", `${byspel}.tung`);
  test(`${byspel} checketh`, () => {
    assert.deepEqual(run(["--check", file]), {
      output: assuming.has(byspel) ? "type ok\nsorry: main\n" : "type ok\n",
      error: "",
      status: 0,
    });
  });
  if (Object.hasOwn(outputs, byspel)) {
    test(`${byspel} printeth its result`, () => {
      assert.deepEqual(run([file]), {
        output: outputs[byspel],
        error: "",
        status: 0,
      });
    });
  }
}

test("word_count readeth its file and counteth repeated words", (context) => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "tung-word-count-"));
  context.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const file = path.join(directory, "words.txt");
  fs.writeFileSync(file, "a b a\n");
  assert.deepEqual(run(["byspel/word_count.tung", file]), {
    output: "a:2\nb:1\n",
    error: "",
    status: 0,
  });
});

test("checking listeth shown declarations that assume sorry", () => {
  const source =
    "show let assumed:ℤ ≔ sorry\nshow let built:ℤ ≔ assumed\nlet hidden:ℤ ≔ sorry\nshow let proved:ℤ ≔ +1";
  assert.deepEqual(run(["--check-stdin"], source), {
    output:
      "type ok\nsorry: assumed\nsorry: built\n<stdin>:1:22:1:27: goal: ℤ\n<stdin>:3:16:3:21: goal: ℤ\n",
    error: "",
    status: 0,
  });
  assert.deepEqual(run(["--no-sorry", "--check-stdin"], source), {
    output: "sorry: assumed\nsorry: built\n",
    error: "",
    status: 1,
  });
});

test("stdin checking reporteth success and rejection through its exit status", () => {
  for (const [source, output, status] of [
    ["let worth:ℤ ≔ +1", "type ok\n", 0],
    ["let worth ≔", "parse error: expected an expression\n", 1],
    [
      "let worth:ℤ ≔ 'text'",
      "type error: in let 'worth': cannot unify text with ℤ\n",
      1,
    ],
  ]) {
    assert.deepEqual(
      run(["--check-stdin"], source),
      { output, error: "", status },
      source,
    );
  }
});
