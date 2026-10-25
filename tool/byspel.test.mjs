import assert from "node:assert/strict";
import { spawn } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import test, { describe } from "node:test";
import { fileURLToPath } from "node:url";

// every byspel checketh without `sorry`, as a program when it defineth
// `main` and as a module otherwise. predictable output is compared exactly,
// including examples whose task delays are random.
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
const executable = process.env.TUNG_EXECUTABLE;
const byspels = fs
  .readdirSync(path.join(root, "byspel"), { recursive: true })
  .filter((name) => name.endsWith(".tung"))
  .map((name) => name.slice(0, -".tung".length))
  .sort();
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

// a run that outlasteth its limit is stopped, and its test faileth.
function run(args, input = "", timeout = 30000) {
  assert.ok(executable, "TUNG_EXECUTABLE nameth the built compiler");
  return new Promise((resolve, reject) => {
    const child = spawn(executable, args, { cwd: root, timeout });
    let output = "";
    let error = "";
    child.stdout.setEncoding("utf8").on("data", (chunk) => (output += chunk));
    child.stderr.setEncoding("utf8").on("data", (chunk) => (error += chunk));
    child.on("error", reject);
    child.on("close", (status, signal) =>
      signal
        ? reject(new Error(`${args.join(" ")} stopped by ${signal}`))
        : resolve({ output, error, status }),
    );
    child.stdin.end(input);
  });
}

// a rebuilt compiler findeth the interface cache cold. checking every library
// module a byspel bringeth first fileth its interfaces, in one process, so each
// byspel's limit measureth that byspel alone rather than the library beneath it.
const library = [
  ...new Set(
    byspels.flatMap((byspel) =>
      [
        ...fs
          .readFileSync(path.join(root, "byspel", `${byspel}.tung`), "utf8")
          .matchAll(/^bring (\S+)/gm),
      ].map((match) => match[1]),
    ),
  ),
]
  .filter((module) => fs.existsSync(path.join(root, "library", module)))
  .sort();

test.before(async () => {
  const brings = library.map((module) => `bring ${module}`).join("\n");
  assert.deepEqual(await run(["--check-stdin"], brings, 600000), {
    output: "type ok\n",
    error: "",
    status: 0,
  });
});

// running also checketh the whole program and rejecteth `sorry`. byspels are
// independent, so they run side by side.
describe("byspels", { concurrency: os.availableParallelism() }, () => {
  for (const byspel of byspels) {
    const file = path.join("byspel", `${byspel}.tung`);
    const output = Object.hasOwn(outputs, byspel) ? outputs[byspel] : undefined;
    test(`${byspel} ${output === undefined ? "checketh" : "printeth its checked result"}`, async () => {
      assert.deepEqual(
        await run(
          output === undefined
            ? ["--no-sorry", "--check", file]
            : ["--no-sorry", file],
        ),
        {
          output: output ?? "type ok\n",
          error: "",
          status: 0,
        },
      );
    });
  }
});

test("word_count readeth its file and counteth repeated words", async (context) => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "tung-word-count-"));
  context.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const file = path.join(directory, "words.txt");
  fs.writeFileSync(file, "a b a\n");
  assert.deepEqual(await run(["byspel/word_count.tung", file]), {
    output: "a:2\nb:1\n",
    error: "",
    status: 0,
  });
});

test("checking listeth shown declarations that assume sorry", async () => {
  const source =
    "show let assumed:ℤ ≔ sorry\nshow let built:ℤ ≔ assumed\nlet hidden:ℤ ≔ sorry\nshow let proved:ℤ ≔ +1";
  assert.deepEqual(await run(["--check-stdin"], source), {
    output:
      "type ok\nsorry: assumed\nsorry: built\n<stdin>:1:22:1:27: goal: ℤ\n<stdin>:3:16:3:21: goal: ℤ\n",
    error: "",
    status: 0,
  });
  assert.deepEqual(await run(["--no-sorry", "--check-stdin"], source), {
    output: "sorry: assumed\nsorry: built\n",
    error: "",
    status: 1,
  });
});

test("stdin checking reporteth success and rejection through its exit status", async () => {
  for (const [source, output, status] of [
    ["let value:ℤ ≔ +1", "type ok\n", 0],
    ["let value ≔", "parse error: expected an expression\n", 1],
    [
      "let value:ℤ ≔ 'text'",
      "type error: in let 'value': cannot unify string with ℤ\n",
      1,
    ],
  ]) {
    assert.deepEqual(
      await run(["--check-stdin"], source),
      { output, error: "", status },
      source,
    );
  }
});

test("checking retaineth goals beside errors without accepting the proof", async (context) => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "tung-goals-"));
  context.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const file = path.join(directory, "proof.tung");
  const unfinished = "let unfinished:[x:ℤ, ℤ] ≔ sorry\n";
  for (const fault of ["let bad:ℤ ≔ 'text'", "let bad ≔"]) {
    const source = unfinished + fault;
    fs.writeFileSync(file, source);
    for (const result of [
      await run(["--check-stdin"], source),
      await run(["--check", file]),
    ]) {
      assert.equal(result.status, 1);
      assert.equal(result.error, "");
      assert.match(result.output, /(?:type|parse) error:/);
      assert.match(result.output, /goal: ℤ\n  x: ℤ/);
      assert.doesNotMatch(result.output, /type ok/);
    }
    const proof = await run(["--name", "unfinished", file]);
    assert.equal(proof.status, 1);
    assert.doesNotMatch(proof.output, /name ok|goal:/);
  }
});

test("name checking reporteth one name and enforceeth its policies", async (context) => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "tung-proof-"));
  context.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const file = path.join(directory, "proof.tung");
  fs.writeFileSync(
    file,
    `type =:[@α:*, x:α, α, *] { reflect:x = @α x }
type one:* { only:one }
let proved:only = only ≔ reflect
let unfinished:one ≔ sorry
axiom assumed:only = only
axiom unused:one
let dependent:only = only ≔ assumed
`,
  );
  assert.deepEqual(
    await run(["--no-sorry", "--no-axiom", "--name", "proved", file]),
    {
      output: "name: proved\ntype: only = only\ndependencies: none\nname ok\n",
      error: "",
      status: 0,
    },
  );
  for (const [options, status, verdict] of [
    [[], 0, "name ok"],
    [["--allow-axiom", "assumed", "--allow-axiom", "unused"], 0, "name ok"],
    [["--no-axiom"], 1, "name error: axiom is not allowed: assumed"],
    [
      ["--allow-axiom", "proved"],
      1,
      "name error: allowed name 'proved' is not an axiom",
    ],
  ]) {
    assert.deepEqual(await run([...options, "--name", "dependent", file]), {
      output: `name: dependent\ntype: only = only\naxiom: assumed: only = only\n${verdict}\n`,
      error: "",
      status,
    });
  }
  const listed = await run(["--name", "unfinished", file]);
  assert.equal(listed.status, 0);
  assert.match(listed.output, /name: unfinished\ntype: one\nsorry: sorry:/);
  assert.match(listed.output, /name ok\n$/);
  const unfinished = await run(["--no-sorry", "--name", "unfinished", file]);
  assert.equal(unfinished.status, 1);
  assert.equal(unfinished.error, "");
  assert.match(unfinished.output, /name: unfinished\ntype: one\nsorry: sorry:/);
  assert.match(unfinished.output, /name error: unfinished proof: sorry\n$/);
  fs.writeFileSync(
    path.join(directory, "tung.yaml"),
    "dependencies: {}\nproof:\n  axioms: []\n",
  );
  assert.equal((await run(["--name", "dependent", file])).status, 1);
  assert.equal(
    (await run(["--allow-axiom", "assumed", "--name", "dependent", file]))
      .status,
    0,
  );
});
