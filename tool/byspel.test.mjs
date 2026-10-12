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

// running also checketh the whole program and rejecteth `sorry`.
for (const byspel of byspels) {
  const file = path.join("byspel", `${byspel}.tung`);
  const output = Object.hasOwn(outputs, byspel) ? outputs[byspel] : undefined;
  test(`${byspel} ${output === undefined ? "checketh" : "printeth its checked result"}`, () => {
    assert.deepEqual(
      run(
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
      "type error: in let 'worth': cannot unify string with ℤ\n",
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

test("checking retaineth goals beside errors without accepting the proof", (context) => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "tung-goals-"));
  context.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const file = path.join(directory, "proof.tung");
  const unfinished = "let unfinished:[x:ℤ, ℤ] ≔ sorry\n";
  for (const fault of ["let bad:ℤ ≔ 'text'", "let bad ≔"]) {
    const source = unfinished + fault;
    fs.writeFileSync(file, source);
    for (const result of [
      run(["--check-stdin"], source),
      run(["--check-module", file]),
    ]) {
      assert.equal(result.status, 1);
      assert.equal(result.error, "");
      assert.match(result.output, /(?:type|parse) error:/);
      assert.match(result.output, /goal: ℤ\n  x: ℤ/);
      assert.doesNotMatch(result.output, /type ok/);
    }
    const proof = run(["--check-proof", "unfinished", file]);
    assert.equal(proof.status, 1);
    assert.doesNotMatch(proof.output, /proof ok|goal:/);
  }
});

test("proof checking reporteth one theorem and enforceeth its axiom policy", (context) => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "tung-proof-"));
  context.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const file = path.join(directory, "proof.tung");
  fs.writeFileSync(
    file,
    `ilk =:[@α:*, x:α, α, *] { eftbend:x = @α x }
ilk one:* { only:one }
let proved:only = only ≔ eftbend
let unfinished:one ≔ sorry
orsetting axiom:only = only
orsetting unused:one
let dependent:only = only ≔ axiom
`,
  );
  assert.deepEqual(
    run(["--no-sorry", "--no-axioms", "--check-proof", "proved", file]),
    {
      output:
        "proof: proved\ntype: only = only\ndependencies: none\nproof ok\n",
      error: "",
      status: 0,
    },
  );
  for (const [options, status, verdict] of [
    [[], 0, "proof ok"],
    [["--allow-axiom", "axiom", "--allow-axiom", "unused"], 0, "proof ok"],
    [["--no-axioms"], 1, "proof error: axiom is not allowed: axiom"],
    [
      ["--allow-axiom", "proved"],
      1,
      "proof error: allowed axiom 'proved' is not an orsetting",
    ],
  ]) {
    assert.deepEqual(run([...options, "--check-proof", "dependent", file]), {
      output: `proof: dependent\ntype: only = only\norsetting: axiom: only = only\n${verdict}\n`,
      error: "",
      status,
    });
  }
  const unfinished = run(["--check-proof", "unfinished", file]);
  assert.equal(unfinished.status, 1);
  assert.equal(unfinished.error, "");
  assert.match(
    unfinished.output,
    /proof: unfinished\ntype: one\nsorry: sorry:/,
  );
  assert.match(unfinished.output, /proof error: unfinished proof: sorry\n$/);
  fs.writeFileSync(
    path.join(directory, "tung.yaml"),
    "dependencies: {}\nproof:\n  axioms: []\n",
  );
  assert.equal(run(["--check-proof", "dependent", file]).status, 1);
  assert.equal(
    run(["--allow-axiom", "axiom", "--check-proof", "dependent", file]).status,
    0,
  );
});
