import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import test from "node:test";
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

function run(args, input = "", timeout = 30000) {
  assert.ok(executable, "TUNG_EXECUTABLE nameth the built compiler");
  const result = spawnSync(executable, args, {
    cwd: root,
    input,
    encoding: "utf8",
    timeout,
  });
  assert.ifError(result.error);
  return { output: result.stdout, error: result.stderr, status: result.status };
}

// a rebuilt compiler findeth the interface cache cold. checking bookhoard once
// first fileth its interfaces, so each byspel's limit measureth that byspel
// alone rather than the whole library.
test.before(() => {
  assert.deepEqual(
    run(["--check", "bookhoard/often.tung"], "", 600000).status,
    0,
  );
});

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
        output: output ?? "ilk ok\n",
        error: "",
        status: 0,
      },
    );
  });
}

test("word_rime readeth its file and rimeth repeated words", (context) => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "tung-word-rime-"));
  context.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const file = path.join(directory, "words.txt");
  fs.writeFileSync(file, "a b a\n");
  assert.deepEqual(run(["byspel/word_rime.tung", file]), {
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
      "ilk ok\nsorry: assumed\nsorry: built\n<stdin>:1:22:1:27: goal: ℤ\n<stdin>:3:16:3:21: goal: ℤ\n",
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
    ["let worth:ℤ ≔ +1", "ilk ok\n", 0],
    ["let worth ≔", "parse error: expected an expression\n", 1],
    [
      "let worth:ℤ ≔ 'text'",
      "ilk error: in let 'worth': cannot unify string with ℤ\n",
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
      run(["--check", file]),
    ]) {
      assert.equal(result.status, 1);
      assert.equal(result.error, "");
      assert.match(result.output, /(?:ilk|parse) error:/);
      assert.match(result.output, /goal: ℤ\n  x: ℤ/);
      assert.doesNotMatch(result.output, /ilk ok/);
    }
    const proof = run(["--name", "unfinished", file]);
    assert.equal(proof.status, 1);
    assert.doesNotMatch(proof.output, /name ok|goal:/);
  }
});

test("name checking reporteth one name and enforceeth its policies", (context) => {
  const directory = fs.mkdtempSync(path.join(os.tmpdir(), "tung-proof-"));
  context.after(() => fs.rmSync(directory, { recursive: true, force: true }));
  const file = path.join(directory, "proof.tung");
  fs.writeFileSync(
    file,
    `ilk =:[@α:*, x:α, α, *] { eftbend:x = @α x }
ilk one:* { only:one }
let proved:only = only ≔ eftbend
let unfinished:one ≔ sorry
orsetting assumed:only = only
orsetting unused:one
let dependent:only = only ≔ assumed
`,
  );
  assert.deepEqual(
    run(["--no-sorry", "--no-orset", "--name", "proved", file]),
    {
      output: "name: proved\nilk: only = only\ndependencies: none\nname ok\n",
      error: "",
      status: 0,
    },
  );
  for (const [options, status, verdict] of [
    [[], 0, "name ok"],
    [["--allow-orset", "assumed", "--allow-orset", "unused"], 0, "name ok"],
    [["--no-orset"], 1, "name error: orsetting is not allowed: assumed"],
    [
      ["--allow-orset", "proved"],
      1,
      "name error: allowed name 'proved' is not an orsetting",
    ],
  ]) {
    assert.deepEqual(run([...options, "--name", "dependent", file]), {
      output: `name: dependent\nilk: only = only\norsetting: assumed: only = only\n${verdict}\n`,
      error: "",
      status,
    });
  }
  const listed = run(["--name", "unfinished", file]);
  assert.equal(listed.status, 0);
  assert.match(listed.output, /name: unfinished\nilk: one\nsorry: sorry:/);
  assert.match(listed.output, /name ok\n$/);
  const unfinished = run(["--no-sorry", "--name", "unfinished", file]);
  assert.equal(unfinished.status, 1);
  assert.equal(unfinished.error, "");
  assert.match(unfinished.output, /name: unfinished\nilk: one\nsorry: sorry:/);
  assert.match(unfinished.output, /name error: unfinished proof: sorry\n$/);
  fs.writeFileSync(
    path.join(directory, "tung.yaml"),
    "dependencies: {}\nproof:\n  orsettings: []\n",
  );
  assert.equal(run(["--name", "dependent", file]).status, 1);
  assert.equal(
    run(["--allow-orset", "assumed", "--name", "dependent", file]).status,
    0,
  );
});
