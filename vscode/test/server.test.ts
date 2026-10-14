import assert from "node:assert/strict";
import * as childProcess from "node:child_process";
import { once } from "node:events";
import * as fs from "node:fs";
import * as os from "node:os";
import * as path from "node:path";
import test from "node:test";
import { pathToFileURL } from "node:url";
import {
  createMessageConnection,
  StreamMessageReader,
  StreamMessageWriter,
} from "vscode-jsonrpc/node";
// lsp results are deliberately heterogeneous in this integration harness.
// deno-lint-ignore no-explicit-any
type LspTestResult = any;
test("server implementeth the editor workflow over stdio", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-lsp-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const depPath = path.join(root, "dep.tung");
  const mainPath = path.join(root, "main.tung");
  const depText =
    "show ilk tally: * { naught: tally }\nshow ilk truth: * { yea: truth, nay: truth }\nshow ilk parcel: [a:*, *] { wrap: [a, a parcel] }\nshow let sameness:[x: ℤ, ℤ] ≔ x\nshow let answer:ℤ ≔ +42\nshow flock hath_convert:[a:*, *] { let convert:[a, a] }\n";
  const mainText =
    "bring dep.tung\nlet worth:ℤ ≔ answer\nlet rime:tally ≔ naught\nlet ratio:float ≔ 1.5\nlet truth_to_string:[truth, string] ≔ { yea ^ 'yea', nay ^ 'nay' }\nlet shipment:ℤ parcel ≔ +1 wrap\nlet hath_≍:ℤ ≔ +1 sameness # \"unicode 𝟙\\n\"\nlet select:[left: ℤ, middle: ℤ, right: ℤ, ℤ] ≔ middle\nlet picker: [ℤ, ℤ, ℤ, ℤ] ≔ { first, second, third ^ second }\nbizen:ℤ hath_convert { let convert:[x:] ≔ x }\nshow ilk _box: [a:*, *] {\n  box: [a, a _box]\n}\n";
  fs.writeFileSync(depPath, depText);
  fs.writeFileSync(mainPath, mainText);
  const depUri = pathToFileURL(depPath).href;
  const mainUri = pathToFileURL(mainPath).href;
  const server = childProcess.spawn(
    process.execPath,
    [path.join(__dirname, "..", "server", "main.js"), "--stdio"],
    { stdio: ["pipe", "pipe", "pipe"], env: { ...process.env, TUNG_PATH: "" } },
  );
  context.after(() => server.kill());
  let stderr = "";
  server.stderr.on("data", (chunk) => (stderr += chunk));
  const connection = createMessageConnection(
    new StreamMessageReader(server.stdout),
    new StreamMessageWriter(server.stdin),
  );
  const semanticRefresh = requestQueue(
    connection,
    "workspace/semanticTokens/refresh",
  );
  connection.listen();
  const request = (method, params) =>
    connection.sendRequest<LspTestResult>(method, params);
  const initialized = await connection.sendRequest<LspTestResult>(
    "initialize",
    {
      processId: process.pid,
      rootUri: pathToFileURL(root).href,
      workspaceFolders: [{ uri: pathToFileURL(root).href, name: "fixture" }],
      initializationOptions: { executablePath: process.env.TUNG_EXECUTABLE },
      capabilities: { workspace: { semanticTokens: { refreshSupport: true } } },
    },
  );
  const capabilities = initialized.capabilities;
  assert.equal(capabilities.textDocumentSync.change, 2);
  for (const capability of [
    "hoverProvider",
    "definitionProvider",
    "declarationProvider",
    "implementationProvider",
    "referencesProvider",
    "documentSymbolProvider",
    "workspaceSymbolProvider",
    "foldingRangeProvider",
    "documentFormattingProvider",
  ]) {
    assert.equal(capabilities[capability], true, capability);
  }
  assert.equal(capabilities.semanticTokensProvider.full, true);
  assert.equal(capabilities.semanticTokensProvider.range, true);
  connection.sendNotification("initialized", {});
  const cleanDepDiagnostics = nextDiagnostics(connection, depUri);
  connection.sendNotification("textDocument/didOpen", {
    textDocument: {
      uri: depUri,
      languageId: "tung",
      version: 1,
      text: depText,
    },
  });
  assert.deepEqual((await cleanDepDiagnostics).diagnostics, []);
  const cleanDiagnostics = nextDiagnostics(connection, mainUri);
  connection.sendNotification("textDocument/didOpen", {
    textDocument: {
      uri: mainUri,
      languageId: "tung",
      version: 1,
      text: mainText,
    },
  });
  assert.deepEqual((await cleanDiagnostics).diagnostics, []);
  const proof = await request("tung/checkProof", {
    textDocument: { uri: mainUri },
    position: positionOf(mainText, "answer"),
    allowedOrsettings: [],
  });
  assert.equal(proof.kind, "proof");
  assert.equal(proof.audit.name, "worth");
  assert.equal(proof.verified, true);
  assert.match(proof.report, /name: worth\nilk: ℤ/);
  const selectedProof = await request("tung/checkProof", {
    textDocument: { uri: mainUri },
    name: "answer",
    allowedOrsettings: [],
  });
  assert.equal(selectedProof.audit.name, "answer");
  assert.equal(selectedProof.verified, true);
  const staleDiskGuard = nextDiagnostics(
    connection,
    mainUri,
    ({ diagnostics }) => diagnostics.length > 0,
  );
  const changedHighlight = semanticRefresh.next();
  connection.sendNotification("textDocument/didChange", {
    textDocument: { uri: depUri, version: 2 },
    contentChanges: [
      {
        text: depText.replace("answer:ℤ ≔ +42", "answer:string ≔ 'changed'"),
      },
    ],
  });
  await changedHighlight;
  assert.match((await staleDiskGuard).diagnostics[0].message, /^ilk error:/);
  const restoredImport = nextDiagnostics(
    connection,
    mainUri,
    ({ diagnostics }) => diagnostics.length === 0,
  );
  const restoredHighlight = semanticRefresh.next();
  connection.sendNotification("textDocument/didChange", {
    textDocument: { uri: depUri, version: 3 },
    contentChanges: [{ text: depText }],
  });
  await restoredHighlight;
  assert.deepEqual((await restoredImport).diagnostics, []);
  connection.sendNotification("textDocument/didSave", {
    textDocument: { uri: depUri },
    text: depText,
  });
  const semantic = await request("textDocument/semanticTokens/full", {
    textDocument: { uri: mainUri },
  });
  assert(semantic.data.length > 0);
  const semanticAt = decodedSemanticTokens(
    semantic.data,
    capabilities.semanticTokensProvider.legend.tokenTypes,
  );
  for (const typeName of ["ℤ", "float", "tally", "parcel"]) {
    assert.equal(
      semanticAt.get(positionKey(positionOf(mainText, typeName))),
      "type",
      typeName,
    );
  }
  assert.equal(
    semanticAt.get(positionKey(positionOf(mainText, "sameness"))),
    "call",
  );
  assert.equal(
    semanticAt.get(positionKey(positionOf(mainText, "answer"))),
    undefined,
  );
  for (const name of ["yea", "nay"]) {
    assert.equal(
      semanticAt.get(positionKey(positionOf(mainText, name))),
      "enumMember",
      name,
    );
  }
  assert.notEqual(
    semanticAt.get(positionKey(positionOf(mainText, "tally"))),
    semanticAt.get(positionKey(positionOf(mainText, "sameness"))),
  );
  assert.equal(
    semanticAt.get(positionKey(positionOf(mainText, "convert", 1))),
    "call",
  );
  for (const name of ["left", "middle", "right"]) {
    assert.equal(
      semanticAt.get(positionKey(positionOf(mainText, name))),
      undefined,
      name,
    );
  }
  for (const name of ["first", "second", "third"]) {
    assert.equal(
      semanticAt.get(positionKey(positionOf(mainText, name))),
      "parameter",
      name,
    );
  }
  assert.equal(
    semanticAt.get(positionKey(positionOf(mainText, "middle", 1))),
    undefined,
  );
  assert.equal(
    semanticAt.get(positionKey(positionOf(mainText, "second", 1))),
    undefined,
  );
  for (
    let character = "bring ".length;
    character < "bring dep.tung".length;
    character += 1
  ) {
    assert.equal(semanticAt.has(positionKey({ line: 0, character })), false);
  }
  const rangedSemantic = await request("textDocument/semanticTokens/range", {
    textDocument: { uri: mainUri },
    range: { start: { line: 1, character: 0 }, end: { line: 2, character: 0 } },
  });
  assert(rangedSemantic.data.length > 0);
  const moduleCompletion = await request("textDocument/completion", {
    textDocument: { uri: mainUri },
    position: { line: 0, character: 10 },
  });
  assert(moduleCompletion.some(({ label }) => label === "dep.tung"));
  const answerPosition = positionOf(mainText, "answer");
  const identityPosition = positionOf(mainText, "sameness");
  const completion = await request("textDocument/completion", {
    textDocument: { uri: mainUri },
    position: answerPosition,
  });
  assert(completion.some(({ label }) => label === "answer"));
  assert(completion.some(({ label }) => label === "dep~answer"));
  const definition = await request("textDocument/definition", {
    textDocument: { uri: mainUri },
    position: answerPosition,
  });
  assert.equal(definition.uri, depUri);
  const hover = await request("textDocument/hover", {
    textDocument: { uri: mainUri },
    position: answerPosition,
  });
  assert.match(hover.contents.value, /let answer:ℤ/);
  assert.match(hover.contents.value, /inferred ilk/);
  const references = await request("textDocument/references", {
    textDocument: { uri: mainUri },
    position: answerPosition,
    context: { includeDeclaration: true },
  });
  assert.deepEqual(
    new Set(references.map(({ uri }) => uri)),
    new Set([depUri, mainUri]),
  );
  const rename = await request("textDocument/rename", {
    textDocument: { uri: mainUri },
    position: answerPosition,
    newName: "result",
  });
  assert.equal(rename.changes[depUri][0].newText, "result");
  assert.equal(rename.changes[mainUri][0].newText, "result");
  for (const newName of ["not a name", "*"]) {
    await assert.rejects(
      request("textDocument/rename", {
        textDocument: { uri: mainUri },
        position: answerPosition,
        newName,
      }),
      /invalid tung name/,
    );
  }
  const primitiveRename = await request("textDocument/prepareRename", {
    textDocument: { uri: mainUri },
    position: positionOf(mainText, "ℤ"),
  });
  assert.equal(primitiveRename, null);
  const symbols = await request("textDocument/documentSymbol", {
    textDocument: { uri: mainUri },
  });
  assert(symbols.some(({ name }) => name === "worth"));
  assert(symbols.some(({ name }) => name === "_box"));
  const workspaceSymbols = await request("workspace/symbol", {
    query: "answer",
  });
  assert(workspaceSymbols.some(({ location }) => location.uri === depUri));
  const convertPosition = positionOf(mainText, "convert");
  const implementations = await request("textDocument/implementation", {
    textDocument: { uri: mainUri },
    position: convertPosition,
  });
  assert(implementations.some(({ uri }) => uri === mainUri));
  const links = await request("textDocument/documentLink", {
    textDocument: { uri: mainUri },
  });
  assert.deepEqual(
    links.map(({ target }) => target),
    [depUri],
  );
  const folds = await request("textDocument/foldingRange", {
    textDocument: { uri: mainUri },
  });
  assert(
    folds.some(
      ({ startLine }) => startLine === positionOf(mainText, "show").line,
    ),
  );
  const selections = await request("textDocument/selectionRange", {
    textDocument: { uri: mainUri },
    positions: [positionOf(mainText, "box", 1)],
  });
  assert(selections[0].parent);
  const signature = await request("textDocument/signatureHelp", {
    textDocument: { uri: mainUri },
    position: {
      line: identityPosition.line,
      character: identityPosition.character + "sameness".length,
    },
  });
  assert.match(signature.signatures[0].label, /sameness/);
  const formatted = await request("textDocument/formatting", {
    textDocument: { uri: mainUri },
    options: { tabSize: 2, insertSpaces: true },
  });
  assert.match(
    formatted[0].newText,
    /show ilk _box: \[a: \*, \*\] \{ box: \[a, a _box\] \}/,
  );
  assert.equal(
    capabilities.documentRangeFormattingProvider,
    undefined,
    "a canonical neat form hath no range of its own",
  );
  connection.sendNotification("textDocument/didClose", {
    textDocument: { uri: depUri },
  });
  const importedSource = depText.replace(
    "answer:ℤ ≔ +42",
    "answer:ℤ ≔ 'wrong'",
  );
  const importedDiagnostics = nextDiagnostics(
    connection,
    depUri,
    ({ diagnostics }) => diagnostics.length > 0,
  );
  fs.writeFileSync(depPath, importedSource);
  connection.sendNotification("workspace/didChangeWatchedFiles", {
    changes: [{ uri: depUri, type: 2 }],
  });
  const importedResult = await importedDiagnostics;
  assert.match(importedResult.diagnostics[0].message, /^ilk error:/);
  assert.deepEqual(
    importedResult.diagnostics[0].range.start,
    positionOf(importedSource, "'wrong'"),
  );
  const clearedImportedDiagnostics = nextDiagnostics(
    connection,
    depUri,
    ({ diagnostics }) => diagnostics.length === 0,
  );
  fs.writeFileSync(depPath, depText);
  connection.sendNotification("workspace/didChangeWatchedFiles", {
    changes: [{ uri: depUri, type: 2 }],
  });
  assert.deepEqual((await clearedImportedDiagnostics).diagnostics, []);
  const badDiagnostics = nextDiagnostics(
    connection,
    mainUri,
    ({ diagnostics }) => diagnostics.length > 0,
  );
  const badText = mainText.replace(
    "let worth:ℤ ≔ answer",
    "let worth:string ≔ answer",
  );
  connection.sendNotification("textDocument/didChange", {
    textDocument: { uri: mainUri, version: 2 },
    contentChanges: [{ text: badText }],
  });
  const badResult = await badDiagnostics;
  assert.match(badResult.diagnostics[0].message, /^ilk error:/);
  assert.deepEqual(
    badResult.diagnostics[0].range.start,
    positionOf(badText, "answer"),
  );
  const completeUse = "bring dep.tung";
  const useDiagnostics = nextDiagnostics(
    connection,
    mainUri,
    ({ diagnostics }) => diagnostics.length === 0,
  );
  connection.sendNotification("textDocument/didChange", {
    textDocument: { uri: mainUri, version: 3 },
    contentChanges: [{ text: completeUse }],
  });
  assert.deepEqual((await useDiagnostics).diagnostics, []);
  const holeText = "let twice:[x:ℤ, ℤ] ≔ sorry";
  const holeDiagnostics = nextDiagnostics(
    connection,
    mainUri,
    ({ diagnostics }) => diagnostics.length > 0,
  );
  connection.sendNotification("textDocument/didChange", {
    textDocument: { uri: mainUri, version: 4 },
    contentChanges: [{ text: holeText }],
  });
  const [goal] = (await holeDiagnostics).diagnostics;
  assert.equal(goal.severity, 3);
  assert.equal(goal.message, "goal: ℤ\n  x: ℤ");
  assert.deepEqual(goal.range.start, positionOf(holeText, "sorry"));
  const goalHover = await request("textDocument/hover", {
    textDocument: { uri: mainUri },
    position: positionOf(holeText, "sorry"),
  });
  assert.match(goalHover.contents.value, /goal: ℤ\n {2}x: ℤ/);
  const unfinishedProof = await request("tung/checkProof", {
    textDocument: { uri: mainUri },
    position: positionOf(holeText, "sorry"),
  });
  assert.equal(unfinishedProof.kind, "proof");
  assert.equal(unfinishedProof.audit.name, "twice");
  assert.equal(unfinishedProof.verified, false);
  assert.match(unfinishedProof.report, /unfinished proof: sorry/);
  let version = 4;
  for (const [kind, text] of [
    ["ilk", `let broken:ℤ ≔ 'wrong'\n${holeText}`],
    ["parse", `${holeText}\nlet broken:ℤ ≔`],
  ]) {
    const recoveredDiagnostics = nextDiagnostics(
      connection,
      mainUri,
      ({ diagnostics }) => diagnostics.length === 2,
    );
    connection.sendNotification("textDocument/didChange", {
      textDocument: { uri: mainUri, version: ++version },
      contentChanges: [{ text }],
    });
    const [error, recoveredGoal] = (await recoveredDiagnostics).diagnostics;
    assert.equal(error.severity, 1);
    assert.match(error.message, new RegExp(`^${kind} error:`));
    assert.equal(recoveredGoal.severity, 3);
    assert.equal(recoveredGoal.message, goal.message);
    assert.deepEqual(recoveredGoal.range.start, positionOf(text, "sorry"));
    const recoveredHover = await request("textDocument/hover", {
      textDocument: { uri: mainUri },
      position: positionOf(text, "sorry"),
    });
    assert.match(recoveredHover.contents.value, /goal: ℤ\n {2}x: ℤ/);
    const rejectedProof = await request("tung/checkProof", {
      textDocument: { uri: mainUri },
      name: "twice",
    });
    assert.equal(rejectedProof.kind, "error");
  }
  const importedGoalText = `bring dep.tung\n${holeText}`;
  const importErrorWithGoal = nextDiagnostics(
    connection,
    depUri,
    ({ diagnostics }) => diagnostics.some(({ severity }) => severity === 1),
  );
  const rootGoalWithImportError = nextDiagnostics(
    connection,
    mainUri,
    ({ diagnostics }) =>
      diagnostics.length === 1 && diagnostics[0].severity === 3,
  );
  fs.writeFileSync(depPath, importedSource);
  connection.sendNotification("workspace/didChangeWatchedFiles", {
    changes: [{ uri: depUri, type: 2 }],
  });
  connection.sendNotification("textDocument/didChange", {
    textDocument: { uri: mainUri, version: ++version },
    contentChanges: [{ text: importedGoalText }],
  });
  assert.deepEqual(
    (await importErrorWithGoal).diagnostics[0].range.start,
    positionOf(importedSource, "'wrong'"),
  );
  const [importIndependentGoal] = (await rootGoalWithImportError).diagnostics;
  assert.equal(importIndependentGoal.message, goal.message);
  assert.deepEqual(
    importIndependentGoal.range.start,
    positionOf(importedGoalText, "sorry"),
  );
  const clearedRootGoals = nextDiagnostics(
    connection,
    mainUri,
    ({ diagnostics }) => diagnostics.length === 0,
  );
  const clearedImportError = nextDiagnostics(
    connection,
    depUri,
    ({ diagnostics }) => diagnostics.length === 0,
  );
  connection.sendNotification("textDocument/didClose", {
    textDocument: { uri: mainUri },
  });
  await Promise.all([clearedRootGoals, clearedImportError]);
  await connection.sendRequest("shutdown");
  connection.sendNotification("exit");
  await once(server, "exit");
  connection.dispose();
  assert.equal(stderr, "");
});
test(
  "proof reports are discarded when an unsaved import changeth during checking",
  { timeout: 10000 },
  async (context) => {
    const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-proof-lsp-"));
    context.after(() => fs.rmSync(root, { recursive: true, force: true }));
    const marker = path.join(root, "started");
    const release = path.join(root, "release");
    const executable = path.join(root, "tung");
    fs.writeFileSync(
      executable,
      `#!${process.execPath}
if (process.argv.includes("--library-paths")) process.exit(0);
const fs = require("node:fs");
require("node:readline").createInterface({input:process.stdin}).on("line", line => {
  const request = JSON.parse(line);
  const reply = result => process.stdout.write(JSON.stringify({protocol:1,id:request.id,version:request.version,result}) + "\\n");
  if (request.command === "highlight") reply({kind:"highlight",roles:[]});
  if (request.command === "check") reply({kind:"check",diagnostics:[]});
  if (request.command === "proof") {
    fs.writeFileSync(${JSON.stringify(marker)}, "");
    const timer = setInterval(() => {
      if (!fs.existsSync(${JSON.stringify(release)})) return;
      clearInterval(timer);
      reply({kind:"proof",audit:{name:"proved",ilk:"ℤ",dependencies:[]},verified:true,message:"name ok",report:"name ok\\n"});
    }, 5);
  }
});
`,
    );
    fs.chmodSync(executable, 0o755);
    const server = childProcess.spawn(
      process.execPath,
      [path.join(__dirname, "..", "server", "main.js"), "--stdio"],
      { stdio: ["pipe", "pipe", "pipe"] },
    );
    context.after(() => server.kill());
    const connection = createMessageConnection(
      new StreamMessageReader(server.stdout),
      new StreamMessageWriter(server.stdin),
    );
    context.after(() => connection.dispose());
    connection.listen();
    const uri = pathToFileURL(path.join(root, "main.tung")).href;
    const depUri = pathToFileURL(path.join(root, "dep.tung")).href;
    fs.writeFileSync(path.join(root, "dep.tung"), "show let exported:ℤ ≔ +1");
    await connection.sendRequest("initialize", {
      processId: process.pid,
      rootUri: pathToFileURL(root).href,
      capabilities: {},
      initializationOptions: { executablePath: executable },
    });
    connection.sendNotification("initialized", {});
    for (const [documentUri, text] of [
      [depUri, "show let exported:ℤ ≔ +1"],
      [uri, "bring dep.tung\nlet proved:ℤ ≔ exported"],
    ]) {
      connection.sendNotification("textDocument/didOpen", {
        textDocument: {
          uri: documentUri,
          languageId: "tung",
          version: 1,
          text,
        },
      });
    }
    const watcher = fs.watch(root);
    context.after(() => watcher.close());
    const started = once(watcher, "change");
    const proof = connection.sendRequest<LspTestResult>("tung/checkProof", {
      textDocument: { uri },
      name: "proved",
    });
    await started;
    assert.equal(fs.existsSync(marker), true);
    connection.sendNotification("textDocument/didChange", {
      textDocument: { uri: depUri, version: 2 },
      contentChanges: [{ text: "show let exported:ℤ ≔ +2" }],
    });
    await connection.sendRequest("textDocument/documentSymbol", {
      textDocument: { uri: depUri },
    });
    fs.writeFileSync(release, "");
    assert.deepEqual(await proof, {
      kind: "error",
      message: "the proof source or its imports changed; check the proof again",
    });
    await connection.sendRequest("shutdown");
    connection.sendNotification("exit");
    await once(server, "exit");
  },
);

test("server resolveth a nested forthcast's git-pinned library", async (context) => {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), "tung-lsp-library-"));
  context.after(() => fs.rmSync(root, { recursive: true, force: true }));
  const repository = path.join(root, "library");
  const project = path.join(root, "forthcast");
  fs.mkdirSync(repository);
  fs.mkdirSync(project);
  fs.writeFileSync(
    path.join(repository, "worth.tung"),
    "show let worth:ℤ ≔ +42",
  );
  const git = (...args: string[]) =>
    childProcess.execFileSync("git", args, { encoding: "utf8" }).trim();
  git("init", "--quiet", repository);
  git("-C", repository, "config", "user.name", "Tung Test");
  git("-C", repository, "config", "user.email", "tung-test@example.invalid");
  git("-C", repository, "add", ".");
  git(
    "-C",
    repository,
    "-c",
    "commit.gpgsign=false",
    "commit",
    "--quiet",
    "-m",
    "library",
  );
  const commit = git("-C", repository, "rev-parse", "HEAD");
  fs.writeFileSync(
    path.join(project, "tung.yaml"),
    `dependencies:\n  sample:\n    repo: ../library\n    hash: "${commit}"\n`,
  );
  const mainPath = path.join(project, "main.tung");
  const source = "bring worth.tung let answer:ℤ ≔ worth";
  fs.writeFileSync(mainPath, source);
  const uri = pathToFileURL(mainPath).href;
  const server = childProcess.spawn(
    process.execPath,
    [path.join(__dirname, "..", "server", "main.js"), "--stdio"],
    { stdio: ["pipe", "pipe", "pipe"], env: { ...process.env, TUNG_PATH: "" } },
  );
  context.after(() => server.kill());
  const connection = createMessageConnection(
    new StreamMessageReader(server.stdout),
    new StreamMessageWriter(server.stdin),
  );
  connection.listen();
  await connection.sendRequest("initialize", {
    processId: process.pid,
    rootUri: pathToFileURL(root).href,
    workspaceFolders: [{ uri: pathToFileURL(root).href, name: "fixture" }],
    initializationOptions: { executablePath: process.env.TUNG_EXECUTABLE },
    capabilities: {},
  });
  connection.sendNotification("initialized", {});
  const diagnostics = nextDiagnostics(connection, uri);
  connection.sendNotification("textDocument/didOpen", {
    textDocument: { uri, languageId: "tung", version: 1, text: source },
  });
  assert.deepEqual((await diagnostics).diagnostics, []);
  assert.equal(await connection.sendRequest("tung/libraryPath"), "");
  const definition = await connection.sendRequest<LspTestResult>(
    "textDocument/definition",
    { textDocument: { uri }, position: positionOf(source, "worth", 1) },
  );
  assert.equal(
    definition.uri,
    pathToFileURL(
      fs.realpathSync(
        path.join(
          project,
          ".tung",
          "libraries",
          "sample",
          commit,
          "worth.tung",
        ),
      ),
    ).href,
  );
  await connection.sendRequest("shutdown");
  connection.sendNotification("exit");
  await once(server, "exit");
  connection.dispose();
});
const diagnosticWaiters = new WeakMap<
  object,
  Set<(params: LspTestResult) => void>
>();
const nextDiagnostics = (
  connection,
  uri,
  accept: (params: LspTestResult) => boolean = () => true,
) => {
  let waiters = diagnosticWaiters.get(connection);
  if (!waiters) {
    waiters = new Set();
    diagnosticWaiters.set(connection, waiters);
    connection.onNotification("textDocument/publishDiagnostics", (params) => {
      for (const receive of waiters) receive(params);
    });
  }
  return new Promise<LspTestResult>((resolve, reject) => {
    const timeout = setTimeout(() => {
      waiters.delete(receive);
      reject(new Error(`timed out waiting for diagnostics for ${uri}`));
    }, 30000);
    const receive = (params) => {
      if (params.uri !== uri || !accept(params)) return;
      clearTimeout(timeout);
      waiters.delete(receive);
      resolve(params);
    };
    waiters.add(receive);
  });
};
const requestQueue = (connection, method) => {
  const queued = [];
  const waiting = [];
  connection.onRequest(method, () => {
    const resolve = waiting.shift();
    if (resolve) resolve();
    else queued.push(true);
    return null;
  });
  return {
    next() {
      if (queued.length) {
        queued.shift();
        return Promise.resolve();
      }
      return new Promise<void>((resolve, reject) => {
        const timeout = setTimeout(
          () => reject(new Error(`timed out waiting for ${method}`)),
          30000,
        );
        waiting.push(() => {
          clearTimeout(timeout);
          resolve();
        });
      });
    },
  };
};
const positionOf = (text, needle, occurrence = 0) => {
  let offset = -1;
  for (let found = 0; found <= occurrence; found += 1) {
    offset = text.indexOf(needle, offset + 1);
  }
  assert(offset >= 0, needle);
  const before = text.slice(0, offset).split("\n");
  return { line: before.length - 1, character: before.at(-1).length };
};
const decodedSemanticTokens = (data, tokenTypes) => {
  const result = new Map();
  let line = 0;
  let character = 0;
  for (let index = 0; index < data.length; index += 5) {
    line += data[index];
    character =
      data[index] === 0 ? character + data[index + 1] : data[index + 1];
    result.set(`${line}:${character}`, tokenTypes[data[index + 3]]);
  }
  return result;
};
const positionKey = ({ line, character }) => {
  return `${line}:${character}`;
};
