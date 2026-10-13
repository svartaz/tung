// persistent bridge to the authoritative haskell checker; responses carry request versions.
import * as childProcess from "node:child_process";
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath } from "node:url";
interface PendingRequest {
  resolve: (value: CompilerResult) => void;
  command: CompilerCommand;
  version: number;
}
type CompilerCommand =
  | "check"
  | "ilk"
  | "proof"
  | "format"
  | "highlight"
  | "cancel";
interface CompilerDiagnostic {
  kind: "parse" | "ilk" | "goal";
  path?: string;
  start: number;
  end: number;
  message: string;
}
interface ProofDependency {
  symbol: { module: string; name: string };
  name: string;
  ilk: string;
  kind: "sorry" | "orsetting" | "host";
  host?: string;
}
interface ProofResult {
  kind: "proof";
  audit: { name: string; ilk: string; dependencies: ProofDependency[] };
  verified: boolean;
  message: string;
  report: string;
}
type CompilerResult =
  | { kind: "check"; diagnostics: CompilerDiagnostic[] }
  | { kind: "ilk"; ilk: string }
  | ProofResult
  | { kind: "format"; source: string }
  | { kind: "highlight"; roles: SourceRole[] }
  | { kind: "error"; message: string };
interface CompilerResponse {
  protocol: 1;
  id: number;
  version: number;
  result: CompilerResult;
}
type SourceRole = [
  start: number,
  end: number,
  role: string,
  modifiers: string[],
];
class CompilerBridge {
  tongue: string | undefined;
  executablePath: string | undefined;
  libraryRoots: string[] = [];
  executable: string | undefined;
  session: childProcess.ChildProcessWithoutNullStreams | undefined;
  pending = new Map<number, PendingRequest>();
  nextRequestId = 1;
  output = "";
  configure(tongue, libraryRoots: string[] = [], executablePath?: string) {
    const tongueChanged = tongue !== this.tongue;
    const executableChanged = executablePath !== this.executablePath;
    const rootsChanged = libraryRoots.length !== this.libraryRoots.length ||
      libraryRoots.some((root, index) => root !== this.libraryRoots[index]);
    if (tongueChanged || rootsChanged || executableChanged) {
      this.dispose();
      if (tongueChanged || executableChanged) this.executable = undefined;
    }
    this.tongue = tongue;
    this.executablePath = executablePath;
    this.libraryRoots = [...libraryRoots];
  }
  available() {
    return Boolean(this.findExecutable());
  }
  check(model, imports, version = 0) {
    return this.request(
      "check",
      model.text,
      imports,
      "",
      version,
      documentPath(model.uri),
    );
  }
  ilkOf(model, imports, name, version = 0) {
    return this.request(
      "ilk",
      model.text,
      imports,
      name,
      version,
      documentPath(model.uri),
    );
  }
  proof(model, imports, name, version = 0, allowedOrsettings?: string[]) {
    return this.request(
      "proof",
      model.text,
      imports,
      name,
      version,
      documentPath(model.uri),
      allowedOrsettings,
    );
  }
  format(source, version = 0) {
    const request = this.request("format", source, [], "", version);
    return {
      ...request,
      result: request.result.then((result) =>
        result.kind === "format" ? result.source : undefined
      ),
    };
  }
  highlight(source: string, version = 0) {
    const request = this.request("highlight", source, [], "", version);
    return {
      ...request,
      result: request.result.then((result): SourceRole[] | undefined =>
        result.kind === "highlight" ? result.roles : undefined
      ),
    };
  }
  request(
    command: CompilerCommand,
    source,
    imports,
    name,
    version,
    path?: string,
    allowedOrsettings?: string[],
  ) {
    const executable = this.findExecutable();
    if (!executable) {
      return {
        process: undefined,
        requestId: 0,
        version,
        result: Promise.resolve<CompilerResult>({
          kind: "error",
          message: "could not find the tung executable",
        }),
        cancel() {},
      };
    }
    const process = this.ensureSession(executable);
    const requestId = this.nextRequestId++;
    let resolveResult: PendingRequest["resolve"];
    const result = new Promise<CompilerResult>(
      (resolve) => (resolveResult = resolve),
    );
    this.pending.set(requestId, { resolve: resolveResult, command, version });
    process.stdin.write(
      sessionRequest(
        requestId,
        version,
        command,
        name,
        source,
        imports,
        path,
        allowedOrsettings,
      ),
    );
    return {
      process,
      requestId,
      version,
      result,
      cancel: () => this.cancel(requestId, version),
    };
  }
  ensureSession(executable) {
    if (
      this.session &&
      this.session.exitCode === null &&
      !this.session.killed
    ) {
      return this.session;
    }
    const process = childProcess.spawn(executable, ["--editor-session"], {
      cwd: this.tongue,
      env: this.libraryRoots.length
        ? {
          ...globalThis.process.env,
          TUNG_PATH: this.libraryRoots.join(path.delimiter),
        }
        : globalThis.process.env,
      stdio: ["pipe", "pipe", "pipe"],
    });
    this.session = process;
    this.output = "";
    let stderr = "";
    process.stdout.setEncoding("utf8");
    process.stderr.setEncoding("utf8");
    process.stdout.on("data", (chunk) => this.consume(chunk, process));
    process.stderr.on("data", (chunk) => (stderr += chunk));
    process.on("error", (error) => {
      this.failSession(
        process,
        `could not run the haskell checker: ${error.message}`,
      );
    });
    process.on("close", () => {
      const detail = stderr.trim();
      this.failSession(
        process,
        detail
          ? `haskell checker session stopped: ${detail}`
          : "haskell checker session stopped",
      );
    });
    process.stdin.on("error", (error) => {
      this.failSession(
        process,
        `could not write to the checker: ${error.message}`,
      );
    });
    return process;
  }
  consume(chunk: string, process = this.session) {
    if (!process || process !== this.session) return;
    this.output += chunk;
    while (true) {
      const newline = this.output.indexOf("\n");
      if (newline < 0) return;
      const line = this.output.slice(0, newline);
      this.output = this.output.slice(newline + 1);
      let response: unknown;
      try {
        response = JSON.parse(line);
      } catch {
        this.failSession(process, "invalid JSON from the checker");
        return;
      }
      if (!isCompilerResponse(response)) {
        this.failSession(process, "invalid checker response schema");
        return;
      }
      const pending = this.pending.get(response.id);
      if (!pending) continue;
      if (
        pending.version !== response.version ||
        (response.result.kind !== pending.command &&
          response.result.kind !== "error")
      ) {
        this.failSession(process, "checker response did not match its request");
        return;
      }
      this.pending.delete(response.id);
      pending.resolve(response.result);
    }
  }
  cancel(requestId, version) {
    const pending = this.pending.get(requestId);
    if (!pending) return;
    this.pending.delete(requestId);
    pending.resolve({ kind: "error", message: "checker request cancelled" });
    if (this.session?.exitCode === null && !this.session.killed) {
      this.session.stdin.write(
        sessionRequest(requestId, version, "cancel", "", "", []),
      );
    }
  }
  failSession(process, message) {
    if (this.session !== process) return;
    this.reset(message);
    if (process.exitCode === null && !process.killed) process.kill();
  }
  dispose() {
    const process = this.reset("checker request cancelled");
    if (process && process.exitCode === null && !process.killed) process.kill();
  }
  reset(message) {
    const process = this.session;
    this.session = undefined;
    for (const { resolve } of this.pending.values()) {
      resolve({ kind: "error", message });
    }
    this.pending.clear();
    this.output = "";
    return process;
  }
  findExecutable() {
    if (this.executable && fs.existsSync(this.executable)) {
      return this.executable;
    }
    if (this.executablePath) {
      try {
        this.executable = fs.statSync(this.executablePath).isFile()
          ? this.executablePath
          : undefined;
      } catch {
        this.executable = undefined;
      }
      return this.executable;
    }
    this.executable = this.tongue
      ? this.findCabalExecutable() || this.findDistExecutable() || findOnPath()
      : findOnPath();
    return this.executable;
  }
  findCabalExecutable() {
    const result = childProcess.spawnSync("cabal", ["list-bin", "exe:tung"], {
      cwd: this.tongue,
      encoding: "utf8",
    });
    const found = result.status === 0 ? result.stdout.trim() : "";
    return found && fs.existsSync(found) ? found : undefined;
  }
  findDistExecutable() {
    const root = path.join(this.tongue, "dist-newstyle", "build");
    return findFile(
      root,
      (file) => file.endsWith(path.join("x", "tung", "build", "tung", "tung")),
    );
  }
}
const findOnPath = () => {
  const names = process.platform === "win32" ? ["tung.exe", "tung"] : ["tung"];
  for (const directory of (process.env.PATH || "").split(path.delimiter)) {
    if (!directory) continue;
    for (const name of names) {
      const candidate = path.join(directory, name);
      try {
        if (fs.statSync(candidate).isFile()) {
          fs.accessSync(candidate, fs.constants.X_OK);
          return candidate;
        }
      } catch {
        // the next PATH entry may contain the compiler.
      }
    }
  }
  return undefined;
};
const findFile = (root, predicate) => {
  if (!fs.existsSync(root)) return undefined;
  const stack = [root];
  while (stack.length > 0) {
    const current = stack.pop();
    const stat = fs.statSync(current);
    if (stat.isFile() && predicate(current)) return current;
    if (stat.isDirectory()) {
      for (const entry of fs.readdirSync(current)) {
        stack.push(path.join(current, entry));
      }
    }
  }
  return undefined;
};
const isObject = (value: unknown): value is Record<string, unknown> =>
  value !== null && typeof value === "object" && !Array.isArray(value);
const isStrings = (value: unknown): value is string[] =>
  Array.isArray(value) && value.every((item) => typeof item === "string");
const isRange = (start: unknown, end: unknown) =>
  Number.isSafeInteger(start) &&
  Number.isSafeInteger(end) &&
  (start as number) >= 0 &&
  (end as number) >= (start as number);
const isDiagnostic = (value: unknown): value is CompilerDiagnostic =>
  isObject(value) &&
  ["parse", "ilk", "goal"].includes(value.kind as string) &&
  (value.path === undefined || typeof value.path === "string") &&
  isRange(value.start, value.end) &&
  typeof value.message === "string";
const isRole = (value: unknown): value is SourceRole =>
  Array.isArray(value) &&
  value.length === 4 &&
  isRange(value[0], value[1]) &&
  typeof value[2] === "string" &&
  isStrings(value[3]);
const isProofDependency = (value: unknown): value is ProofDependency =>
  isObject(value) &&
  isObject(value.symbol) &&
  typeof value.symbol.module === "string" &&
  typeof value.symbol.name === "string" &&
  typeof value.name === "string" &&
  typeof value.ilk === "string" &&
  ["sorry", "orsetting", "host"].includes(value.kind as string) &&
  (value.kind === "host"
    ? typeof value.host === "string"
    : value.host === undefined);
const isResult = (value: unknown): value is CompilerResult => {
  if (!isObject(value)) return false;
  switch (value.kind) {
    case "check":
      return (
        Array.isArray(value.diagnostics) &&
        value.diagnostics.every(isDiagnostic)
      );
    case "ilk":
      return typeof value.ilk === "string";
    case "proof":
      return (
        isObject(value.audit) &&
        typeof value.audit.name === "string" &&
        typeof value.audit.ilk === "string" &&
        Array.isArray(value.audit.dependencies) &&
        value.audit.dependencies.every(isProofDependency) &&
        typeof value.verified === "boolean" &&
        typeof value.message === "string" &&
        typeof value.report === "string"
      );
    case "format":
      return typeof value.source === "string";
    case "highlight":
      return Array.isArray(value.roles) && value.roles.every(isRole);
    case "error":
      return typeof value.message === "string";
    default:
      return false;
  }
};
const isCompilerResponse = (value: unknown): value is CompilerResponse =>
  isObject(value) &&
  value.protocol === 1 &&
  Number.isSafeInteger(value.id) &&
  (value.id as number) > 0 &&
  Number.isSafeInteger(value.version) &&
  isResult(value.result);
// a file document nameth its path, so the session can reuse the project's
// interface cache.
const documentPath = (uri: string | undefined) => {
  if (!uri?.startsWith("file:")) return undefined;
  try {
    return fileURLToPath(uri);
  } catch {
    return undefined;
  }
};
const sessionRequest = (
  id,
  version,
  command,
  name,
  source,
  imports,
  path?: string,
  allowedOrsettings?: string[],
) =>
  JSON.stringify({
    protocol: 1,
    id,
    version,
    command,
    name,
    source,
    imports: Object.fromEntries(imports),
    ...(path === undefined ? {} : { path }),
    ...(allowedOrsettings === undefined ? {} : { allowedOrsettings }),
  }) + "\n";
export {
  CompilerBridge,
  CompilerDiagnostic,
  CompilerResult,
  ProofResult,
  sessionRequest,
  SourceRole,
};
