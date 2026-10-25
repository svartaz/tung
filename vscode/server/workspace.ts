// workspace-wide index over document models. models take their syntax, and
// navigation its names, from the compiler: `ready` fetcheth what is missing
// before a request, and text and file changes invalidate models and caches.
// a written name resolveth as checking resolved it, else to a local binder
// in scope, else through the module's visible names; nothing is guessed.
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import {
  analyzeDocument,
  findDefinition,
  nameRange,
  roleLabel,
  smallestRegion,
  tokenAtPosition,
} from "./analysis.ts";
import {
  emptyNames,
  emptySyntax,
  type SourceNames,
  type SourceSyntax,
} from "./checker.ts";
import { languageNames } from "./syntax.ts";
type DocumentModel = ReturnType<typeof analyzeDocument>;
type DocumentSnapshot = {
  text: string;
  version: number;
  request?: ReturnType<SyntaxSource["highlight"]>;
  syntax?: SourceSyntax;
  namesRequest?: { result: Promise<SourceNames | undefined>; cancel(): void };
  names?: SourceNames;
  model?: DocumentModel;
};
type SyntaxSource = {
  highlight(
    source: string,
    version: number,
  ): {
    result: Promise<SourceSyntax | undefined>;
    cancel(): void;
  };
  names?(
    model: { uri: string; text: string },
    texts: [string, string][],
    version: number,
  ): { result: Promise<SourceNames | undefined>; cancel(): void };
};
type DocumentLike = { uri: string; version?: number; getText(): string };
type DocumentStore = {
  get(uri: string): DocumentLike | undefined;
  all(): DocumentLike[];
};
const skippedDirectories = new Set([
  ".git",
  ".tung",
  "dist-newstyle",
  "node_modules",
]);
class WorkspaceIndex {
  roots: string[] = [];
  libraryRoots: string[] = [];
  // navigation and colouring share one versioned compiler snapshot per uri.
  cache = new Map<string, DocumentSnapshot>();
  fileUris: string[] = [];
  filesDirty = true;
  modelsCache: DocumentModel[] | undefined = undefined;
  // each known file's real path, as the compiler nameth it, to its uri.
  realUris: Map<string, string> | undefined = undefined;
  constructor(
    public documents: DocumentStore,
    public compiler?: SyntaxSource,
  ) {}
  configure(roots: string[], libraryRoots: string[] = []) {
    this.roots = [
      ...new Set(roots.filter(Boolean).map((root) => path.resolve(root))),
    ];
    this.libraryRoots = [
      ...new Set(
        libraryRoots.filter(Boolean).map((root) => path.resolve(root)),
      ),
    ];
    this.invalidateFiles();
  }
  // a changed document maketh stale the names of every document that
  // bringeth it.
  invalidate(uri) {
    this.snapshot(uri, this.documents.get(uri)?.getText());
    const file = realPath(toFilePath(uri));
    for (const entry of this.cache.values()) {
      if (file && Object.values(entry.names?.files ?? {}).includes(file))
        forgetNames(entry);
    }
    this.invalidateDerived();
  }
  // a file appearing or vanishing may change where any bring resolveth.
  invalidateFiles() {
    this.filesDirty = true;
    this.realUris = undefined;
    for (const entry of this.cache.values()) forgetNames(entry);
    this.invalidateDerived();
  }
  invalidateDerived() {
    this.modelsCache = undefined;
  }
  async syntax(
    uri: string,
    text: string | undefined,
    version = this.versionOf(uri),
  ): Promise<SourceSyntax> {
    const entry = this.snapshot(uri, text, version);
    if (!this.compiler || !entry) return emptySyntax;
    entry.request ||= this.compiler.highlight(entry.text, entry.version);
    if (entry.syntax) return entry.syntax;
    const syntax = await entry.request.result;
    if (this.cache.get(uri) !== entry) return emptySyntax;
    if (!entry.syntax) {
      entry.syntax = syntax || emptySyntax;
      entry.model = undefined;
      this.invalidateDerived();
    }
    return entry.syntax;
  }
  // the compiler resolveth the document's brings, reading open documents'
  // unsaved texts.
  async names(uri: string): Promise<SourceNames> {
    const model = this.model(uri);
    const entry = this.cache.get(uri);
    if (!this.compiler?.names || !model || !entry) return emptyNames;
    entry.namesRequest ||= this.compiler.names(
      model,
      this.openTexts(),
      entry.version,
    );
    if (entry.names) return entry.names;
    const names = await entry.namesRequest.result;
    if (this.cache.get(uri) !== entry) return emptyNames;
    entry.names ||= names || emptyNames;
    return entry.names;
  }
  namesOf(uri: string) {
    return this.cache.get(uri)?.names ?? emptyNames;
  }
  // the unsaved text of each open file document, by path.
  openTexts(): [string, string][] {
    return this.documents.all().flatMap((document) => {
      const file = toFilePath(document.uri);
      return file ? [[file, document.getText()] as [string, string]] : [];
    });
  }
  // the texts of every module a document reacheth, as its names resolved
  // them; a change to one supersedeth a result that read it.
  reachedTexts(uri: string) {
    return Object.entries(this.namesOf(uri).files).map(([importPath, file]) => [
      importPath,
      this.textOf(this.fileUri(file)),
    ]);
  }
  // a file the compiler named, as the uri the workspace knoweth it by.
  fileUri(file: string) {
    if (!this.realUris) {
      this.realUris = new Map();
      for (const uri of this.knownUris()) {
        const real = realPath(toFilePath(uri));
        if (real) this.realUris.set(real, uri);
      }
    }
    return this.realUris.get(file) ?? pathToFileURL(file).href;
  }
  clearSyntax() {
    for (const entry of this.cache.values()) {
      entry.request?.cancel();
      entry.namesRequest?.cancel();
    }
    this.cache.clear();
    this.invalidateDerived();
  }
  versionOf(uri: string) {
    return this.documents.get(uri)?.version || 0;
  }
  snapshot(
    uri: string,
    text: string | undefined,
    version = this.versionOf(uri),
  ) {
    const previous = this.cache.get(uri);
    if (previous?.text === text && previous?.version === version)
      return previous;
    previous?.request?.cancel();
    previous?.namesRequest?.cancel();
    if (text === undefined) {
      this.cache.delete(uri);
      return undefined;
    }
    const entry: DocumentSnapshot = { text, version };
    this.cache.set(uri, entry);
    return entry;
  }
  // syntax for every known document, and names for the open ones, or for
  // every document when a request searcheth them all.
  async ready(everywhere = false) {
    if (!this.compiler) return;
    await Promise.all(
      this.knownUris().map((uri) => this.syntax(uri, this.textOf(uri))),
    );
    const uris = everywhere
      ? this.knownUris()
      : this.documents.all().map(({ uri }) => uri);
    await Promise.all(uris.map((uri) => this.names(uri)));
  }
  knownUris() {
    const uris = new Set(this.workspaceFileUris());
    for (const document of this.documents.all()) uris.add(document.uri);
    return [...uris];
  }
  textOf(uri) {
    const open = this.documents.get(uri);
    if (open) return open.getText();
    const file = toFilePath(uri);
    if (!file || !fs.existsSync(file)) return undefined;
    return fs.readFileSync(file, "utf8");
  }
  model(uri) {
    const text = this.textOf(uri);
    return text === undefined ? undefined : this.modelForText(uri, text);
  }
  modelForText(uri, text) {
    const entry = this.snapshot(uri, text)!;
    if (entry.model) return entry.model;
    entry.model = analyzeDocument(text, uri, entry.syntax);
    entry.model.instances.forEach((instance) => (instance.uri = uri));
    this.invalidateDerived();
    return entry.model;
  }
  models() {
    if (this.modelsCache) return this.modelsCache;
    this.modelsCache = this.knownUris()
      .map((uri) => this.model(uri))
      .filter(Boolean);
    return this.modelsCache;
  }
  workspaceFileUris() {
    if (!this.filesDirty) return this.fileUris;
    const roots = new Set([...this.roots, ...this.libraryRoots]);
    const files = [];
    for (const root of roots) collectFiles(root, files);
    this.fileUris = [...new Set(files.map((file) => pathToFileURL(file).href))];
    this.filesDirty = false;
    return this.fileUris;
  }
  // a global as the compiler nameth it: its module is `<root>` for the
  // document itself, `<primitive>`, or a bring path the document reacheth.
  definitionOf(model, module: string, name: string) {
    const bare = name.startsWith("unbuild ") ? name.slice(8) : name;
    if (module === "<primitive>") {
      return languageNames.primitiveTypes.includes(bare)
        ? primitive(bare, "type")
        : undefined;
    }
    const target =
      module === "<root>" ? model : this.importModel(model, module);
    const global = (written) =>
      target?.definitions.find(
        (definition) => !definition.local && definition.bareName === written,
      );
    // a field `type.field` is the named slot of its type's constructor.
    const dot = bare.lastIndexOf(".");
    if (dot > 0) {
      const family = global(bare.slice(0, dot));
      const region =
        family && smallestRegion(target.regions, family.token.offset, "type");
      return (
        region &&
        target.definitions.find(
          (definition) =>
            definition.bareName === bare.slice(dot + 1) &&
            region.startOffset <= definition.token.offset &&
            definition.token.offset <= region.endOffset,
        )
      );
    }
    return global(bare);
  }
  resolveAt(uri, position) {
    const model = this.model(uri);
    const token = model && tokenAtPosition(model, position);
    if (!model || !token || token.kind !== "name") {
      return { model, token, definition: undefined };
    }
    const found = (definition) => ({ model, token, definition });
    const names = this.namesOf(uri);
    const resolved = names.resolved.find(([start]) => start === token.offset);
    if (resolved)
      return found(this.definitionOf(model, resolved[2], resolved[3]));
    if (model.roles.get(token.index)?.type === "property")
      return found(undefined);
    const visible = names.visible.find(([written]) => written === token.text);
    const local = token.text.includes("~")
      ? undefined
      : findDefinition(model, token, token.offset);
    // a pattern binder that nameth a visible constructor is that constructor.
    if (local && !(local.role === "parameter" && visible?.[3])) {
      return found(local);
    }
    return found(visible && this.definitionOf(model, visible[1], visible[2]));
  }
  // every occurrence that resolveth to the definition, in one document or all.
  references(definition, includeDeclaration = true, only?: string) {
    if (!definition) return [];
    const key = definitionKey(definition);
    const locations = [];
    for (const model of this.models()) {
      if (only && model.uri !== only) continue;
      for (const token of model.occurrences) {
        const resolved = this.resolveAt(model.uri, {
          line: token.line,
          character: token.char,
        }).definition;
        if (resolved && definitionKey(resolved) === key) {
          locations.push({ uri: model.uri, range: nameRange(token) });
        }
      }
    }
    // the declaration's own name resolveth to it too; the caller decideth.
    const declared = ({ uri, range }) =>
      uri === definition.uri && sameRange(range, definition.selectionRange);
    if (!includeDeclaration)
      return locations.filter((location) => !declared(location));
    if (!locations.some(declared)) {
      locations.unshift({
        uri: definition.uri,
        range: definition.selectionRange,
      });
    }
    return locations;
  }
  implementations(definition) {
    if (!definition || definition.role !== "class") return [];
    return this.models().flatMap((model) =>
      model.instances
        .filter(({ className }) => className === definition.bareName)
        .map(({ uri, range }) => ({ uri, range })),
    );
  }
  // the module a bring path of a document reacheth, as its names resolved it.
  importModel(model, importPath) {
    const file = model && this.namesOf(model.uri).files[importPath];
    return file ? this.model(this.fileUri(file)) : undefined;
  }
  completions(uri, position) {
    const model = this.model(uri);
    if (!model) return [];
    const token = tokenAtPosition(model, position);
    const offset = token?.offset ?? model.text.length;
    const local = model.definitions.filter(
      ({ scopeStart, scopeEnd }) => scopeStart <= offset && offset <= scopeEnd,
    );
    const visible = this.namesOf(uri).visible.flatMap(
      ([written, module, name]) => {
        const definition = this.definitionOf(model, module, name);
        return definition ? [{ ...definition, completionName: written }] : [];
      },
    );
    return uniqueByKey(
      [...local, ...visible],
      (definition) => definition.completionName || definition.bareName,
    );
  }
  modulePaths(uri) {
    const current = toFilePath(uri);
    const result = new Set<string>();
    for (const model of this.models()) {
      const file = toFilePath(model.uri);
      if (!file || file === current) continue;
      if (current) {
        result.add(normalPath(path.relative(path.dirname(current), file)));
      }
      for (const root of this.libraryRoots) {
        const relative = path.relative(root, file);
        if (
          relative &&
          !relative.startsWith(".." + path.sep) &&
          relative !== ".." &&
          !path.isAbsolute(relative)
        ) {
          result.add(normalPath(relative));
        }
      }
    }
    return [...result]
      .filter(
        (name) => name && (!name.startsWith("../") || name.endsWith(".tung")),
      )
      .sort();
  }
  primitiveCompletions() {
    return languageNames.primitiveTypes.map((name) => primitive(name, "type"));
  }
}
const collectFiles = (root, result) => {
  if (!root || !fs.existsSync(root)) return;
  let entries;
  try {
    entries = fs.readdirSync(root, { withFileTypes: true });
  } catch {
    return;
  }
  for (const entry of entries) {
    if (entry.isDirectory() && skippedDirectories.has(entry.name)) continue;
    const file = path.join(root, entry.name);
    if (entry.isDirectory()) collectFiles(file, result);
    if (entry.isFile() && entry.name.endsWith(".tung")) result.push(file);
  }
};
const primitive = (name, role) => {
  return {
    name,
    bareName: name,
    completionName: name,
    role,
    modifiers: ["defaultLibrary"],
    detail: `built-in ${roleLabel(role)} ${name}`,
    primitive: true,
  };
};
const definitionKey = (definition) => {
  return (
    definition.id ||
    `${definition.uri}:${definition.token?.offset}:${definition.bareName}`
  );
};
const uniqueByKey = (items, keyOf = (item) => item) => {
  const seen = new Set();
  return items.filter((item) => {
    const key = keyOf(item);
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
};
const sameRange = (left, right) => {
  return (
    left.start.line === right.start.line &&
    left.start.character === right.start.character &&
    left.end.line === right.end.line &&
    left.end.character === right.end.character
  );
};
const normalPath = (file) => {
  return file ? path.normalize(file).split(path.sep).join("/") : undefined;
};
const forgetNames = (entry: DocumentSnapshot) => {
  entry.namesRequest?.cancel();
  entry.namesRequest = undefined;
  entry.names = undefined;
};
const realPath = (file) => {
  try {
    return file ? fs.realpathSync(file) : undefined;
  } catch {
    return undefined;
  }
};
const toFilePath = (uri) => {
  try {
    return uri?.startsWith("file:") ? fileURLToPath(uri) : undefined;
  } catch {
    return undefined;
  }
};
export { toFilePath, uniqueByKey, WorkspaceIndex };
