// workspace-wide import and visibility index over document models. models
// take their roles from the compiler: `ready` fetcheth missing roles before a
// request, and text and file changes invalidate models and derived caches.
import * as fs from "node:fs";
import * as path from "node:path";
import { fileURLToPath, pathToFileURL } from "node:url";
import {
  analyzeDocument,
  findDefinition,
  nameRange,
  tokenAtPosition,
} from "./analysis.ts";
import type { SourceRole } from "./checker.ts";
import { languageNames } from "./syntax.ts";
type DocumentModel = ReturnType<typeof analyzeDocument>;
type DocumentSnapshot = {
  text: string;
  version: number;
  request?: ReturnType<RoleSource["highlight"]>;
  roles?: SourceRole[];
  model?: DocumentModel;
};
type RoleSource = {
  highlight(
    source: string,
    version: number,
  ): {
    result: Promise<SourceRole[] | undefined>;
    cancel(): void;
  };
};
type DocumentLike = { uri: string; version?: number; getText(): string };
type DocumentStore = {
  get(uri: string): DocumentLike | undefined;
  all(): DocumentLike[];
};
type Definition = DocumentModel["definitions"][number];
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
  resolveImportCache = new Map<string, DocumentModel | undefined>();
  publicDefinitionsCache = new Map<string, Definition[]>();
  constructor(
    public documents: DocumentStore,
    public compiler?: RoleSource,
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
  invalidate(uri) {
    this.snapshot(uri, this.documents.get(uri)?.getText());
    this.invalidateDerived();
  }
  invalidateFiles() {
    this.filesDirty = true;
    this.invalidateDerived();
  }
  invalidateDerived() {
    this.modelsCache = undefined;
    this.resolveImportCache.clear();
    this.publicDefinitionsCache.clear();
  }
  async roles(
    uri: string,
    text: string | undefined,
    version = this.versionOf(uri),
  ): Promise<SourceRole[]> {
    const entry = this.snapshot(uri, text, version);
    if (!this.compiler || !entry) return [];
    entry.request ||= this.compiler.highlight(entry.text, entry.version);
    if (entry.roles) return entry.roles;
    const roles = await entry.request.result;
    if (this.cache.get(uri) !== entry) return [];
    if (!entry.roles) {
      entry.roles = roles || [];
      entry.model = undefined;
      this.invalidateDerived();
    }
    return entry.roles;
  }
  clearRoles() {
    for (const entry of this.cache.values()) entry.request?.cancel();
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
    if (text === undefined) {
      this.cache.delete(uri);
      return undefined;
    }
    const entry: DocumentSnapshot = { text, version };
    this.cache.set(uri, entry);
    return entry;
  }
  async ready() {
    if (!this.compiler) return;
    await Promise.all(
      this.knownUris().map((uri) => this.roles(uri, this.textOf(uri))),
    );
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
    entry.model = analyzeDocument(text, uri, entry.roles || []);
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
  resolveImport(model, imported) {
    const cacheKey = `${model?.uri || ""}\0${imported.path}`;
    if (this.resolveImportCache.has(cacheKey)) {
      return this.resolveImportCache.get(cacheKey);
    }
    const models = this.models();
    const byPath = new Map(
      models.map((candidate) => [
        normalPath(toFilePath(candidate.uri)),
        candidate,
      ]),
    );
    const from = toFilePath(model.uri);
    if (from) {
      const candidate = path.resolve(path.dirname(from), imported.path);
      const found = byPath.get(normalPath(candidate));
      if (found) return this.cacheResolvedImport(cacheKey, found);
    }
    const libraryMatches = this.libraryRoots
      .map((root) => byPath.get(normalPath(path.resolve(root, imported.path))))
      .filter(Boolean);
    return this.cacheResolvedImport(
      cacheKey,
      libraryMatches.length === 1 ? libraryMatches[0] : undefined,
    );
  }
  cacheResolvedImport(key, model) {
    this.resolveImportCache.set(key, model);
    return model;
  }
  importDefinitions(model, imported, seen = new Set()) {
    return this.publicDefinitions(this.resolveImport(model, imported), seen);
  }
  // public definitions follow shown declarations, shown imports, and explicit
  // re-exports while the seen set preventeth import cycles.
  publicDefinitions(model, seen = new Set()) {
    if (!model || seen.has(model.uri)) return [];
    if (seen.size === 0 && this.publicDefinitionsCache.has(model.uri)) {
      return this.publicDefinitionsCache.get(model.uri);
    }
    const nextSeen = new Set(seen).add(model.uri);
    const own = model.definitions.filter(({ exported }) => exported);
    const shownImports = model.imports
      .filter(({ exported }) => exported)
      .flatMap((imported) => this.importDefinitions(model, imported, nextSeen));
    // `show name` re-exporteth every visible role with that name.
    const reexported = model.reexports.flatMap(({ name }) =>
      this.resolveVisible(model, name, nextSeen),
    );
    const definitions = uniqueByKey(
      [...own, ...shownImports, ...reexported],
      definitionKey,
    );
    if (seen.size === 0) {
      this.publicDefinitionsCache.set(model.uri, definitions);
    }
    return definitions;
  }
  resolveVisible(model, name, seen = new Set(), role = undefined) {
    const visibleRole = (definition) => !role || definition.role === role;
    const split = name.indexOf("~");
    if (split >= 0) {
      const qualifier = name.slice(0, split);
      const bare = name.slice(split + 1);
      const imported = model.imports.find(
        ({ namespace }) => namespace === qualifier,
      );
      if (imported) {
        return this.importDefinitions(model, imported, seen).filter(
          (definition) =>
            definition.bareName === bare && visibleRole(definition),
        );
      }
      return model.definitions
        .filter(
          ({ bareName, containerName }) =>
            bareName === bare && containerName === qualifier,
        )
        .filter(visibleRole);
    }
    const own = model.definitions.filter(
      (definition) =>
        !definition.local &&
        definition.bareName === name &&
        visibleRole(definition),
    );
    if (own.length) return own;
    return uniqueByKey(
      model.imports.flatMap((imported) =>
        this.importDefinitions(model, imported, seen).filter(
          (definition) =>
            definition.bareName === name && visibleRole(definition),
        ),
      ),
      definitionKey,
    );
  }
  resolveAt(uri, position) {
    const model = this.model(uri);
    const token = model && tokenAtPosition(model, position);
    if (!model || !token || token.kind !== "name") {
      return { model, token, definition: undefined };
    }
    if (
      model.instances.some((instance) => instance.token.offset === token.offset)
    ) {
      const visibleClasses = this.resolveVisibleRole(
        model,
        token.text,
        "class",
      );
      return {
        model,
        token,
        definition: visibleClasses.length === 1 ? visibleClasses[0] : undefined,
        candidates: visibleClasses,
      };
    }
    if (model.roles.get(token.index)?.type === "property") {
      return { model, token, definition: undefined };
    }
    const local = findDefinition(model, token, token.offset);
    if (local?.role === "parameter" && !token.text.includes("~")) {
      const constructors = this.resolveVisibleRole(
        model,
        token.text,
        "enumMember",
      );
      if (constructors.length === 1) {
        return {
          model,
          token,
          definition: constructors[0],
          candidates: constructors,
        };
      }
    }
    if (local && !token.text.includes("~")) {
      return { model, token, definition: local };
    }
    const visible = this.resolveVisible(model, token.text);
    // a name in type position without a local binder nameth a visible type.
    const tokenRole = model.roles.get(token.index)?.type;
    const role = tokenRole === "typeParameter" ? "type" : tokenRole;
    const matching = role
      ? visible.filter((definition) => definition.role === role)
      : visible;
    const candidates = matching.length ? matching : visible;
    return {
      model,
      token,
      definition: candidates.length === 1 ? candidates[0] : local,
      candidates,
    };
  }
  resolveVisibleRole(model, name, role) {
    return this.resolveVisible(model, name, new Set(), role);
  }
  references(definition, includeDeclaration = true) {
    if (!definition) return [];
    const key = definitionKey(definition);
    const locations = [];
    for (const model of this.models()) {
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
    if (
      includeDeclaration &&
      !locations.some(
        ({ uri, range }) =>
          uri === definition.uri && sameRange(range, definition.selectionRange),
      )
    ) {
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
  importSources(model, seen = new Set()) {
    if (!model || seen.has(model.uri)) return [];
    const nextSeen = new Set(seen).add(model.uri);
    const imports = [];
    for (const imported of model.imports) {
      const target = this.resolveImport(model, imported);
      if (!target) continue;
      imports.push([imported.path, target.text]);
      imports.push(...this.importSources(target, nextSeen));
    }
    return uniqueByKey(imports, ([importPath]) => importPath);
  }
  importModel(model, importPath, seen = new Set()) {
    if (!model || seen.has(model.uri)) return undefined;
    const nextSeen = new Set(seen).add(model.uri);
    for (const imported of model.imports) {
      const target = this.resolveImport(model, imported);
      if (!target) continue;
      if (imported.path === importPath) return target;
      const nested = this.importModel(target, importPath, nextSeen);
      if (nested) return nested;
    }
    return undefined;
  }
  completions(uri, position) {
    const model = this.model(uri);
    if (!model) return [];
    const token = tokenAtPosition(model, position);
    const offset = token?.offset ?? model.text.length;
    const local = model.definitions.filter(
      ({ scopeStart, scopeEnd }) => scopeStart <= offset && offset <= scopeEnd,
    );
    const imported = model.imports.flatMap((entry) => {
      const definitions = this.importDefinitions(model, entry);
      return definitions.flatMap((definition) => [
        definition,
        {
          ...definition,
          completionName: `${entry.namespace}~${definition.bareName}`,
        },
      ]);
    });
    return uniqueByKey(
      [...local, ...imported],
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
    detail: `built-in ${role} ${name}`,
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
const toFilePath = (uri) => {
  try {
    return uri?.startsWith("file:") ? fileURLToPath(uri) : undefined;
  } catch {
    return undefined;
  }
};
export { toFilePath, uniqueByKey, WorkspaceIndex };
