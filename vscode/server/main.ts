// lsp transport and request orchestration. tolerant workspace models serve
// editor features; the compiler bridge alone supplieth authoritative diagnostics.
import * as fs from "node:fs";
import * as path from "node:path";
import {
  CompletionItemKind,
  createConnection,
  type Diagnostic,
  DiagnosticSeverity,
  DidChangeWatchedFilesNotification,
  DocumentHighlightKind,
  InsertTextFormat,
  MarkupKind,
  ProposedFeatures,
  SemanticTokensBuilder,
  SymbolKind,
  TextDocuments,
  TextDocumentSyncKind,
} from "vscode-languageserver/node";
import { TextDocument } from "vscode-languageserver-textdocument";
import {
  keywordHelp,
  roleLabel,
  nameRange,
  smallestRegion,
  tokenAtPosition,
  tokenRange,
} from "./analysis.ts";
import { CompilerBridge } from "./checker.ts";
import {
  readDeclaredLibraryPaths,
  resolveLibraryPaths,
} from "./library-paths.ts";
import { languageNames } from "./syntax.ts";
import { toFilePath, uniqueByKey, WorkspaceIndex } from "./workspace.ts";
import {
  buildHighlightRanges,
  tokenModifiers,
  tokenTypes,
} from "./highlight.ts";
const connection = createConnection(ProposedFeatures.all);
const documents = new TextDocuments(TextDocument);
const compiler = new CompilerBridge();
const workspace = new WorkspaceIndex(documents, compiler);
// navigation readeth models built from compiler roles; missing roles are
// fetched before the request is answered.
const navigation =
  <Arguments extends unknown[], Result>(
    handler: (...parameters: Arguments) => Result,
  ) =>
  async (...parameters: Arguments): Promise<Awaited<Result>> => {
    await workspace.ready();
    return await handler(...parameters);
  };
const timers = new Map();
const checks = new Map();
const diagnosticReports = new Map();
// the goals of the latest successful check, by document.
const goalReports = new Map();
const typeCache = new Map<
  string,
  { promise: Promise<string | undefined>; cancel: () => void }
>();
const defaultCheckDelay = 500;
const dependentCheckDelay = 1000;
const semanticRefreshDelay = 200;
let workspaceRoots = [];
let tongueDir;
let canRegisterWatchedFiles = false;
let canRefreshSemanticTokens = false;
let configuredTongue;
let configuredExecutable;
let configuredLibraryPaths;
let libraryRoots: string[] = [];
let localLibraryRoots: string[] = [];
let libraryResolutionError: string | undefined;
let semanticRefreshTimer;
connection.onInitialize((params) => {
  configuredTongue = params.initializationOptions?.tonguePath;
  configuredExecutable = params.initializationOptions?.executablePath;
  configuredLibraryPaths = params.initializationOptions?.libraryPaths;
  canRegisterWatchedFiles = Boolean(
    params.capabilities?.workspace?.didChangeWatchedFiles?.dynamicRegistration,
  );
  canRefreshSemanticTokens = Boolean(
    params.capabilities?.workspace?.semanticTokens?.refreshSupport,
  );
  workspaceRoots = uniqueByKey(
    [
      ...(params.workspaceFolders || []).map(({ uri }) => toFilePath(uri)),
      toFilePath(params.rootUri),
    ].filter(Boolean),
  );
  configureWorkspace();
  return {
    capabilities: {
      textDocumentSync: {
        openClose: true,
        change: TextDocumentSyncKind.Incremental,
        save: { includeText: true },
      },
      semanticTokensProvider: {
        legend: { tokenTypes, tokenModifiers },
        full: true,
        range: true,
      },
      completionProvider: { triggerCharacters: ["/", "."] },
      hoverProvider: true,
      definitionProvider: true,
      declarationProvider: true,
      typeDefinitionProvider: true,
      implementationProvider: true,
      referencesProvider: true,
      documentHighlightProvider: true,
      documentSymbolProvider: true,
      workspaceSymbolProvider: true,
      renameProvider: { prepareProvider: true },
      foldingRangeProvider: true,
      selectionRangeProvider: true,
      documentLinkProvider: { resolveProvider: false },
      documentFormattingProvider: true,
      signatureHelpProvider: { triggerCharacters: [" ", "$"] },
      workspace: {
        workspaceFolders: {
          supported: true,
          changeNotifications: true,
        },
      },
    },
    serverInfo: { name: "tung-language-server", version: "0.1.0" },
  };
});
connection.onInitialized(() => {
  if (!canRegisterWatchedFiles) return;
  connection.client
    .register(DidChangeWatchedFilesNotification.type, {
      watchers: [{ globPattern: "**/*.tung" }, { globPattern: "**/tung.yaml" }],
    })
    .catch(() => {});
});
connection.onShutdown(() => {
  workspace.clearRoles();
  compiler.dispose();
  return null;
});
connection.onRequest("tung/executable", () => compiler.findExecutable());
connection.onRequest("tung/libraryPath", () =>
  localLibraryRoots.join(path.delimiter),
);
connection.onRequest(
  "tung/checkProof",
  navigation(
    async (
      { textDocument, position, name, allowedOrsettings },
      cancellation,
    ) => {
      if (libraryResolutionError)
        return {
          kind: "error",
          message: `project error: ${libraryResolutionError}`,
        };
      const model = workspace.model(textDocument.uri);
      if (!model)
        return { kind: "error", message: "open a tung file to check a proof" };
      const document = documents.get(textDocument.uri);
      const version = document?.version ?? 0;
      const offset = position ? document?.offsetAt(position) : undefined;
      const region =
        offset === undefined
          ? undefined
          : smallestRegion(
              model.regions.filter(
                (candidate) =>
                  candidate.depth === 0 && candidate.kind === "let",
              ),
              offset,
            );
      const declaration =
        region &&
        model.definitions.find(
          (definition) =>
            definition.topLevel &&
            definition.token.index > region.startIndex &&
            definition.token.index <= region.headerEnd,
        );
      const selected =
        typeof name === "string" && name.trim()
          ? name.trim()
          : declaration?.name;
      if (!selected)
        return {
          kind: "error",
          message:
            "select a proof name or place the cursor in its top-level let declaration",
        };
      const imports = workspace.importSources(model);
      const running = compiler.proof(
        model,
        imports,
        selected,
        version,
        allowedOrsettings,
      );
      const cancelled = cancellation?.onCancellationRequested(() =>
        running.cancel(),
      );
      try {
        const result = await running.result;
        const current = workspace.model(textDocument.uri);
        const currentImports = workspace.importSources(current);
        if (
          (documents.get(textDocument.uri)?.version ?? 0) !== version ||
          current?.text !== model.text ||
          currentImports.length !== imports.length ||
          currentImports.some(
            ([path, text], index) =>
              path !== imports[index][0] || text !== imports[index][1],
          )
        )
          return {
            kind: "error",
            message:
              "the proof source or its imports changed; check the proof again",
          };
        return result;
      } finally {
        cancelled?.dispose();
      }
    },
  ),
);
process.on("exit", () => compiler.dispose());
connection.onNotification(
  "workspace/didChangeWorkspaceFolders",
  ({ event }) => {
    const { added = [], removed = [] } = event || {};
    const removedPaths = new Set(
      removed.map(({ uri }) => toFilePath(uri)).filter(Boolean),
    );
    workspaceRoots = uniqueByKey([
      ...workspaceRoots.filter((root) => !removedPaths.has(root)),
      ...added.map(({ uri }) => toFilePath(uri)).filter(Boolean),
    ]);
    configureWorkspace();
    checkAllOpenDocuments();
    scheduleSemanticRefresh();
  },
);
connection.onDidChangeWatchedFiles(({ changes }) => {
  if (
    changes.some(
      ({ uri }) => path.basename(toFilePath(uri) || "") === "tung.yaml",
    )
  ) {
    configureWorkspace();
  }
  for (const { uri } of changes) workspace.invalidate(uri);
  workspace.invalidateFiles();
  checkAllOpenDocuments();
  scheduleSemanticRefresh();
});
connection.languages.semanticTokens.on(({ textDocument }) =>
  semanticTokens(textDocument.uri),
);
connection.languages.semanticTokens.onRange(({ textDocument, range }) =>
  semanticTokens(textDocument.uri, range),
);
connection.onCompletion(
  navigation(({ textDocument, position }) => {
    const model = workspace.model(textDocument.uri);
    if (!model) return [];
    if (inUsePath(model, position)) {
      return workspace.modulePaths(textDocument.uri).map((label) => ({
        label,
        kind: CompletionItemKind.Module,
        detail: "tung module",
      }));
    }
    const prefix = completionPrefix(model, position);
    const definitions = [
      ...workspace.completions(textDocument.uri, position),
      ...workspace.primitiveCompletions(),
    ];
    const definitionItems = definitions
      .map((definition) => definitionCompletion(definition))
      .filter(
        ({ label }) =>
          !prefix || label.startsWith(prefix) || label.includes(`.${prefix}`),
      );
    const keywordItems = languageNames.keywords
      .filter((name) => !prefix || name.startsWith(prefix))
      .map((label) => ({
        label,
        kind: CompletionItemKind.Keyword,
        detail: keywordHelp[label] || "tung keyword",
      }));
    return uniqueByKey(
      [...definitionItems, ...keywordItems],
      ({ label }) => label,
    );
  }),
);
connection.onHover(
  navigation(async ({ textDocument, position }, cancellation) => {
    // a `sorry` showeth the goal and context the latest check found there.
    const open = documents.get(textDocument.uri);
    const offset = open?.offsetAt(position);
    const goal = (goalReports.get(textDocument.uri) || []).find(
      ({ start, end }) =>
        offset !== undefined && start <= offset && offset < end,
    );
    if (open && goal) {
      return {
        range: {
          start: open.positionAt(goal.start),
          end: open.positionAt(goal.end),
        },
        contents: {
          kind: MarkupKind.Markdown,
          value: `\`\`\`tung\n${goal.message}\n\`\`\``,
        },
      };
    }
    const resolved = workspace.resolveAt(textDocument.uri, position);
    if (resolved.definition) {
      const definition = resolved.definition;
      const header =
        definition.detail ||
        `${roleLabel(definition.role)} ${definition.bareName}`;
      const inferred = await inspectType(definition, cancellation);
      const docText = definition.documentation
        ? `${definition.documentation}\n\n`
        : "";
      const typeText = inferred
        ? `\n\n**inferred ilk**\n\n\`\`\`tung\n${definition.bareName}: ${inferred}\n\`\`\``
        : "";
      return {
        range: nameRange(resolved.token),
        contents: {
          kind: MarkupKind.Markdown,
          value: `${docText}\`\`\`tung\n${header}\n\`\`\`\n\n${roleDescription(
            definition,
          )}${typeText}`,
        },
      };
    }
    if (
      resolved.token?.kind === "keyword" &&
      keywordHelp[resolved.token.text]
    ) {
      return {
        range: tokenRange(resolved.token),
        contents: {
          kind: MarkupKind.Markdown,
          value: keywordHelp[resolved.token.text],
        },
      };
    }
    const primitive = workspace
      .primitiveCompletions()
      .find(({ bareName }) => bareName === resolved.token?.text);
    return primitive
      ? {
          range: nameRange(resolved.token),
          contents: { kind: MarkupKind.Markdown, value: primitive.detail },
        }
      : null;
  }),
);
const navigateToDefinition = navigation(({ textDocument, position }) =>
  definitionLocation(textDocument.uri, position),
);
connection.onDefinition(navigateToDefinition);
connection.onDeclaration(navigateToDefinition);
connection.onTypeDefinition(navigateToDefinition);
connection.onImplementation(
  navigation(({ textDocument, position }) => {
    const { definition } = workspace.resolveAt(textDocument.uri, position);
    return workspace.implementations(definition);
  }),
);
connection.onReferences(
  navigation(({ textDocument, position, context }) => {
    const { definition } = workspace.resolveAt(textDocument.uri, position);
    return workspace.references(definition, context.includeDeclaration);
  }),
);
connection.onDocumentHighlight(
  navigation(({ textDocument, position }) => {
    const { definition } = workspace.resolveAt(textDocument.uri, position);
    return workspace
      .references(definition, true)
      .filter(({ uri }) => uri === textDocument.uri)
      .map(({ range }) => ({ range, kind: DocumentHighlightKind.Read }));
  }),
);
connection.onDocumentSymbol(
  navigation(({ textDocument }) => {
    const model = workspace.model(textDocument.uri);
    if (!model) return [];
    const visible = model.definitions.filter(
      (definition) => !definition.local && definition.topLevel,
    );
    return visible.map((definition) => ({
      name: definition.bareName,
      detail: definition.detail,
      kind: symbolKind(definition.role),
      range:
        smallestRegion(model.regions, definition.token.offset)?.range ||
        definition.range,
      selectionRange: definition.selectionRange,
    }));
  }),
);
connection.onWorkspaceSymbol(
  navigation(({ query }) => {
    const wanted = query.toLocaleLowerCase();
    return workspace.models().flatMap((model) =>
      model.definitions
        .filter(
          (definition) =>
            !definition.local &&
            (!wanted ||
              definition.bareName.toLocaleLowerCase().includes(wanted)),
        )
        .map((definition) => ({
          name: definition.bareName,
          kind: symbolKind(definition.role),
          location: {
            uri: definition.uri,
            range: definition.selectionRange,
          },
          containerName: definition.containerName,
        })),
    );
  }),
);
connection.onPrepareRename(
  navigation(({ textDocument, position }) => {
    const { token, definition, candidates } = workspace.resolveAt(
      textDocument.uri,
      position,
    );
    if (!token || !definition || definition.primitive) return null;
    if (candidates?.length > 1) {
      throw new Error(`cannot rename ambiguous name '${token.text}'`);
    }
    return { range: nameRange(token), placeholder: definition.bareName };
  }),
);
connection.onRenameRequest(
  navigation(({ textDocument, position, newName }) => {
    if (!validName(newName)) throw new Error(`invalid tung name '${newName}'`);
    const { definition, candidates } = workspace.resolveAt(
      textDocument.uri,
      position,
    );
    if (!definition || definition.primitive) return null;
    if (candidates?.length > 1) {
      throw new Error("cannot rename an ambiguous name");
    }
    const changes = {};
    for (const { uri, range } of workspace.references(definition, true)) {
      (changes[uri] ||= []).push({ range, newText: newName });
    }
    return { changes };
  }),
);
connection.onFoldingRanges(
  navigation(
    ({ textDocument }) => workspace.model(textDocument.uri)?.folds || [],
  ),
);
connection.onSelectionRanges(
  navigation(({ textDocument, positions }) => {
    const model = workspace.model(textDocument.uri);
    if (!model) return [];
    return positions.map((position) => selectionRange(model, position));
  }),
);
connection.onDocumentLinks(
  navigation(({ textDocument }) => {
    const model = workspace.model(textDocument.uri);
    if (!model) return [];
    return model.imports.flatMap((imported) => {
      const target = workspace.resolveImport(model, imported);
      return target
        ? [
            {
              range: imported.range,
              target: target.uri,
              tooltip: `open ${imported.path}`,
            },
          ]
        : [];
    });
  }),
);
const formatDocument = async (uri) => {
  const document = documents.get(uri);
  if (!document) return undefined;
  const source = document.getText();
  const version = document.version;
  const formatted = await compiler.format(source, version).result;
  return formatted !== undefined && documents.get(uri)?.version === version
    ? { document, source, formatted }
    : undefined;
};
connection.onDocumentFormatting(async ({ textDocument }) => {
  const result = await formatDocument(textDocument.uri);
  return !result || result.formatted === result.source
    ? []
    : [{ range: fullRange(result.document), newText: result.formatted }];
});
connection.onSignatureHelp(
  navigation(({ textDocument, position }) => {
    const model = workspace.model(textDocument.uri);
    if (!model) return null;
    const before = model.tokens
      .filter(
        (token) =>
          token.line < position.line ||
          (token.line === position.line && token.char < position.character),
      )
      .at(-1);
    if (!before) return null;
    const resolved = workspace.resolveAt(textDocument.uri, {
      line: before.line,
      character: before.char,
    });
    if (
      !resolved.definition ||
      !["function", "method"].includes(resolved.definition.role)
    ) {
      return null;
    }
    return {
      signatures: [
        {
          label: resolved.definition.detail || resolved.definition.bareName,
        },
      ],
      activeSignature: 0,
      activeParameter: 0,
    };
  }),
);
documents.onDidOpen(({ document }) => {
  configureWorkspace();
  workspace.invalidate(document.uri);
  clearTypeCache(document.uri);
  checkAllOpenDocuments();
});
documents.onDidChangeContent(({ document }) => {
  workspace.invalidate(document.uri);
  clearTypeCache(document.uri);
  scheduleCheck(document);
  for (const dependent of documents.all()) {
    if (dependent.uri !== document.uri) {
      scheduleCheck(dependent, dependentCheckDelay);
    }
  }
  scheduleSemanticRefresh();
});
documents.onDidSave(({ document }) => {
  workspace.invalidate(document.uri);
  clearTypeCache(document.uri);
});
documents.onDidClose(({ document }) => {
  cancelCheck(document.uri);
  configureWorkspace();
  workspace.invalidate(document.uri);
  const previous = diagnosticReports.get(document.uri);
  diagnosticReports.delete(document.uri);
  goalReports.delete(document.uri);
  for (const { targetUri } of previous || []) refreshDiagnostics(targetUri);
  refreshDiagnostics(document.uri);
  checkAllOpenDocuments();
});
// requests share one compiler parse per buffer version. navigation refineth only
// names whose constructor identity requireth workspace context.
const semanticTokens = async (uri, requestedRange = undefined) => {
  const document = documents.get(uri);
  const builder = new SemanticTokensBuilder();
  if (!document) return builder.build();
  const source = document.getText();
  const version = document.version;
  const roles = await workspace.roles(uri, source, version);
  await workspace.ready();
  if (documents.get(uri)?.version !== version) return builder.build();
  const resolve = (token) =>
    workspace.resolveAt(uri, { line: token.line, character: token.char })
      .definition;
  for (const token of buildHighlightRanges(source, roles, resolve)) {
    if (requestedRange && !rangeContainsLine(requestedRange, token.line)) {
      continue;
    }
    const type = tokenTypes.indexOf(token.type);
    if (type < 0) continue;
    builder.push(
      token.line,
      token.char,
      token.length,
      type,
      token.modifiers.reduce((bits, name) => {
        const index = tokenModifiers.indexOf(name);
        return index < 0 ? bits : bits | (1 << index);
      }, 0),
    );
  }
  return builder.build();
};
const scheduleSemanticRefresh = (delay = semanticRefreshDelay) => {
  clearTimeout(semanticRefreshTimer);
  semanticRefreshTimer = setTimeout(() => {
    semanticRefreshTimer = undefined;
    if (canRefreshSemanticTokens) {
      Promise.resolve(connection.languages.semanticTokens.refresh()).catch(
        () => {},
      );
    }
  }, delay);
};
const scheduleCheck = (document, delay = defaultCheckDelay) => {
  cancelCheck(document.uri);
  timers.set(
    document.uri,
    setTimeout(() => runCheck(document), delay),
  );
};
const cancelCheck = (uri) => {
  clearTimeout(timers.get(uri));
  timers.delete(uri);
  checks.get(uri)?.cancel();
  checks.delete(uri);
};
const checkAllOpenDocuments = () => {
  for (const document of documents.all()) scheduleCheck(document, 0);
};
// diagnostics are debounced and versioned; cancellation stopeth obsolete work
// in the persistent compiler session before a newer request is sent.
const runCheck = (document) => {
  timers.delete(document.uri);
  if (libraryResolutionError) {
    publish(document, `project error: ${libraryResolutionError}`);
    return;
  }
  if (!compiler.available()) {
    publish(
      document,
      configuredExecutable
        ? `could not find tung executable at ${configuredExecutable}`
        : "could not find tung executable; install tung or set tung.executablePath",
    );
    return;
  }
  const model = workspace.model(document.uri);
  const running = compiler.check(
    model,
    workspace.importSources(model),
    document.version,
  );
  checks.set(document.uri, running);
  running.result.then((output) => {
    if (checks.get(document.uri) !== running) return;
    checks.delete(document.uri);
    const current = documents.get(document.uri);
    if (!current || current.version !== running.version) return;
    const diagnostics = output.kind === "check" ? output.diagnostics : [];
    const goals = diagnostics.filter(
      (diagnostic) => diagnostic.kind === "goal",
    );
    goalReports.set(current.uri, goals);
    publish(
      current,
      output.kind === "error"
        ? output.message
        : diagnostics.find((diagnostic) => diagnostic.kind !== "goal"),
      goals,
    );
  });
};
const inspectType = (definition, cancellation = undefined) => {
  if (!definition?.uri || definition.primitive || !compiler.available()) {
    return Promise.resolve(undefined);
  }
  const model = workspace.model(definition.uri);
  if (!model) return Promise.resolve(undefined);
  const key = `${definition.uri}\0${definition.bareName}\0${model.text}`;
  const cached = typeCache.get(key);
  if (cached) return cached.promise;
  const version = documents.get(definition.uri)?.version || 0;
  const running = compiler.ilkOf(
    model,
    workspace.importSources(model),
    definition.bareName,
    version,
  );
  const entry = {
    cancel: running.cancel,
    promise: running.result.then((output) =>
      output.kind === "ilk" ? output.ilk : undefined,
    ),
  };
  typeCache.set(key, entry);
  const cancelled = cancellation?.onCancellationRequested(() => {
    if (typeCache.get(key) !== entry) return;
    typeCache.delete(key);
    entry.cancel();
  });
  return entry.promise.finally(() => cancelled?.dispose());
};
const clearTypeCache = (uri) => {
  for (const key of typeCache.keys()) {
    if (!key.startsWith(`${uri}\0`)) continue;
    typeCache.get(key)?.cancel();
    typeCache.delete(key);
  }
};
const publish = (document, diagnostic, goals = []) => {
  const previous = diagnosticReports.get(document.uri);
  const message =
    typeof diagnostic === "string" ? diagnostic : diagnostic?.message;
  const owner = diagnosticOwner(document, diagnostic);
  // a root buffer's goals retain their locations when an import hath an error.
  const items: { targetUri: string; diagnostic: Diagnostic }[] = goals.map(
    ({ start, end, message: goal }) => ({
      targetUri: document.uri,
      diagnostic: {
        range: {
          start: document.positionAt(start),
          end: document.positionAt(end),
        },
        severity: DiagnosticSeverity.Information,
        source: "tung",
        message: goal,
      },
    }),
  );
  if (message) {
    items.unshift({
      targetUri: owner.uri,
      diagnostic: {
        range: errorRange(owner, diagnostic),
        severity: DiagnosticSeverity.Error,
        source: "tung",
        message,
      },
    });
  }
  if (items.length) {
    diagnosticReports.set(document.uri, items);
  } else {
    diagnosticReports.delete(document.uri);
  }
  for (const uri of new Set([
    document.uri,
    ...[...(previous || []), ...items].map(({ targetUri }) => targetUri),
  ])) {
    refreshDiagnostics(uri);
  }
};
const diagnosticOwner = (document, diagnostic) => {
  if (typeof diagnostic !== "string" && diagnostic?.path) {
    const root = workspace.model(document.uri);
    const imported = workspace.importModel(root, diagnostic.path);
    if (imported) {
      const open = documents.get(imported.uri);
      return (
        open || TextDocument.create(imported.uri, "tung", 0, imported.text)
      );
    }
  }
  return document;
};
const refreshDiagnostics = (uri) => {
  if (!uri) return;
  const items = uniqueByKey(
    [...diagnosticReports.values()]
      .flat()
      .filter(({ targetUri }) => targetUri === uri)
      .map(({ diagnostic }) => diagnostic),
    ({ range, message }) =>
      `${range.start.line}:${range.start.character}:${range.end.line}:${range.end.character}:${message}`,
  );
  const open = documents.get(uri);
  connection.sendDiagnostics({
    uri,
    ...(open ? { version: open.version } : {}),
    diagnostics: items,
  });
};
const errorRange = (document, diagnostic) => {
  if (
    typeof diagnostic !== "string" &&
    Number.isInteger(diagnostic?.start) &&
    Number.isInteger(diagnostic?.end)
  ) {
    return {
      start: document.positionAt(diagnostic.start),
      end: document.positionAt(diagnostic.end),
    };
  }
  return {
    start: document.positionAt(0),
    end: document.positionAt(Math.min(1, document.getText().length)),
  };
};
const definitionLocation = (uri, position) => {
  const { definition } = workspace.resolveAt(uri, position);
  return definition?.uri
    ? { uri: definition.uri, range: definition.selectionRange }
    : null;
};
const definitionCompletion = (definition) => {
  const label = definition.completionName || definition.bareName;
  return {
    label,
    kind: completionKind(definition.role),
    detail: definition.detail,
    documentation: definition.documentation,
    insertText: label,
    insertTextFormat: InsertTextFormat.PlainText,
    sortText: definition.local
      ? `0-${label}`
      : definition.primitive
        ? `2-${label}`
        : `1-${label}`,
  };
};
const roleKinds: Record<string, [CompletionItemKind, SymbolKind]> = {
  namespace: [CompletionItemKind.Module, SymbolKind.Namespace],
  type: [CompletionItemKind.TypeParameter, SymbolKind.TypeParameter],
  class: [CompletionItemKind.Interface, SymbolKind.Interface],
  function: [CompletionItemKind.Function, SymbolKind.Function],
  method: [CompletionItemKind.Method, SymbolKind.Method],
  variable: [CompletionItemKind.Variable, SymbolKind.Variable],
  parameter: [CompletionItemKind.Variable, SymbolKind.Variable],
  property: [CompletionItemKind.Field, SymbolKind.Field],
  enumMember: [CompletionItemKind.EnumMember, SymbolKind.EnumMember],
};
const completionKind = (role) =>
  roleKinds[role]?.[0] || CompletionItemKind.Text;
const symbolKind = (role) => roleKinds[role]?.[1] || SymbolKind.String;
const roleDescription = (definition) => {
  const where =
    definition.uri && toFilePath(definition.uri)
      ? `defined in \`${path.basename(toFilePath(definition.uri))}\``
      : "";
  const visibility = definition.exported
    ? "shown"
    : definition.local
      ? "local"
      : "private";
  return [visibility, roleLabel(definition.role), where]
    .filter(Boolean)
    .join(" · ");
};
const selectionRange = (model, position) => {
  const token = tokenAtPosition(model, position);
  const ranges = [
    token ? tokenRange(token) : { start: position, end: position },
  ];
  const containing = [...model.pairs.entries()]
    .filter(
      ([open, close]) =>
        model.tokens[open].offset <= (token?.offset ?? model.text.length) &&
        (token?.endOffset ?? model.text.length) <=
          model.tokens[close].endOffset,
    )
    .sort(([a], [b]) => b - a);
  for (const [open, close] of containing) {
    ranges.push(tokenRange(model.tokens[open], model.tokens[close]));
  }
  let parent;
  for (const range of ranges.reverse()) {
    parent = { range, ...(parent ? { parent } : {}) };
  }
  return parent;
};
const inUsePath = (model, position) => {
  const offset = offsetAt(model.text, position);
  return (
    model.imports.some(({ range }) => positionInRange(position, range)) ||
    /(?:^|\s)use\s+[^\s]*$/.test(model.text.slice(0, offset))
  );
};
const completionPrefix = (model, position) => {
  const offset = offsetAt(model.text, position);
  const before = model.text.slice(0, offset);
  return before.match(/[^\s#()[\]{}:,;=.$`'@^]+$/u)?.[0] || "";
};
const fullRange = (document) => {
  return {
    start: { line: 0, character: 0 },
    end: document.positionAt(document.getText().length),
  };
};
const rangeContainsLine = (range, line) => {
  return range.start.line <= line && line <= range.end.line;
};
const positionInRange = (position, range) => {
  return (
    comparePosition(range.start, position) <= 0 &&
    comparePosition(position, range.end) <= 0
  );
};
const comparePosition = (left, right) => {
  return left.line - right.line || left.character - right.character;
};
const offsetAt = (text, position) => {
  const lines = text.split(/\r\n|\r|\n/);
  let offset = 0;
  for (let line = 0; line < Math.min(position.line, lines.length); line += 1) {
    offset += lines[line].length + 1;
  }
  return offset + position.character;
};
const validName = (name) => {
  return Boolean(name) && name !== "*" && !/[\s#()[\]{}:,;=.$`'@^]/u.test(name);
};
const configureWorkspace = () => {
  tongueDir = findTongueDir(configuredTongue);
  localLibraryRoots = resolveLibraryPaths(
    [],
    configuredLibraryPaths,
    process.env.TUNG_PATH,
  );
  const executable = configuredExecutable || undefined;
  if (
    compiler.tongue !== tongueDir ||
    compiler.executablePath !== executable ||
    compiler.libraryRoots.length !== localLibraryRoots.length ||
    compiler.libraryRoots.some(
      (root, index) => root !== localLibraryRoots[index],
    )
  ) {
    workspace.clearRoles();
  }
  compiler.configure(tongueDir, localLibraryRoots, executable);
  let declared: string[] = [];
  libraryResolutionError = undefined;
  try {
    const openProjects = documents
      .all()
      .map(({ uri }) => toFilePath(uri))
      .filter(Boolean);
    declared = readDeclaredLibraryPaths(
      compiler.findExecutable(),
      openProjects.length ? openProjects : workspaceRoots,
    );
  } catch (error) {
    libraryResolutionError = String(error);
    connection.console.error(libraryResolutionError);
  }
  libraryRoots = resolveLibraryPaths(declared, localLibraryRoots, undefined);
  workspace.configure(workspaceRoots, libraryRoots);
};
const findTongueDir = (configured) => {
  const roots = [
    configured && path.resolve(configured),
    process.env.TUNG_TONGUE && path.resolve(process.env.TUNG_TONGUE),
    ...workspaceRoots,
    path.resolve(__dirname, "..", "..", ".."),
  ];
  for (const root of roots.filter(Boolean)) {
    for (const candidate of [root, path.join(root, "tongue")]) {
      if (fs.existsSync(path.join(candidate, "tung.cabal"))) return candidate;
    }
  }
  return undefined;
};
documents.listen(connection);
connection.listen();
