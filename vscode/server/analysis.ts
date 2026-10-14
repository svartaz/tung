// document model over the compiler's one parse of a buffer, complete or not:
// its roles, tokens, declarations, docs, imports, and local scopes. it addeth
// ownership; it never checketh types.
import { emptySyntax, type SourceRole, type SourceSyntax } from "./checker.ts";
import {
  bracketPairs,
  lastQualifiedSegment,
  sourceTokens,
  tokenDepths,
  useNamespace,
  type SourceToken,
} from "./syntax.ts";
const ownedKinds = new Set(["ilk", "flock"]);
const localRoles = new Set(["parameter", "typeParameter"]);
// lsp role names stay in the protocol; people read them in tung's terms.
const roleNames = {
  type: "ilk",
  typeParameter: "ilk input",
  class: "flock",
  enumMember: "constructor",
  method: "limb",
};
const roleLabel = (role: string) => roleNames[role] ?? role;
const keywordHelp = {
  bring:
    "import a tung file; its last path segment is the default namespace, and an optional alias overrideth it.",
  show: "publish a declaration, or re-export every visible term, ilk, and flock with a name.",
  yield: "introduce a block result.",
  sorry:
    "stand for an omitted proof or definition of any ilk; performing it is a runtime error.",
  orsetting:
    "assume a named constant of an ilk without a proof; `--check` lists it, `--no-sorry` alloweth it, and `--no-orset` refuseth it in a proof check.",
  unbuild:
    "name the eliminator of an ilk or flock: `drive unbuild name methods target` performeth structural induction.",
  flock: "declare a flock and its members.",
  fremmed:
    "bind an annotated file-level let to the host function named by a preceding string key.",
  bizen: "provide evidence and member definitions for a flock.",
  match:
    "match one or more values against exhaustive pattern rows; `;` joineth rows that share a result.",
  fall: "write an annotated function: inputs, a final result ilk, `^`, and the body.",
  let: "bind a value, curried function, or ilk alias.",
  ilk: "declare an inductive ilk and its constructors.",
};
const analyzeDocument = (
  text: string,
  uri = "",
  syntax: SourceSyntax = emptySyntax,
) => {
  const tokens = sourceTokens(text, syntax);
  const depths = tokenDepths(tokens);
  const pairs = bracketPairs(tokens);
  const regions = declarationRegions(tokens, depths, syntax);
  const semantic = compilerSemantic(tokens, syntax.roles, regions, depths);
  const roles = semantic.semantic;
  const imports = syntax.imports.flatMap(({ path, alias, start, end }) => {
    const first = tokenAt(tokens, start);
    const last = tokenEndingAt(tokens, end);
    if (!first || !last) return [];
    return [
      {
        path,
        namespace: useNamespace(path, alias ?? undefined),
        alias: alias ?? undefined,
        exported: false,
        range: tokenRange(first, last),
      },
    ];
  });
  const definitions = semanticDefinitions(
    text,
    tokens,
    semantic,
    depths,
    regions,
    syntax,
  );
  definitions.forEach((definition, id) => {
    definition.id = `${uri}:${definition.token.offset}:${id}`;
    definition.uri = uri;
  });
  return {
    uri,
    text,
    tokens,
    semantic,
    roles,
    depths,
    pairs,
    regions,
    imports,
    instances: collectInstances(tokens, semantic, regions),
    definitions,
    occurrences: tokens.filter((token) => token.kind === "name"),
    folds: [...pairs.entries()]
      .map(([open, close]) => ({
        startLine: tokens[open].line,
        endLine: tokens[close].line - 1,
      }))
      .filter(({ startLine, endLine }) => endLine > startLine),
  };
};
// compiler roles become the model's token roles. a header binder arriveth as
// `headerPattern`, since only name resolution can tell a binder from a
// constructor: it is a parameter here, and resolution prefereth a visible
// constructor of the same name. a direct declaration in a flock or bizen
// body is a method; nested declarations retain their own roles.
const compilerSemantic = (
  tokens,
  sourceRoles: SourceRole[],
  regions,
  depths,
) => {
  const byOffset = new Map<number, SourceToken>(
    tokens.map((token) => [token.offset, token]),
  );
  const semantic = new Map<number, { type: string; modifiers: string[] }>();
  const callableConstructors = new Set<string>();
  for (const [start, , role, modifiers] of sourceRoles) {
    const token = byOffset.get(start);
    if (!token || token.kind !== "name") continue;
    const declared = modifiers.includes("declaration");
    let type = role;
    let roleModifiers = modifiers.filter(
      (modifier) => modifier !== "constructor",
    );
    if (modifiers.includes("constructor")) {
      type = "enumMember";
      if (role === "function") {
        callableConstructors.add(lastQualifiedSegment(token.text));
      }
    } else if (role === "headerPattern") {
      type = "parameter";
      roleModifiers = ["declaration"];
    } else if (role === "call" && declared) {
      type = "function";
    }
    if (
      declared &&
      (type === "variable" || type === "function") &&
      regions.some(
        (region) =>
          (region.kind === "flock" || region.kind === "bizen") &&
          depths[token.index] === region.depth + 1 &&
          token.index > region.headerEnd &&
          token.offset <= region.endOffset &&
          token.offset >= region.startOffset,
      )
    ) {
      type = "method";
    }
    semantic.set(token.index, { type, modifiers: roleModifiers });
  }
  return { semantic, callableConstructors };
};
const collectInstances = (tokens, semantic, regions) => {
  return regions
    .filter(({ kind }) => kind === "bizen")
    .flatMap((region) => {
      for (
        let index = region.headerEnd - 1;
        index > region.startIndex;
        index -= 1
      ) {
        const role = semantic.semantic.get(index);
        if (role?.type === "class" && tokens[index]?.kind === "name") {
          return [
            {
              className: lastQualifiedSegment(tokens[index].text),
              uri: "",
              range: tokenRange(tokens[index]),
              token: tokens[index],
            },
          ];
        }
      }
      return [];
    });
};
// regions supply ownership and source extents for symbols, folding, docs, and
// local scope. each is a declaration the compiler's tree holdeth.
const declarationRegions = (tokens, depths, syntax: SourceSyntax) =>
  syntax.declarations.flatMap(({ kind, start, end, headerEnd, shown, doc }) => {
    const startToken = tokenAt(tokens, start);
    const endToken = tokenEndingAt(tokens, end);
    if (!startToken || !endToken) return [];
    const header = tokens.findIndex((token) => token.offset >= headerEnd);
    return [
      {
        kind,
        startOffset: start,
        endOffset: end,
        startIndex: startToken.index,
        endIndex: endToken.index,
        headerEnd: header < 0 ? tokens.length : header,
        depth: depths[startToken.index],
        shown,
        doc: doc ?? undefined,
        range: tokenRange(startToken, endToken),
      },
    ];
  });
const tokenAt = (tokens, offset) =>
  tokens.find((token) => token.offset === offset);
const tokenEndingAt = (tokens, offset) =>
  tokens.findLast((token) => token.endOffset === offset);
const semanticDefinitions = (
  text,
  tokens,
  semantic,
  depths,
  regions,
  syntax: SourceSyntax,
) => {
  // the parser giveth each local binder the span where it is seen; every
  // other declaration is seen by the whole document.
  const scopes = new Map(
    syntax.scopes.map(([start, , scopeStart, scopeEnd]) => [
      start,
      { start: scopeStart, end: scopeEnd },
    ]),
  );
  const documentEnd = tokens.at(-1)?.endOffset || 0;
  const definitions = [];
  for (const [index, role] of semantic.semantic) {
    if (!role.modifiers.includes("declaration")) continue;
    const token = tokens[index];
    if (
      !token ||
      token.kind !== "name" ||
      token.text === "_" ||
      role.type === "namespace"
    ) {
      continue;
    }
    const region = smallestRegion(regions, token.offset);
    const owner =
      region && ownedKinds.has(region.kind) && token.index > region.headerEnd
        ? region
        : enclosingOwner(regions, region, token.offset);
    const binder = scopes.get(token.offset);
    const local = Boolean(binder) || localRoles.has(role.type);
    const primary =
      region &&
      token.index > region.startIndex &&
      token.index <= region.headerEnd;
    const exported =
      !local &&
      Boolean(
        (region?.shown && primary) ||
        (owner?.shown &&
          ["enumMember", "method", "function"].includes(role.type)),
      );
    // a local the parser could not scope, in broken source, keepeth to its
    // declaration.
    const scope =
      binder ??
      (local && region
        ? { start: region.startOffset, end: region.endOffset }
        : { start: 0, end: documentEnd });
    const parameter = Boolean(binder) && localRoles.has(role.type);
    definitions.push({
      name: token.text,
      bareName: lastQualifiedSegment(token.text),
      role: role.type,
      modifiers: binder ? ["declaration"] : role.modifiers,
      token,
      range: tokenRange(token),
      selectionRange: tokenRange(token),
      scopeStart: scope.start,
      scopeEnd: scope.end,
      exported: !binder && exported,
      local,
      topLevel: !binder && depths[token.index] === 0,
      detail: parameter
        ? `parameter ${lastQualifiedSegment(token.text)}`
        : declarationDetail(text, tokens, token, region, role.type),
      callableConstructor: binder
        ? undefined
        : role.type === "enumMember" &&
          semantic.callableConstructors.has(lastQualifiedSegment(token.text)),
      documentation: binder ? undefined : region?.doc,
      containerName: binder ? undefined : ownerName(tokens, semantic, owner),
    });
  }
  return definitions;
};
const declarationDetail = (text, tokens, token, region, role) => {
  if (!region) return `${roleLabel(role)} ${lastQualifiedSegment(token.text)}`;
  const end = tokens[region.headerEnd]?.offset ?? token.endOffset;
  const header = text
    .slice(region.startOffset, end)
    .replace(/\s+/g, " ")
    .trim();
  return header || `${roleLabel(role)} ${lastQualifiedSegment(token.text)}`;
};
const smallestRegion = (regions, offset, kind = undefined) => {
  return regions
    .filter(
      (region) =>
        (!kind || region.kind === kind) &&
        region.startOffset <= offset &&
        offset <= region.endOffset,
    )
    .sort(
      (a, b) => a.endOffset - a.startOffset - (b.endOffset - b.startOffset),
    )[0];
};
const enclosingOwner = (regions, region, offset) => {
  return smallestRegion(
    regions.filter(
      (candidate) => ownedKinds.has(candidate.kind) && candidate !== region,
    ),
    offset,
  );
};
const ownerName = (tokens, semantic, owner) => {
  if (!owner) return undefined;
  for (let index = owner.startIndex + 1; index <= owner.headerEnd; index += 1) {
    const role = semantic.semantic.get(index);
    if (role?.modifiers.includes("declaration") && !localRoles.has(role.type)) {
      return tokens[index].text;
    }
  }
  return undefined;
};
const findDefinition = (model, token, offset = token?.offset) => {
  if (!token || token.kind !== "name") return undefined;
  const name = lastQualifiedSegment(token.text);
  return model.definitions
    .filter(
      (definition) =>
        definition.bareName === name &&
        definition.scopeStart <= offset &&
        offset <= definition.scopeEnd,
    )
    .sort((a, b) => {
      const aWidth = a.scopeEnd - a.scopeStart;
      const bWidth = b.scopeEnd - b.scopeStart;
      if (aWidth !== bWidth) return aWidth - bWidth;
      return (
        Math.abs(offset - a.token.offset) - Math.abs(offset - b.token.offset)
      );
    })[0];
};
const tokenAtPosition = (model, position) => {
  return model.tokens.find(
    (token) =>
      token.line === position.line &&
      token.char <= position.character &&
      token.endChar > position.character,
  );
};
const tokenRange = (first, last = first) => {
  return {
    start: { line: first.line, character: first.char },
    end: { line: last.endLine, character: last.endChar },
  };
};
const nameRange = (token) => {
  const split = token.text.indexOf("~");
  const delta = split < 0 ? 0 : split + 1;
  return {
    start: { line: token.line, character: token.char + delta },
    end: { line: token.endLine, character: token.endChar },
  };
};
export {
  analyzeDocument,
  findDefinition,
  keywordHelp,
  roleLabel,
  nameRange,
  smallestRegion,
  tokenAtPosition,
  tokenRange,
};
