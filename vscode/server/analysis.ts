// structural model for incomplete buffers. it joineth the compiler's source
// roles with declaration regions, docs, imports, and scopes; it never checketh
// types.
import type { SourceRole } from "./checker.ts";
import {
  bracketPairs,
  declarationKeywords,
  findFileDeclarationBoundary,
  findInstanceHeader,
  findMatching,
  lastQualifiedSegment,
  patternArmRegions,
  tokenDepths,
  tokenize,
  useNamespace,
  useParts,
} from "./syntax.ts";
const ownedKinds = new Set(["ilk", "flock"]);
const localRoles = new Set(["parameter", "typeParameter"]);
const keywordHelp = {
  use: "import a tung file; its last path segment is the default namespace, and an optional alias overrideth it.",
  show: "publish a declaration, or re-export every visible term, type, and flock with a name.",
  yield: "introduce a block result.",
  sorry:
    "stand for an omitted proof or definition of any type; performing it is a runtime error.",
  orsetting:
    "assume a named constant of a type without a proof; `--check` lists it and `--no-sorry` allows it.",
  unbuild:
    "name the eliminator of an ilk or flock: `motive unbuild name methods target` performeth structural induction.",
  flock: "declare a flock and its members.",
  fremmed:
    "bind an annotated file-level let to the host function named by a preceding string key.",
  bizen: "provide evidence and member definitions for a flock.",
  match:
    "match one or more values against exhaustive pattern rows; `;` joineth rows that share a result.",
  fall: "write a typed function: inputs, a final result type, `^`, and the body.",
  let: "bind a value, curried function, or type alias.",
  ilk: "declare an algebraic data type.",
};
const analyzeDocument = (
  text: string,
  uri = "",
  sourceRoles: SourceRole[] = [],
) => {
  const tokens = tokenize(text);
  const depths = tokenDepths(tokens);
  const pairs = bracketPairs(tokens);
  const regions = declarationRegions(tokens, depths, pairs);
  const semantic = compilerSemantic(tokens, sourceRoles, regions, depths);
  const roles = semantic.semantic;
  const docs = collectDocComments(text);
  attachDocs(regions, docs, tokens);
  const imports = collectImports(tokens, depths);
  const reexports = collectReexports(tokens, depths);
  const definitions = semanticDefinitions(
    text,
    tokens,
    semantic,
    depths,
    regions,
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
    reexports,
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
  const byOffset = new Map<number, ReturnType<typeof tokenize>[number]>(
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
const collectDocComments = (text) => {
  const docs = [];
  const linePattern = /^[ \t]*##[ \t]?(.*)$/;
  let offset = 0;
  const lines = text.split(/(\r\n|\r|\n)/);
  for (let index = 0; index < lines.length; index += 2) {
    const line = lines[index];
    const newline = lines[index + 1] || "";
    const match = line.match(linePattern);
    if (match) {
      const startOffset = offset;
      const parts = [match[1]];
      let endOffset = offset + line.length + newline.length;
      offset = endOffset;
      while (index + 2 < lines.length) {
        const nextLine = lines[index + 2];
        const nextNewline = lines[index + 3] || "";
        const nextMatch = nextLine.match(linePattern);
        if (!nextMatch) break;
        parts.push(nextMatch[1]);
        index += 2;
        endOffset += nextLine.length + nextNewline.length;
        offset = endOffset;
      }
      docs.push({
        startOffset,
        endOffset,
        text: cleanDoc(parts.join("\n")),
      });
      continue;
    }
    offset += line.length + newline.length;
  }
  for (const match of text.matchAll(/\/\*\*([\s\S]*?)\*\//g)) {
    docs.push({
      startOffset: match.index,
      endOffset: match.index + match[0].length,
      text: cleanBlockDoc(match[1]),
    });
  }
  return docs
    .filter(({ text }) => text)
    .sort((a, b) => a.startOffset - b.startOffset);
};
const cleanBlockDoc = (text) => {
  return cleanDoc(
    text
      .split(/\r?\n/)
      .map((line) => line.replace(/^\s*\* ?/, ""))
      .join("\n"),
  );
};
const cleanDoc = (text) => {
  return text
    .split(/\r?\n/)
    .map((line) => line.trim())
    .join("\n")
    .replace(/^\n+|\n+$/g, "");
};
const attachDocs = (regions, docs, tokens) => {
  for (const region of regions) {
    const doc = [...docs]
      .reverse()
      .find(
        (candidate) =>
          candidate.endOffset <= region.startOffset &&
          !hasDeclarationBetween(
            tokens,
            candidate.endOffset,
            region.startOffset,
          ),
      );
    if (doc) region.doc = doc.text;
  }
};
const hasDeclarationBetween = (tokens, startOffset, endOffset) => {
  return tokens.some(
    (token) =>
      token.offset >= startOffset &&
      token.offset < endOffset &&
      token.kind === "keyword" &&
      declarationKeywords.has(token.text),
  );
};
// regions supply ownership and source extents for symbols, folding, docs, and
// local scope. unmatched delimiters fall back to the document end.
const declarationRegions = (tokens, depths, pairs) => {
  const regions = [];
  for (const token of tokens) {
    if (token.kind !== "keyword" || !declarationKeywords.has(token.text)) {
      continue;
    }
    const baseDepth = depths[token.index];
    const open =
      token.text === "bizen"
        ? (findInstanceHeader(tokens, token.index + 1, depths)?.body ?? -1)
        : ownedKinds.has(token.text)
          ? findAtDepth(tokens, depths, token.index + 1, "{", baseDepth)
          : -1;
    const boundary = findFileDeclarationBoundary(
      tokens,
      token.index + 1,
      depths,
      baseDepth,
    );
    const endIndex =
      open >= 0 && pairs.has(open)
        ? pairs.get(open)
        : Math.max(token.index, boundary - 1);
    const endToken = tokens[endIndex] || tokens.at(-1) || token;
    const headerEnd =
      token.text === "bizen" && open >= 0
        ? open
        : findHeaderEnd(
            tokens,
            depths,
            token.index + 1,
            endIndex + 1,
            baseDepth,
          );
    const shown = tokens[token.index - 1]?.text === "show";
    regions.push({
      kind: token.text,
      startOffset: token.offset,
      endOffset: endToken.endOffset,
      startIndex: token.index,
      endIndex,
      headerEnd,
      depth: baseDepth,
      shown,
      range: tokenRange(token, endToken),
    });
  }
  return regions;
};
const findHeaderEnd = (tokens, depths, start, end, baseDepth) => {
  for (let index = start; index < end; index += 1) {
    if (depths[index] === baseDepth && tokens[index].text === "[") {
      const close = findMatching(tokens, index);
      if (close >= 0) return close + (tokens[close + 1]?.text === "≔" ? 2 : 1);
    }
    if (depths[index] === baseDepth && tokens[index].text === "≔")
      return index + 1;
    if (depths[index] === baseDepth && tokens[index].text === "{") return index;
  }
  return Math.max(start, end - 1);
};
const collectImports = (tokens, depths) => {
  const imports = [];
  for (const token of tokens) {
    if (token.text !== "use") continue;
    const { pathTokens, aliasToken } = useParts(tokens, token.index, depths);
    const importPath = pathTokens.map(({ text }) => text).join("");
    if (!importPath) continue;
    const namespace = useNamespace(importPath, aliasToken?.text);
    imports.push({
      path: importPath,
      namespace,
      alias: aliasToken?.text,
      exported: tokens[token.index - 1]?.text === "show",
      range: tokenRange(pathTokens[0], pathTokens.at(-1)),
    });
  }
  return imports;
};
const collectReexports = (tokens, depths) => {
  const reexports = [];
  for (const token of tokens) {
    if (token.text !== "show" || depths[token.index] !== 0) continue;
    const next = tokens[token.index + 1];
    if (!next || next.kind !== "name") continue;
    const end = findFileDeclarationBoundary(
      tokens,
      next.index,
      depths,
      depths[token.index],
    );
    for (let index = next.index; index < end; index += 1) {
      if (tokens[index].kind === "name") {
        reexports.push({ name: tokens[index].text });
      }
    }
  }
  return reexports;
};
const semanticDefinitions = (text, tokens, semantic, depths, regions) => {
  const scopes = patternScopes(tokens, semantic);
  // row binders come first, as their precise scopes override declaration-wide
  // scopes. every token still hath only one definition and one stable id.
  const indices = new Set([...scopes.keys(), ...semantic.semantic.keys()]);
  const definitions = [];
  for (const index of indices) {
    const role = semantic.semantic.get(index);
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
    const local = localRoles.has(role.type);
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
    const pattern = scopes.get(index);
    const scope = pattern || definitionScope(tokens, region, role.type);
    definitions.push({
      name: token.text,
      bareName: lastQualifiedSegment(token.text),
      role: role.type,
      modifiers: pattern ? ["declaration"] : role.modifiers,
      token,
      range: tokenRange(token),
      selectionRange: tokenRange(token),
      scopeStart: scope.start,
      scopeEnd: scope.end,
      exported: !pattern && exported,
      local: Boolean(pattern) || local,
      topLevel: !pattern && depths[token.index] === 0,
      detail: pattern
        ? `parameter ${lastQualifiedSegment(token.text)}`
        : declarationDetail(text, tokens, token, region, role.type),
      callableConstructor: pattern
        ? undefined
        : role.type === "enumMember" &&
          semantic.callableConstructors.has(lastQualifiedSegment(token.text)),
      documentation: pattern ? undefined : region?.doc,
      containerName: pattern ? undefined : ownerName(tokens, semantic, owner),
    });
  }
  return definitions;
};
const patternScopes = (tokens, semantic) => {
  const scopes = new Map<number, { start: number; end: number }>();
  for (const { patternStart, pipe, bodyEnd } of patternArmRegions(tokens)) {
    const endOffset =
      tokens[bodyEnd]?.offset ?? tokens.at(-1)?.endOffset ?? pipe.endOffset;
    for (const token of tokens.slice(patternStart, pipe.index)) {
      const role = semantic.semantic.get(token.index);
      if (
        token.kind !== "name" ||
        role?.type !== "parameter" ||
        !role.modifiers.includes("declaration")
      ) {
        continue;
      }
      if (!scopes.has(token.index))
        scopes.set(token.index, { start: pipe.endOffset, end: endOffset });
    }
  }
  return scopes;
};
const definitionScope = (tokens, region, role) => {
  const documentEnd = tokens.at(-1)?.endOffset || 0;
  if (!localRoles.has(role)) return { start: 0, end: documentEnd };
  if (!region) return { start: 0, end: documentEnd };
  return {
    start:
      role === "typeParameter"
        ? region.startOffset
        : (tokens[region.headerEnd]?.offset ?? region.startOffset),
    end: region.endOffset,
  };
};
const declarationDetail = (text, tokens, token, region, role) => {
  if (!region) return `${role} ${lastQualifiedSegment(token.text)}`;
  const end = tokens[region.headerEnd]?.offset ?? token.endOffset;
  const header = text
    .slice(region.startOffset, end)
    .replace(/\s+/g, " ")
    .trim();
  return header || `${role} ${lastQualifiedSegment(token.text)}`;
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
const findAtDepth = (tokens, depths, start, text, depth) => {
  for (let index = start; index < tokens.length; index += 1) {
    if (depths[index] === depth && tokens[index].text === text) {
      return index;
    }
  }
  return -1;
};
export {
  analyzeDocument,
  findDefinition,
  keywordHelp,
  nameRange,
  smallestRegion,
  tokenAtPosition,
  tokenRange,
};
