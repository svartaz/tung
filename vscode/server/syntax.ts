// tokens and bracket structure over the compiler's concrete syntax. the
// compiler lexeth and parseth; this module only placeth its tokens by line.
import generatedLanguageNames from "../generated/language-names.json";
import type { SourceSyntax } from "./checker.ts";

const closeForOpen = new Map([
  ["(", ")"],
  ["[", "]"],
  ["<{", "}"],
  [">{", "}"],
  ["{", "}"],
]);
const closingDelimiters = new Set(closeForOpen.values());

// the compiler's UTF-16 token spans, with lsp line and character positions.
const sourceTokens = (text: string, syntax: SourceSyntax) => {
  const lineStarts = [0];
  for (const newline of text.matchAll(/\r\n|\r|\n/g)) {
    lineStarts.push(newline.index + newline[0].length);
  }
  let line = 0;
  const lineOf = (offset: number) => {
    while (line > 0 && lineStarts[line] > offset) line -= 1;
    while (line + 1 < lineStarts.length && lineStarts[line + 1] <= offset)
      line += 1;
    return line;
  };
  return syntax.tokens.map(([offset, endOffset, kind], index) => {
    const startLine = lineOf(offset);
    const char = offset - lineStarts[startLine];
    const endLine = lineOf(endOffset);
    return {
      index,
      kind,
      text: text.slice(offset, endOffset),
      offset,
      line: startLine,
      char,
      endOffset,
      endLine,
      endChar: endOffset - lineStarts[endLine],
    };
  });
};
type SourceToken = ReturnType<typeof sourceTokens>[number];

// one scan findeth depths and matching delimiters; an unmatched close
// neither pairth nor goeth below depth zero.
const structureCache = new WeakMap();
const tokenStructure = (tokens: SourceToken[]) => {
  const cached = structureCache.get(tokens);
  if (cached) return cached;
  const depths: number[] = [];
  const forward = new Map<number, number>();
  const backward = new Map<number, number>();
  const stack: number[] = [];
  let depth = 0;
  for (const token of tokens) {
    depths.push(depth);
    if (closeForOpen.has(token.text)) {
      depth += 1;
      stack.push(token.index);
    } else if (closingDelimiters.has(token.text)) {
      depth = Math.max(0, depth - 1);
      const open = stack.at(-1);
      if (
        open !== undefined &&
        closeForOpen.get(tokens[open].text) === token.text
      ) {
        stack.pop();
        forward.set(open, token.index);
        backward.set(token.index, open);
      }
    }
  }
  const structure = { depths, forward, backward };
  structureCache.set(tokens, structure);
  return structure;
};
const tokenDepths = (tokens: SourceToken[]) => tokenStructure(tokens).depths;
const bracketPairs = (tokens: SourceToken[]) => tokenStructure(tokens).forward;
const findMatching = (tokens: SourceToken[], openIndex: number) =>
  tokenStructure(tokens).forward.get(openIndex) ?? -1;
const findOpening = (tokens: SourceToken[], closeIndex: number) =>
  tokenStructure(tokens).backward.get(closeIndex) ?? -1;

const lastQualifiedSegment = (name) => {
  const separator = name.lastIndexOf("~");
  return separator > 0 && separator + 1 < name.length
    ? name.slice(separator + 1)
    : name;
};

const useNamespace = (path, alias) => {
  const basename = path.split("/").at(-1) || path;
  return alias || basename.split(".")[0];
};

const languageNames = generatedLanguageNames;

export {
  bracketPairs,
  findMatching,
  findOpening,
  languageNames,
  lastQualifiedSegment,
  sourceTokens,
  tokenDepths,
  useNamespace,
};
export type { SourceToken };
