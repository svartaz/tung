// compiler roles and workspace resolution supply semantic highlighting.
import type { SourceRole } from "./checker.ts";
import { lastQualifiedSegment } from "./syntax.ts";

const tokenTypes = [
  "keyword",
  "namespace",
  "type",
  "typeParameter",
  "class",
  "function",
  "method",
  "variable",
  "parameter",
  "property",
  "enumMember",
  "operator",
  "call",
];
const tokenModifiers = [
  "declaration",
  "defaultLibrary",
  "applied",
  "typeFunction",
];
// parser roles identify syntax. workspace resolution only refineth names whose
// constructor identity cannot be decided from syntax alone.
const buildHighlightRanges = (
  source: string,
  roles: SourceRole[],
  resolveDefinition,
) => {
  // plain terms need no lookup when the file cannot contain visible
  // constructors. these compiler hints avoid eager navigation analysis.
  const needsResolution = roles.some(
    ([, , role, modifiers]) =>
      role === "import" || modifiers.includes("constructor"),
  );
  const lineStarts = [0];
  for (const newline of source.matchAll(/\r\n|\r|\n/g)) {
    lineStarts.push(newline.index + newline[0].length);
  }
  let line = 0;
  const ranges = [];
  for (const [start, end, role, originalModifiers] of roles) {
    // compiler ranges are ordered UTF-16 offsets, matching the lsp encoding.
    while (line + 1 < lineStarts.length && lineStarts[line + 1] <= start)
      line++;
    const token = {
      text: source.slice(start, end),
      offset: start,
      line,
      char: start - lineStarts[line],
    };
    if (token.text === "_" || role === "plain") continue;
    let type = role;
    const modifiers = originalModifiers.filter((modifier) =>
      tokenModifiers.includes(modifier),
    );
    if (["term", "headerPattern", "parameter", "call"].includes(role)) {
      const definition = needsResolution ? resolveDefinition(token) : undefined;
      if (role === "term" || role === "headerPattern") {
        if (definition?.role !== "enumMember") continue;
        type =
          role === "term" && definition.callableConstructor
            ? "function"
            : "enumMember";
      } else if (role === "parameter" && definition?.role === "enumMember") {
        type = "enumMember";
        modifiers.length = 0;
      }
    }
    if (!tokenTypes.includes(type)) continue;
    const name = lastQualifiedSegment(token.text);
    const namespaceLength = token.text.length - name.length;
    if (namespaceLength > 0) {
      ranges.push({
        line: token.line,
        char: token.char,
        length: namespaceLength - 1,
        type: "namespace",
        modifiers: [],
      });
    }
    ranges.push({
      line: token.line,
      char: token.char + namespaceLength,
      length: end - start - namespaceLength,
      type,
      modifiers,
    });
  }
  return ranges.sort((a, b) => a.line - b.line || a.char - b.char);
};
export { buildHighlightRanges, tokenTypes, tokenModifiers };
