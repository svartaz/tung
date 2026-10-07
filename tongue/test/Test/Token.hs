-- literal, escape, comment, keyword, broad-name, and lexical failure coverage.
module Test.Token (group) where

import Data.Char (chr)
import Test.Harness (Group, Test, expectEq, expectPrefix)
import Test.Harness qualified as Harness
import Tung

group :: IO Group
group = Harness.group "token" (map lexCase lexCases ++ map lexError lexErrors ++ scalarCases)

lexCases :: [(String, String, [Token])]
lexCases =
  [ ("record access separateth member names", "person.age", [TIdent "person", TDot, TIdent "age"]),
    ("case separator is syntax", "^", [TMapsTo]),
    ("type parameter prefix is syntax", "@a", [TAt, TIdent "a"]),
    ("kind star is syntax", "*", [TKindStar]),
    ("prefixed names and greek parameters are ordinary names", "*person list~*list @α:*", [TIdent "*person", TIdent "list~*list", TAt, TIdent "α", TColon, TKindStar]),
    ("type composition useth ordinary brace tokens", ">{pair,ℤ,text}:*", [TBraceKeyword ">", TIdent "pair", TComma, TIdent "ℤ", TComma, TIdent "text", TRBrace, TColon, TKindStar]),
    ("kind marker leaveth compound names intact", "@a:* ‥ …* magma~·", [TAt, TIdent "a", TColon, TKindStar, TIdent "‥", TIdent "…*", TIdent "magma~·"]),
    ("the function arrow is an ordinary name", "ℤ → ℤ", [TIdent "ℤ", TIdent "→", TIdent "ℤ"]),
    ("pipe is an ordinary name", "|", [TIdent "|"]),
    ("qualified operator stayeth one name", "list~‥", [TIdent "list~‥"]),
    ("qualified name stayeth one name", "list~empty", [TIdent "list~empty"]),
    ("unicode operator is a name", "≍", [TIdent "≍"]),
    ("minus signs an ℤ", "-1", [TInteger (-1)]),
    ("ℤ literals are arbitrary precision", "+123456789012345678901234567890", [TInteger 123456789012345678901234567890]),
    ("unsigned digits are a natural", "123456789012345678901234567890", [TNatural 123456789012345678901234567890]),
    ("minus signs a float", "-1.25", [TFloat (-1.25)]),
    ("plus signs an ℤ", "+1", [TInteger 1]),
    ("a spaced plus remaineth a name", "+ 1", [TIdent "+", TNatural 1]),
    ("double minus remaineth a name", "--1", [TIdent "--1"]),
    ("list prepend is one name", "‥", [TIdent "‥"]),
    ("backslash is an ordinary name", "\\\\", [TIdent "\\\\"]),
    ("record opener stayeth one token", "r{", [TBraceKeyword "r"]),
    ("anonymous function opener is a brace", "{", [TLBrace]),
    ("left association opener stayeth one token", "<{", [TBraceKeyword "<"]),
    ("right association opener stayeth one token", ">{", [TBraceKeyword ">"]),
    ("separated special openers remain names", "r { < { > {", [TIdent "r", TLBrace, TIdent "<", TLBrace, TIdent ">", TLBrace]),
    ("function brackets and effects are syntax", "[ ] ;", [TLBracket, TRBracket, TSemicolon]),
    ("comment endeth at newline", "1 # hidden\n2", [TNatural 1, TNatural 2]),
    ("block comment is skipped", "1 /* hidden { = */ 2", [TNatural 1, TNatural 2]),
    ("unicode escapes", "`\\n `\\r `\\t `\\' `\\\\", map TUnicode ['\n', '\r', '\t', '\'', '\\']),
    ("unicode decimal code points", "`\\65; `\\23383; `\\128512;", [TUnicode 'A', TUnicode '字', TUnicode '😀']),
    ("raw astral unicode code point", "`😀", [TUnicode '😀']),
    ("text escapes", "'\\n\\r\\t\\'\\\\'", [TText "\n\r\t'\\"]),
    ("text decimal code points", "'\\65;\\23383;'", [TText "A字"]),
    ("unicode text", "'λ字'", [TText "λ字"]),
    ("all keywords", unwords keywordNames, map keywordToken keywordNames)
  ]

lexErrors :: [(String, String)]
lexErrors =
  [ ("path-qualified namespace", "ilk/list~empty"),
    ("unterminated text", "'no"),
    ("unknown text escape", "'\\q'"),
    ("empty unicode escape", "`\\;"),
    ("unterminated decimal unicode escape", "`\\65"),
    ("braced unicode escape", "`\\{65}"),
    ("bare unicode marker", "`"),
    ("unterminated block comment", "1 /* no")
  ]

scalarCases :: [Test]
scalarCases =
  [ let source = wrap ("\\" ++ show value ++ ";")
        name = "unicode scalar boundary " ++ source
     in if valid
          then lexCase (name, source, [token (chr value)])
          else lexError (name, source)
  | (value, valid) <- [(0, True), (55295, True), (55296, False), (57343, False), (57344, True), (65535, True), (65536, True), (1114111, True), (1114112, False)],
    (wrap, token) <- [(('`' :), TUnicode), (\escape -> "'" ++ escape ++ "'", TText . (: []))]
  ]

lexCase :: (String, String, [Token]) -> Test
lexCase (name, source, expected) = case lexTokens source of
  Left message -> expectPrefix name "tokenisation should heir" message
  Right actual -> expectEq name expected actual

lexError :: (String, String) -> Test
lexError (name, source) = case lexTokens source of
  Left _ -> pure Nothing
  Right actual -> pure (Just (name ++ ": unexpectedly tokenised as " ++ show actual))

keywordToken :: String -> Token
keywordToken = \case
  "let" -> TLet
  "show" -> TExport
  "use" -> TImport
  "ilk" -> TType
  "deed" -> TIdent "deed"
  "yield" -> TYield
  "fremmed" -> TForeign
  "flock" -> TClass
  "bizen" -> TInstance
  "match" -> TMatch
  "sorry" -> TSorry
  "orsetting" -> TOrsend
  "unbuild" -> TInduce
  "fall" -> TFall
  name -> error ("missing keyword token in test: " ++ name)
