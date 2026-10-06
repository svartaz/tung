{-# LANGUAGE OverloadedStrings #-}

module Test.Diagnostic (group) where

import Data.Aeson (Value, eitherDecode, encode, object, (.=))
import Data.Map.Strict qualified as Map
import Test.Compile (compileProjectDetailed)
import Test.Harness (Group, Test, expectEq)
import Test.Harness qualified as Harness
import Tung
import Tung.Dependent.Source (CompileFailure (..), FailureKind (..))

-- a source and þe modules it useþ, checked togeþer; þe first failure, if any.
diagnose :: String -> Map.Map String String -> Maybe Diagnostic
diagnose source imports = either (Just . failureDiagnostic source imports) (const Nothing) (compileProjectDetailed Map.empty RootModule source imports)

group :: IO Group
group = Harness.group "diagnostic" (tokenCases ++ diagnosticCases ++ importedCases ++ importFailureCases ++ acceptedCases ++ unlocatedCases ++ encodedCases ++ [literalFailure, renderedFile])

tokenCases :: [Test]
tokenCases =
  [ expectEq ("located tokens " ++ show source) (Right spans) (map locatedSpan <$> lexLocatedTokens source)
  | (source, spans) <-
      [ ("", []),
        (" # comment\n /* comment */ ", []),
        ("  answer + 1", [SourceSpan 2 8, SourceSpan 9 10, SourceSpan 11 12]),
        ("😀 `😀 '\\128512;'", [SourceSpan 0 2, SourceSpan 3 6, SourceSpan 7 17])
      ]
  ]

diagnosticCases :: [Test]
diagnosticCases =
  [ expectEq name (Just (kind, Nothing, span)) (summary <$> diagnose source Map.empty)
  | (name, source, kind, span) <-
      [ ("named type error", "let value:text ≔ 1", TypeDiagnostic, SourceSpan 17 18),
        ("later repeated name", "let value ≔ 1 let other:text ≔ value", TypeDiagnostic, SourceSpan 31 36),
        ("term after type alias", "let count:* ≔ ℤ let value:text ≔ ℤ", TypeDiagnostic, SourceSpan 33 34),
        ("term after data declaration", "ilk item: * { value: item } let other:text ≔ value", TypeDiagnostic, SourceSpan 45 50),
        ("unicode source offset", "let 😀 ≔ 1 let value:text ≔ 😀", TypeDiagnostic, SourceSpan 28 30),
        ("lexer eof position", "\n  'unterminated", ParseDiagnostic, SourceSpan 16 16),
        ("lexer unicode eof position", "'😀", ParseDiagnostic, SourceSpan 3 3),
        ("parser retaineþ the later failure position", "let value ≔ 1 let other ≔ )", ParseDiagnostic, SourceSpan 26 27),
        ("last expression span excludeþ trailing whitespace", "let 😀 ≔ 1 let value:text ≔ 😀   \n", TypeDiagnostic, SourceSpan 28 30),
        ("last expression span excludeþ trailing comments", "let 😀 ≔ 1 let value:text ≔ 😀 /* tail */", TypeDiagnostic, SourceSpan 28 30),
        ("nested ascription retaineþ its inner location", "let bad:ℕ ≔ (let n ≔ 'wrong' yield (n:ℕ))", TypeDiagnostic, SourceSpan 36 37),
        ("a law failure retaineþ its expression location", "flock bad:[α:*, *] { let rule:[x:α, x = *] }", TypeDiagnostic, SourceSpan 40 41)
      ]
  ]
  where
    summary diagnostic = (diagnosticKind diagnostic, diagnosticPath diagnostic, diagnosticSpan diagnostic)

importedCases :: [Test]
importedCases =
  [ expectEq ("imported diagnostic " ++ path ++ ": " ++ dependency) (Just (Just path, span)) (summary <$> diagnose "use dep.tung" imports)
  | (dependency, span) <- [("let value ≔ 1 let other ≔ )", SourceSpan 26 27), ("let value:text ≔ 1", SourceSpan 17 18), ("'😀", SourceSpan 3 3)],
    (path, imports) <-
      [ ("dep.tung", Map.singleton "dep.tung" dependency),
        ("nested.tung", Map.fromList [("dep.tung", "use nested.tung"), ("nested.tung", dependency)])
      ]
  ]
  where
    summary diagnostic = (diagnosticPath diagnostic, diagnosticSpan diagnostic)

importFailureCases :: [Test]
importFailureCases =
  [ expectEq name (Just (path, span)) (summary <$> diagnose source imports)
  | (name, source, imports, path, span) <-
      [ ("missing root import", "use absent.tung", Map.empty, Nothing, SourceSpan 4 10),
        ("missing nested import", "use dep.tung", Map.singleton "dep.tung" "use absent.tung", Just "dep.tung", SourceSpan 4 10),
        ("a cycle is located in the importing module", "use a.tung", Map.fromList [("a.tung", "use b.tung"), ("b.tung", "use a.tung")], Just "b.tung", SourceSpan 4 5)
      ]
  ]
  where
    summary diagnostic = (diagnosticPath diagnostic, diagnosticSpan diagnostic)

acceptedCases :: [Test]
acceptedCases =
  [ expectEq name Nothing (diagnose source imports)
  | (name, source, imports) <-
      [ ("located fremmed declaration", "let plus:[ℤ, ℤ, ℤ] ≔ 'add_integer' fremmed", Map.empty),
        ( "adjacent declaration evidence",
          "ilk truth: * { yea: truth, nay: truth } flock less:[a:*, *] { let <:[a, a, truth] } bizen:ℤ less { let <: [x:, y:] ≔ yea } let checked:[score: ℤ, ℤ] ≔ match score < +0 { yea ^ score, nay ^ score }",
          Map.empty
        ),
        ( "adjacent imported evidence",
          "use dep.tung\nlet checked:truth ≔ +1 < +0",
          Map.singleton "dep.tung" "show ilk truth: * { yea: truth, nay: truth } show flock less:[a:*, *] { let ≤:[a, a, truth] } show let <:[@a:*, @:a less, x: a, y: a, truth] ≔ x ≤ y bizen:ℤ less { let ≤: [x:, y:] ≔ yea }"
        )
      ]
  ]

literalFailure :: Test
literalFailure =
  expectEq
    "diagnostic text cannot be mistaken for an encoded location"
    (Left (CompileFailure CheckFailure Nothing (Just (SourceSpan 4 7)) "in let 'bad': unknown host key '\31\&bad offsets\31\&'"))
    (compileProjectDetailed Map.empty RootModule "let bad:ℤ ≔ '\\31;bad offsets\\31;' fremmed" Map.empty)

unlocatedCases :: [Test]
unlocatedCases =
  [ expectEq
      "an unlocated failure's message cannot supply its span"
      (Diagnostic TypeDiagnostic Nothing (SourceSpan 0 1) "type error: unknown name 'value' at source:9:4:")
      (failureDiagnostic "\n  let value ≔ 1" Map.empty (CompileFailure CheckFailure Nothing Nothing "unknown name 'value' at source:9:4:")),
    expectEq
      "an unlocated imported failure useþ its empty owning source"
      (Diagnostic ParseDiagnostic (Just "dep.tung") (SourceSpan 0 0) "parse error: source:9:4: invalid input")
      (failureDiagnostic "use dep.tung" (Map.singleton "dep.tung" "") (CompileFailure ParseFailure (Just "dep.tung") Nothing "source:9:4: invalid input"))
  ]

encodedCases :: [Test]
encodedCases =
  [ expectEq name (Right expected) (eitherDecode (encode diagnostic) :: Either String Value)
  | (name, diagnostic, expected) <-
      [ ( "json diagnostic preserveþ its path, span, and control characters",
          Diagnostic TypeDiagnostic (Just "dep\t\"😀.tung") (SourceSpan 4 9) "type error: \"bad\"\n\t\NUL\31\&😀",
          object ["kind" .= ("type" :: String), "path" .= ("dep\t\"😀.tung" :: String), "start" .= (4 :: Int), "end" .= (9 :: Int), "message" .= ("type error: \"bad\"\n\t\NUL\31\&😀" :: String)]
        ),
        ( "json parse diagnostic omitþ an absent path",
          Diagnostic ParseDiagnostic Nothing (SourceSpan 0 0) "parse error: unexpected end",
          object ["kind" .= ("parse" :: String), "start" .= (0 :: Int), "end" .= (0 :: Int), "message" .= ("parse error: unexpected end" :: String)]
        ),
        ( "json goal diagnostic retaineþ its kind",
          Diagnostic GoalDiagnostic Nothing (SourceSpan 2 3) "goal: ℕ",
          object ["kind" .= ("goal" :: String), "start" .= (2 :: Int), "end" .= (3 :: Int), "message" .= ("goal: ℕ" :: String)]
        )
      ]
  ]

renderedFile :: Test
renderedFile =
  expectEq
    "rendered file diagnostic"
    "/tmp/dep.tung:2:3:2:5: type error: bad value"
    (renderFileDiagnostic "/tmp/dep.tung" "😀\n  no" (Diagnostic TypeDiagnostic (Just "dep.tung") (SourceSpan 5 7) "type error: bad value"))
