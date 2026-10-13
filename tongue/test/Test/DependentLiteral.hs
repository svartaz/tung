-- host value types, literals, and pure host functions in the dependent path.
module Test.DependentLiteral (group) where

import Control.Monad (forM_)
import Data.Map.Strict qualified as Map
import Test.Compile (compileProject)
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent
import Tung.Dependent.Source (SourceProgram, inferSourceExpression, sourceDefinitions, sourceEnvironment, sourceGlobal)

group :: IO Harness.Group
group = do
  example <- exampleSource "dependent_tales.tung"
  library <- loadLibrary ["ilk/one.tung", "ilk/maybe.tung", "ilk/product.tung", "ilk/two.tung"]
  Harness.group "dependent-literal" (tests (compileWith library "dependent_tales.tung") example ++ numericIndexTests ++ subjectReductionTests)

numericIndexTests :: [Test]
numericIndexTests =
  expectEq
    "numeric constructor indices solve their implicit fields in both directions"
    (Right [True, True, True])
    ( do
        program <- compiled ""
        forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd)
        traverse
          (uncurry (sameNormalIn program))
          [("natural_value natural_read", "1"), ("positive_value positive_read", "2"), ("negative_value negative_read", "2")]
    )
    : [ rejectContaining label "cannot unify" (compiled source)
      | (label, source) <-
          [ ("naught cannot inhabit a successor index", "let bad:0 natural_index ≔ natural_case"),
            ("a positive constructor cannot inhabit a negative index", "let bad:-3 wholetale_index ≔ positive_case")
          ]
      ]
  where
    compiled = compileAs "dependent_numeric_index.tung" . (source ++)
    source =
      """
      ilk natural_index:[ℕ, *] { natural_case:[@n:ℕ, (n heir) natural_index] }
      ilk wholetale_index:[ℤ, *] {
        positive_case:[@n:ℕ, (n overnaught) wholetale_index],
        negative_case:[@n:ℕ, (n heir_undernaught) wholetale_index]
      }
      let natural_value:2 natural_index ≔ natural_case
      let positive_value:+2 wholetale_index ≔ positive_case
      let negative_value:-3 wholetale_index ≔ negative_case
      let natural_read:[@n:ℕ, (n heir) natural_index, ℕ] ≔ {_ ^ n}
      let positive_read:[@n:ℕ, (n overnaught) wholetale_index, ℕ] ≔ {_ ^ n}
      let negative_read:[@n:ℕ, (n heir_undernaught) wholetale_index, ℕ] ≔ {_ ^ n}

      """

tests :: (String -> Either String SourceProgram) -> String -> [Test]
tests compiled example =
  [ computes "integer addition computeth during checking" "+2 + +2" "+4",
    computes "integer arithmetic composeth" "(+7 · +6) offdraw +2" "+40",
    computes "division is euclidean for a undernaught divisor" "+7 deal_leftover -2" "(-3 both +1) some",
    computes "division is euclidean for a undernaught dividend" "-7 deal_leftover +2" "(-4 both +1) some",
    computes "division by naught hath no result" "+5 deal_leftover +0" "(none : (ℤ ∏ ℤ) maybe)",
    computes "a comparison yieldeth yea for true" "+1 ≤ +2" "yea",
    computes "a comparison yieldeth nay for false" "+2 ≍ +3" "nay",
    computes "integers convert to string" "+42 to_string" "'42'",
    computes "float addition computeth" "0.5 ⊕ 0.25" "0.75",
    computes "a float floor is an integer" "-2.5 ⌊" "-3 some",
    expectEq "non-finite floats have no integer floor" (Right [True, True, True]) do
      program <- compiled (example ++ "let deal_float:[float,float,float] ≔ 'deal_float' fremmed\n")
      traverse (\number -> sameNormalIn program ("(" ++ number ++ " deal_float 0.0) ⌊") "(none:ℤ maybe)") ["1.0", "-1.0", "0.0"],
    computes "string yoketh" "'tu' yoke 'ng'" "'tung'",
    computes "string splitteth off its first scalar" "'tung' behead" "(`t both 'ung') some",
    computes "empty string hath no first scalar" "'' behead" "(none : (unicode ∏ string) maybe)",
    computes "a unicode scalar hath a natural code" "`a code" "97",
    computes "unsigned digits are a natural" "2 ⊞ 3" "5",
    computes "natural subtraction stopth at naught" "2 ⊟ 3" "0",
    computes "a natural becometh an integer" "2 to_wholetale" "+2",
    computes "a undernaught integer is no natural" "-1 to_natural" "(none : ℕ maybe)",
    computes "an operation on a variable stayeth neutral" "{n:ℤ ^ n + +0}" "{n:ℤ ^ n + +0}",
    expectEq "a natural is 0 or succeedeth another, and selfcalling on it computeth" (Right True) do
      program <- compiled (example ++ "let double:[n: ℕ, ℕ] ≔ match n { 0 ^ 0, m heir ^ ((m double) heir) heir }\nlet small:[ℕ, string] ≔ { 2 ^ 'two', _ ^ 'other' }\n")
      results <- traverse (\(expression, expected) -> sameNormalIn program expression expected) [("3 double", "6"), ("2 small", "'two'"), ("3 small", "'other'")]
      pure (and results),
    expectEq "the runner readeth a literal as its constructors" (Right (Right 0, "two")) $
      compiled (example ++ "let small:[ℕ, string] ≔ { 2 ^ 'two', _ ^ 'other' }\nlet write:[string, 𝟙 deed] ≔ 'write' fremmed\nlet main:𝟙 deed ≔ (1 heir) small $ write\n")
        >>= (`runSimulated` []),
    expectEq "a type may be chosen by an integer comparison" (Right True) $
      True <$ compiled (example ++ "let six:(+0 by_greatness) ≔ 'six'\n"),
    rejectContaining "the comparison decideth the chosen type" "cannot unify" $
      compiled (example ++ "let wrong:(+0 by_greatness) ≔ +6\n"),
    rejectContaining "a float literal is not an integer" "cannot unify" $
      compiled (example ++ "let wrong:ℤ ≔ 1.5\n"),
    rejectContaining "an unsigned literal is not an integer" "cannot unify" $
      compiled (example ++ "let wrong:ℤ ≔ 1\n"),
    rejectContaining "a comparison yieldeth bookhoard's 𝟚" "requireth a different type" $
      compiled (example ++ "ilk three:* { a: three, b: three, c: three }\nlet bad:[float, float, three] ≔ 'same_float' fremmed\n"),
    expectEq "the runner computeth sheer host functions" (Right (Right 0, "5")) $
      compiled (example ++ "let write:[string, 𝟙 deed] ≔ 'write' fremmed\nlet main:𝟙 deed ≔ (+2 + +3) to_string $ write\n")
        >>= (`runSimulated` [])
  ]
  where
    computes label expression expected = expectEq label (Right True) do
      program <- compiled example
      sameNormalIn program expression expected

subjectReductionTests :: [Test]
subjectReductionTests =
  [ expectEq "a comparison preserveth its higher-universe result" (Right (Global (SymbolId (SourceModule "ilk/two.tung") "yea") [level 1])) do
      program <- hostEncodingProgram
      comparison <- maybe (Left "missing comparison") Right (sourceGlobal program "compare")
      let one = Literal (SymbolId PrimitiveModule "ℤ") (IntegerValue 1)
          term = Apply Explicit (Apply Explicit (Global comparison [level 1]) one) one
      inferred <- infer (sourceEnvironment program) term
      preserve program inferred,
    expectEq "nested maybe and product results retain their checked type" (Right ()) do
      program <- hostEncodingProgram
      inferred <- inferSourceExpression program "+7 deal +2"
      () <$ preserve program inferred,
    expectEq "list results retain their checked type" (Right ()) do
      program <- hostEncodingProgram
      inferred <- inferSourceExpression program "'tu' scalars"
      () <$ preserve program inferred
  ]
  where
    preserve program inferred = do
      let environment = sourceEnvironment program
      normal <- normalise environment (inferredTerm inferred)
      validate environment inferred {inferredTerm = normal}
      pure normal

-- canonical host families allow independent universe parameters; checking a
-- normal form must preserve the original judgement, not specialise its levels.
hostEncodingProgram :: Either String SourceProgram
hostEncodingProgram =
  compileProject
    RootModule
    """
    use ilk/two.tung
    use ilk/maybe.tung
    use ilk/product.tung
    use ilk/list.tung
    let compare:[ℤ,ℤ,𝟚] ≔ 'same_wholetale' fremmed
    let deal:[ℤ,ℤ,(ℤ ∏ ℤ) maybe] ≔ 'deal_leftover_wholetale' fremmed
    let scalars:[string,unicode list] ≔ 'string_to_list' fremmed
    """
    ( Map.fromList
        [ ("ilk/two.tung", "show ilk 𝟚:* { yea:𝟚, nay:𝟚 }"),
          ("ilk/maybe.tung", "show ilk maybe:[α:*,*] { none:α maybe, some:[α,α maybe] }"),
          ("ilk/product.tung", "show ilk ∏:[α:*,β:*,*] { both:[α,β,α ∏ β] }"),
          ("ilk/list.tung", "show ilk list:[α:*,*] { empty:α list, ‥:[α,α list,α list] }")
        ]
    )
