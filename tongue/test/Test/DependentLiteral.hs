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
  example <- exampleSource "host_tales.tung"
  library <- loadLibrary ["type/one.tung", "type/optional.tung", "type/and.tung", "type/two.tung"]
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
          [ ("zero cannot inhabit a successor index", "let bad:0 natural_index ≔ natural_case"),
            ("a positive constructor cannot inhabit a negative index", "let bad:-3 integer_index ≔ positive_case")
          ]
      ]
  where
    compiled = compileAs "dependent_numeric_index.tung" . (source ++)
    source =
      """
      type natural_index:[ℕ, *] { natural_case:[@n:ℕ, (n next) natural_index] }
      type integer_index:[ℤ, *] {
        positive_case:[@n:ℕ, (n nonnegative) integer_index],
        negative_case:[@n:ℕ, (n next_negative) integer_index]
      }
      let natural_value:2 natural_index ≔ natural_case
      let positive_value:+2 integer_index ≔ positive_case
      let negative_value:-3 integer_index ≔ negative_case
      let natural_read:[@n:ℕ, (n next) natural_index, ℕ] ≔ {_ ^ n}
      let positive_read:[@n:ℕ, (n nonnegative) integer_index, ℕ] ≔ {_ ^ n}
      let negative_read:[@n:ℕ, (n next_negative) integer_index, ℕ] ≔ {_ ^ n}

      """

tests :: (String -> Either String SourceProgram) -> String -> [Test]
tests compiled example =
  [ computes "integer addition computeth during checking" "+2 + +2" "+4",
    computes "integer arithmetic composeth" "(+7 · +6) subtract +2" "+40",
    computes "division is euclidean for a negative divisor" "+7 divide_leftover -2" "(-3 ⸴ +1) some",
    computes "division is euclidean for a negative dividend" "-7 divide_leftover +2" "(-4 ⸴ +1) some",
    computes "division by zero hath no result" "+5 divide_leftover +0" "(none : (ℤ ∧ ℤ) optional)",
    computes "a comparison yieldeth yea for true" "+1 ≤ +2" "yea",
    computes "a comparison yieldeth nay for false" "+2 ≍ +3" "nay",
    computes "integers convert to string" "+42 to_string" "'42'",
    computes "float addition computeth" "0.5 ⊕ 0.25" "0.75",
    computes "a float floor is an integer" "-2.5 ⌊" "-3 some",
    expectEq "non-finite floats have no integer floor" (Right [True, True, True]) do
      program <- compiled (example ++ "let divide_float:[float,float,float] ≔ 'divide_float' foreign\n")
      traverse (\number -> sameNormalIn program ("(" ++ number ++ " divide_float 0.0) ⌊") "(none:ℤ optional)") ["1.0", "-1.0", "0.0"],
    computes "string joineth" "'tu' join 'ng'" "'tung'",
    computes "string splitteth off its first scalar" "'tung' behead" "(`t ⸴ 'ung') some",
    computes "empty string hath no first scalar" "'' behead" "(none : (unicode ∧ string) optional)",
    computes "a unicode scalar hath a natural code" "`a code" "97",
    computes "unsigned digits are a natural" "2 ⊞ 3" "5",
    computes "natural subtraction stopth at zero" "2 ⊟ 3" "0",
    computes "a natural becometh an integer" "2 to_integer" "+2",
    computes "a negative integer is no natural" "-1 to_natural" "(none : ℕ optional)",
    computes "an operation on a variable stayeth neutral" "{n:ℤ ^ n + +0}" "{n:ℤ ^ n + +0}",
    expectEq "a natural is 0 or succeedeth another, and recursion on it computeth" (Right True) do
      program <- compiled (example ++ "let double:[n: ℕ, ℕ] ≔ match n { 0 ^ 0, m next ^ ((m double) next) next }\nlet small:[ℕ, string] ≔ { 2 ^ 'two', _ ^ 'other' }\n")
      results <- traverse (\(expression, expected) -> sameNormalIn program expression expected) [("3 double", "6"), ("2 small", "'two'"), ("3 small", "'other'")]
      pure (and results),
    expectEq "the runner readeth a literal as its constructors" (Right (Right 0, "two")) $
      compiled (example ++ "let small:[ℕ, string] ≔ { 2 ^ 'two', _ ^ 'other' }\nlet write:[string, 𝟙 effect] ≔ 'write' foreign\nlet main:𝟙 effect ≔ (1 next) small $ write\n")
        >>= (`runSimulated` []),
    expectEq "a type may be chosen by an integer comparison" (Right True) $
      True <$ compiled (example ++ "let six:(+0 by_manyhood) ≔ 'six'\n"),
    rejectContaining "the comparison decideth the chosen type" "cannot unify" $
      compiled (example ++ "let wrong:(+0 by_manyhood) ≔ +6\n"),
    rejectContaining "a float literal is not an integer" "cannot unify" $
      compiled (example ++ "let wrong:ℤ ≔ 1.5\n"),
    rejectContaining "an unsigned literal is not an integer" "cannot unify" $
      compiled (example ++ "let wrong:ℤ ≔ 1\n"),
    rejectContaining "a comparison yieldeth library's 𝟚" "requireth a different type" $
      compiled (example ++ "type three:* { a: three, b: three, c: three }\nlet bad:[float, float, three] ≔ 'equal_float' foreign\n"),
    expectEq "the runner computeth sheer host functions" (Right (Right 0, "5")) $
      compiled (example ++ "let write:[string, 𝟙 effect] ≔ 'write' foreign\nlet main:𝟙 effect ≔ (+2 + +3) to_string $ write\n")
        >>= (`runSimulated` [])
  ]
  where
    computes label expression expected = expectEq label (Right True) do
      program <- compiled example
      sameNormalIn program expression expected

subjectReductionTests :: [Test]
subjectReductionTests =
  [ expectEq "a comparison preserveth its higher-universe result" (Right (Global (SymbolId (SourceModule "type/two.tung") "yea") [level 1])) do
      program <- hostEncodingProgram
      comparison <- maybe (Left "missing comparison") Right (sourceGlobal program "compare")
      let one = Literal (SymbolId PrimitiveModule "ℤ") (IntegerValue 1)
          term = Apply Explicit (Apply Explicit (Global comparison [level 1]) one) one
      inferred <- infer (sourceEnvironment program) term
      preserve program inferred,
    expectEq "nested optional and product results retain their checked type" (Right ()) do
      program <- hostEncodingProgram
      inferred <- inferSourceExpression program "+7 divide +2"
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
    bring type/two.tung
    bring type/optional.tung
    bring type/and.tung
    bring type/list.tung
    let compare:[ℤ,ℤ,𝟚] ≔ 'equal_integer' foreign
    let divide:[ℤ,ℤ,(ℤ ∧ ℤ) optional] ≔ 'divide_leftover_integer' foreign
    let scalars:[string,unicode list] ≔ 'string_to_list' foreign
    """
    ( Map.fromList
        [ ("type/two.tung", "show type 𝟚:* { yea:𝟚, nay:𝟚 }"),
          ("type/optional.tung", "show type optional:[α:*,*] { none:α optional, some:[α,α optional] }"),
          ("type/and.tung", "show type ∧:[α:*,β:*,*] { ⸴:[α,β,α ∧ β] }"),
          ("type/list.tung", "show type list:[α:*,*] { empty:α list, ‥:[α,α list,α list] }")
        ]
    )
