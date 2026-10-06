-- host value types, literals, and pure host functions in the dependent path.
module Test.DependentLiteral (group) where

import Data.Map.Strict qualified as Map
import Test.Compile (compileProject)
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent
import Tung.Dependent.Source (SourceProgram, inferSourceExpression, sourceEnvironment, sourceGlobal)

group :: IO Harness.Group
group = do
  example <- exampleSource "dependent_numbers.tung"
  library <- loadLibrary ["ilk/one.tung", "ilk/option.tung", "ilk/product.tung", "ilk/two.tung"]
  Harness.group "dependent-literal" (tests (compileWith library "dependent_numbers.tung") example ++ subjectReductionTests)

tests :: (String -> Either String SourceProgram) -> String -> [Test]
tests compiled example =
  [ computes "integer addition computeþ during checking" "+2 + +2" "+4",
    computes "integer arithmetic composeþ" "(+7 × +6) - +2" "+40",
    computes "division is euclidean for a negative divisor" "+7 divide_remainder -2" "(-3 boþ +1) some",
    computes "division is euclidean for a negative dividend" "-7 divide_remainder +2" "(-4 boþ +1) some",
    computes "division by zero hath no result" "+5 divide_remainder +0" "(none : (ℤ ∏ ℤ) option)",
    computes "a comparison yieldeþ yea for true" "+1 ≤ +2" "yea",
    computes "a comparison yieldeþ nay for false" "+2 ≍ +3" "nay",
    computes "integers convert to text" "+42 to_text" "'42'",
    computes "float addition computeþ" "0.5 ⊕ 0.25" "0.75",
    computes "a float floor is an integer" "-2.5 ⌊" "-3 some",
    expectEq "non-finite floats have no integer floor" (Right [True, True, True]) do
      program <- compiled (example ++ "let divide_float:[float,float,float] ≔ 'divide_float' fremmed\n")
      traverse (\number -> sameNormalIn program ("(" ++ number ++ " divide_float 0.0) ⌊") "(none:ℤ option)") ["1.0", "-1.0", "0.0"],
    computes "text joineþ" "'tu' · 'ng'" "'tung'",
    computes "text splitteþ off its first scalar" "'tung' behead" "(`t boþ 'ung') some",
    computes "empty text hath no first scalar" "'' behead" "(none : (unicode ∏ text) option)",
    computes "a unicode scalar hath a natural code" "`a code" "97",
    computes "unsigned digits are a natural" "2 ⊞ 3" "5",
    computes "natural subtraction stopþ at zero" "2 ⊟ 3" "0",
    computes "a natural becomeþ an integer" "2 to_integer" "+2",
    computes "a negative integer is no natural" "-1 to_natural" "(none : ℕ option)",
    computes "an operation on a variable stayeþ neutral" "{n:ℤ ^ n + +0}" "{n:ℤ ^ n + +0}",
    expectEq "a natural is 0 or succeedeþ anoþer, and recursion on it computeþ" (Right True) do
      program <- compiled (example ++ "let double:[n: ℕ, ℕ] ≔ match n { 0 ^ 0, m succeed ^ ((m double) succeed) succeed }\nlet small:[ℕ, text] ≔ { 2 ^ 'two', _ ^ 'other' }\n")
      results <- traverse (\(expression, expected) -> sameNormalIn program expression expected) [("3 double", "6"), ("2 small", "'two'"), ("3 small", "'other'")]
      pure (and results),
    expectEq "the runner readeþ a literal as its constructors" (Right (Right 0, "two")) $
      compiled (example ++ "let small:[ℕ, text] ≔ { 2 ^ 'two', _ ^ 'other' }\nlet write:[text, 𝟙 deed] ≔ 'write' fremmed\nlet main:𝟙 deed ≔ (1 succeed) small $ write\n")
        >>= (`runSimulated` []),
    expectEq "a type may be chosen by an integer comparison" (Right True) $
      True <$ compiled (example ++ "let six:(+0 sized) ≔ 'six'\n"),
    rejectContaining "the comparison decideþ the chosen type" "cannot unify" $
      compiled (example ++ "let wrong:(+0 sized) ≔ +6\n"),
    rejectContaining "a float literal is not an integer" "cannot unify" $
      compiled (example ++ "let wrong:ℤ ≔ 1.5\n"),
    rejectContaining "an unsigned literal is not an integer" "cannot unify" $
      compiled (example ++ "let wrong:ℤ ≔ 1\n"),
    rejectContaining "a comparison yieldeþ bookhoard's 𝟚" "requireþ a different type" $
      compiled (example ++ "ilk three:* { a: three, b: three, c: three }\nlet bad:[float, float, three] ≔ 'equal_float' fremmed\n"),
    expectEq "the runner computeþ pure host functions" (Right (Right 0, "5")) $
      compiled (example ++ "let write:[text, 𝟙 deed] ≔ 'write' fremmed\nlet main:𝟙 deed ≔ (+2 + +3) to_text $ write\n")
        >>= (`runSimulated` [])
  ]
  where
    computes label expression expected = expectEq label (Right True) do
      program <- compiled example
      sameNormalIn program expression expected

subjectReductionTests :: [Test]
subjectReductionTests =
  [ expectEq "a comparison preserveþ its higher-universe result" (Right (Global (SymbolId (SourceModule "ilk/two.tung") "yea") [level 1])) do
      program <- hostEncodingProgram
      comparison <- maybe (Left "missing comparison") Right (sourceGlobal program "compare")
      let one = Literal (SymbolId PrimitiveModule "ℤ") (IntegerValue 1)
          term = Apply Explicit (Apply Explicit (Global comparison [level 1]) one) one
      inferred <- infer (sourceEnvironment program) term
      preserve program inferred,
    expectEq "nested option and product results retain their checked type" (Right ()) do
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
-- normal form must preserve þe original judgement, not specialise its levels.
hostEncodingProgram :: Either String SourceProgram
hostEncodingProgram =
  compileProject
    RootModule
    """
    use ilk/two.tung
    use ilk/option.tung
    use ilk/product.tung
    use ilk/list.tung
    let compare:[ℤ,ℤ,𝟚] ≔ 'equal_integer' fremmed
    let divide:[ℤ,ℤ,(ℤ ∏ ℤ) option] ≔ 'divide_remainder_integer' fremmed
    let scalars:[text,unicode list] ≔ 'text_to_list' fremmed
    """
    ( Map.fromList
        [ ("ilk/two.tung", "show ilk 𝟚:* { yea:𝟚, nay:𝟚 }"),
          ("ilk/option.tung", "show ilk option:[α:*,*] { none:α option, some:[α,α option] }"),
          ("ilk/product.tung", "show ilk ∏:[α:*,β:*,*] { boþ:[α,β,α ∏ β] }"),
          ("ilk/list.tung", "show ilk list:[α:*,*] { empty:α list, ‥:[α,α list,α list] }")
        ]
    )
