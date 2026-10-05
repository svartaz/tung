-- lists at every universe use ordinary constructors and structural induction.
module Test.DependentList (group) where

import Control.Monad (forM_)
import Data.Either (isLeft)
import Test.DependentSupport
import Test.Harness (Group, Test, expect, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent
import Tung.Dependent.Source (SourceProgram, normaliseSourceExpression, parseExpression, sourceDefinitions, sourceEnvironment)

group :: IO Group
group = do
  source <- exampleSource "dependent_list.tung"
  Harness.group "dependent_list" (tests source)

tests :: String -> [Test]
tests source =
  [ checked "the ordinary list library containeth kernel-checked definitions" "",
    checked "one list family storeþ values, types, and type constructors" $
      "let values:nat list ≔ "
        ++ values
        ++ "\n"
        ++ "let types:* list ≔ "
        ++ types
        ++ "\n"
        ++ "let constructors:[*, *] list ≔ "
        ++ constructors
        ++ "\n",
    same "supplied and inferred implicit list elements agree" "" values "zero ‥ @nat ((zero successor) ‥ @nat (∅ @nat))",
    expectEq "composition associateþ ordinary applications independently of lists" (Right [True, True]) $
      traverse
        (uncurry (equalIn (extended "ilk pair:[α:*, β:*, *] {}\n")))
        [ ("<{pair, nat, bool, nat}", "(nat pair bool) pair nat"),
          (">{pair, nat, bool, nat}", "nat pair (bool pair nat)")
        ],
    expectEq "composition requireþ two operands and closing braces" [True, True, True] $
      map (isLeft . parseExpression) [">{}", ">{‥, zero}", ">{‥, zero, ∅"],
    expectEq "append computeþ at value and type levels" (Right [True, True]) $
      traverse
        (uncurry (equalIn base))
        [ ("(>{‥, zero, ∅}) · (>{‥, zero successor, ∅})", values),
          ("(>{‥, nat, ∅}) · (>{‥, bool, ∅})", types)
        ],
    same "map computeþ from the ordinary list eliminator" "" (values ++ " map successor") ">{‥, zero successor, (zero successor) successor, ∅}",
    same "map can turn type constructors into types" "" (constructors ++ " map {F:[*, *] ^ nat F}") ">{‥, nat list, nat, ∅}",
    same "fold replaceþ constructors by its supplied methods" "" (values ++ " fold zero {_, rest ^ rest successor}") "(zero successor) successor",
    expectEq "open append retaineth an induction neutral and a checked type" (Right True) $ do
      program <- extended openAppend
      result <- normaliseSourceExpression program "append_empty"
      infer (sourceEnvironment program) result >>= validate (sourceEnvironment program)
      identity <- normaliseSourceExpression program "{xs:nat list ^ xs}"
      pure (eraseLevels result /= eraseLevels identity),
    same "open append computeþ after its list is substituted" openAppend (values ++ " append_empty") values,
    checked "append and map aliases convert inside family indices" $
      indexed
        ++ "let appended ≔ (>{‥, nat, ∅}) · (>{‥, bool, ∅})\n"
        ++ "let mapped ≔ row map {α:* ^ α}\n"
        ++ "let first:appended tag ≔ witness\n"
        ++ "let second:mapped tag ≔ witness\n",
    rejected "list indices preserve element order" (indexed ++ "let bad:(>{‥, bool, nat, ∅}) tag ≔ witness\n"),
    rejected "list indices preserve duplicate elements" (indexed ++ "let bad:(>{‥, nat, nat, bool, ∅}) tag ≔ witness\n"),
    rejected "a list cannot mix incompatible element types" "let bad ≔ >{‥, zero, nat, ∅}\n",
    rejected "a list cannot put its universe inside itself" "let bad ≔ (let U ≔ * yield U ‥ @U (∅ @U))\n"
  ]
  where
    base = compile (source ++ naturalSource)
    extended suffix = compile (source ++ naturalSource ++ suffix)
    checked label suffix = expectEq label (Right ()) $ do
      program <- extended suffix
      forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd)
    same label suffix actual expected = expectEq label (Right True) (equalIn (extended suffix) actual expected)
    rejected label suffix = expect label (isLeft (extended suffix))

naturalSource, openAppend, indexed, values, types, constructors :: String
naturalSource =
  """
  ilk nat:* { zero: nat, successor:[nat, nat] }
  ilk bool:* { no: bool, yes: bool }

  """
openAppend = "let append_empty:[xs:nat list, nat list] ≔ xs · (∅ @nat)\n"
indexed =
  """
  let row:* list ≔ >{‥, nat, bool, ∅}
  ilk tag:[* list, *] { witness:row tag }

  """
values = ">{‥, zero, zero successor, ∅}"
types = ">{‥, nat, bool, ∅}"
constructors = ">{‥, list, {α:* ^ α}, ∅ @([*, *])}"

compile :: String -> Either String SourceProgram
compile = compileAs "dependent_list.tung"

equalIn :: Either String SourceProgram -> String -> String -> Either String Bool
equalIn result actual expected = result >>= \program -> sameNormalIn program actual expected
