-- lists at every universe use ordinary constructors and structural induction.
module Test.DependentList (group) where

import Control.Monad (forM_)
import Data.Either (isLeft)
import Test.DependentSupport
import Test.Harness (Group, Test, expect, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent
import Tung.Dependent.Source (SourceProgram, normaliseSourceExpression, sourceDefinitions, sourceEnvironment)

group :: IO Group
group = do
  source <- exampleSource "list_family.tung"
  Harness.group "dependent_list" (tests source)

tests :: String -> [Test]
tests source =
  [ checked "one list family storeth values, types, and type constructors" $
      "let values:nat list ≔ "
        ++ values
        ++ "\n"
        ++ "let types:* list ≔ "
        ++ types
        ++ "\n"
        ++ "let constructors:[*, *] list ≔ "
        ++ constructors
        ++ "\n",
    same "supplied and inferred implicit list elements agree" "" values "naught ‥ @nat ((naught next) ‥ @nat (∅ @nat))",
    expectEq "onhang computeth at worth and type levels" (Right [True, True]) $
      traverse
        (uncurry (equalIn (extended "")))
        [ ("(>{‥, naught, ∅}) · (>{‥, naught next, ∅})", values),
          ("(>{‥, nat, ∅}) · (>{‥, bool, ∅})", types)
        ],
    same "warp computeth from the ordinary list eliminator" "" (values ++ " warp next") ">{‥, naught next, (naught next) next, ∅}",
    same "warp can turn type constructors into types" "" (constructors ++ " warp {F:[*, *] ^ nat F}") ">{‥, nat list, nat, ∅}",
    same "fold replaceth constructors by its supplied methods" "" (values ++ " gather naught {_, rest ^ rest next}") "(naught next) next",
    expectEq "open onhang retaineth an induction neutral and a checked type" (Right True) $ do
      program <- extended openAppend
      result <- normaliseSourceExpression program "onhang_empty"
      infer (sourceEnvironment program) result >>= validate (sourceEnvironment program)
      identity <- normaliseSourceExpression program "{xs:nat list ^ xs}"
      pure (eraseLevels result /= eraseLevels identity),
    same "open onhang computeth after its list is substituted" openAppend (values ++ " onhang_empty") values,
    checked "onhang and warp aliases convert inside family indices" $
      indexed
        ++ "let onhanged ≔ (>{‥, nat, ∅}) · (>{‥, bool, ∅})\n"
        ++ "let mapped ≔ row warp {α:* ^ α}\n"
        ++ "let first:onhanged tag ≔ witness\n"
        ++ "let second:mapped tag ≔ witness\n",
    rejected "list indices preserve element order" (indexed ++ "let bad:(>{‥, bool, nat, ∅}) tag ≔ witness\n"),
    rejected "list indices preserve duplicate elements" (indexed ++ "let bad:(>{‥, nat, nat, bool, ∅}) tag ≔ witness\n"),
    rejected "a list cannot mix incompatible element types" "let bad ≔ >{‥, naught, nat, ∅}\n",
    rejected "a list cannot put its universe inside itself" "let bad ≔ (let U ≔ * yield U ‥ @U (∅ @U))\n"
  ]
  where
    extended "" = compile (source ++ naturalSource)
    extended suffix = compile (source ++ naturalSource ++ suffix)
    checked label suffix = expectEq label (Right ()) $ do
      program <- extended suffix
      forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd)
    same label suffix actual expected = expectEq label (Right True) (equalIn (extended suffix) actual expected)
    rejected label suffix = expect label (isLeft (extended suffix))

naturalSource, openAppend, indexed, values, types, constructors :: String
naturalSource =
  """
  ilk nat:* { naught: nat, next:[nat, nat] }
  ilk bool:* { no: bool, yes: bool }

  """
openAppend = "let onhang_empty:[xs:nat list, nat list] ≔ xs · (∅ @nat)\n"
indexed =
  """
  let row:* list ≔ >{‥, nat, bool, ∅}
  ilk tag:[* list, *] { witness:row tag }

  """
values = ">{‥, naught, naught next, ∅}"
types = ">{‥, nat, bool, ∅}"
constructors = ">{‥, list, {α:* ^ α}, ∅ @([*, *])}"

compile :: String -> Either String SourceProgram
compile = compileAs "dependent_list.tung"

equalIn :: Either String SourceProgram -> String -> String -> Either String Bool
equalIn result actual expected = result >>= \program -> sameNormalIn program actual expected
