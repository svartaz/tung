-- source declarations exercise the same inductive kernel through elaboration.
module Test.DependentInductiveSource (group) where

import Control.Monad (forM_)
import Data.List (isInfixOf)
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent
import Tung.Dependent.Source (SourceProgram, inferSourceExpression, sourceDefinitions, sourceEnvironment)

group :: IO Harness.Group
group = Harness.group "dependent-inductive-source" tests

tests :: [Test]
tests =
  [ sameNormal "source natural induction computeþ" naturalSource naturalFold "(zero successor) successor",
    expectEq "polymorphic constructors accept ordinary and higher-universe elements" (Right ()) $ do
      program <-
        compile
          ( naturalSource
              ++ listSource
              ++ """
                 let lower:nat list ≔ zero cons @nat (empty @nat)
                 let higher:* list ≔ * cons @* (empty @*)

                 """
          )
      forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd),
    sameNormal "source indexed induction preserveþ the result index" (naturalSource ++ vectorSource) vectorFold vectorOne,
    sameNormal "a constructor index is unified wiþ each constructor's index" (naturalSource ++ vectorSource ++ vectorHead) ("(" ++ vectorOne ++ ") head") "zero",
    expectEq "equal successors have equal predecessors" (Right ()) $
      () <$ compile (naturalSource ++ identitySource ++ "let predecessor:[@a:nat, @b:nat, refl:(a successor) equal @nat (b successor), a equal @nat b] ≔ refl\n"),
    expectEq "zero is not a successor" (Right ()) $
      () <$ compile (naturalSource ++ identitySource ++ "ilk void:* {}\nlet distinct:[zero equal @nat (zero successor), void] ≔ {}\n"),
    sameNormal "a field after a recursive child retaineþ its original dependencies" (naturalSource ++ identitySource ++ vectorProofSource) vectorProofFold vectorProofOne,
    rejectContaining "an indexed constructor cannot inhabit another index" "cannot unify" $ do
      program <-
        compile
          ( naturalSource
              ++ """
                 ilk bool:* { no: bool, yes: bool }
                 ilk tag:[*, *] { natural_tag:nat tag }

                 """
          )
      inferSourceExpression program "(natural_tag:bool tag)",
    sameNormal "source identity transport computeþ on reflexivity" (naturalSource ++ identitySource ++ transportSource) "transport" "{F:[nat, *] ^ {value:(zero F) ^ value}}",
    expectEq "types and constructors share one namespace" (Right [True, True]) $
      traverse
        collision
        [ "let nat ≔ *\n" ++ naturalSource,
          "let zero ≔ *\n" ++ naturalSource
        ],
    rejectContaining "only an ilk or flock can be unbuilt" "cannot be unbuilt" $
      compile (naturalSource ++ "let origin ≔ zero\nlet bad ≔ unbuild origin\n"),
    rejectContaining "a transparent alias cannot hide negative source recursion" "strictly positive" $
      compile
        ( naturalSource
            ++ """
               let negative:[α:*, *] ≔ [α, nat]
               ilk bad:* { make:[value:bad negative, bad] }

               """
        ),
    -- `α` is an index, so a match on `α tagged` is accepted.
    expectEq "a header slot þat a constructor changeþ becomeþ an index" (Right ()) $
      () <$ compile (naturalSource ++ "ilk tagged:[α:*, *] { make:nat tagged }\nlet probe:[@α:*, α tagged, nat] ≔ { make ^ zero }\n"),
    rejectContaining "source constructor results must name their own family" "direct saturated family application" $
      compile (naturalSource ++ "ilk bad:* { make:nat }\n"),
    rejectContaining "local inductive declarations cannot enter a let block" "must be top-level" $
      compile "let outer ≔ (let value ≔ * ilk local:* {} yield value)",
    rejectContaining "a constructor requireþ a written type" "requireþ a type" $
      compile (naturalSource ++ "ilk tag:[nat, *] { missing }\n")
  ]

naturalSource, listSource, vectorSource, vectorProofSource, identitySource, transportSource, vectorHead :: String
naturalSource = "ilk nat:* { zero: nat, successor:[n:nat, nat] }\n"
listSource = "ilk list:[α:*, *] { empty: α list, cons:[head:α, tail:α list, α list] }\n"
vectorSource = "ilk vec:[α:*, [nat, *]] { nil:α vec zero, cons:[n:nat, head:α, tail:α vec n, α vec (n successor)] }\n"
vectorProofSource = "ilk vec_proof:[α:*, [nat, *]] { nil:α vec_proof zero, cons:[n:nat, tail:α vec_proof n, proof:(n equal @nat n), α vec_proof (n successor)] }\n"
identitySource = "ilk equal:[@α:*, x:α, [α, *]] { refl:(x equal @α x) }\n"
vectorHead = "let head:[@α:*, @n:nat, v:α vec (n successor), α] ≔ match v { _ cons a _ ^ a }\n"
transportSource = "let transport:[F:[nat, *], value:zero F, zero F] ≔ {y:nat ^ {proof:(zero equal @nat y) ^ y F}} unbuild equal @nat @zero value zero (refl @nat @zero)\n"

naturalFold, vectorOne, vectorFold, vectorProofOne, vectorProofFold :: String
naturalFold = "{n:nat ^ nat} unbuild nat zero {n:nat ^ {ih:nat ^ ih successor}} ((zero successor) successor)"
vectorOne = "zero cons @nat zero (nil @nat)"
vectorFold = "{n:nat ^ {value:(nat vec n) ^ nat vec n}} unbuild vec @nat (nil @nat) {n:nat ^ {head:nat ^ {tail:(nat vec n) ^ {ih:(nat vec n) ^ n cons @nat head ih}}}} (zero successor) (" ++ vectorOne ++ ")"
vectorProofOne = "zero cons @nat (nil @nat) (refl @nat @zero)"
vectorProofFold = "{n:nat ^ {value:(nat vec_proof n) ^ nat vec_proof n}} unbuild vec_proof @nat (nil @nat) {n:nat ^ {tail:(nat vec_proof n) ^ {ih:(nat vec_proof n) ^ {proof:(n equal @nat n) ^ n cons @nat ih proof}}}} (zero successor) (" ++ vectorProofOne ++ ")"

compile :: String -> Either String SourceProgram
compile = compileAs "inductive_example.tung"

sameNormal :: String -> String -> String -> String -> Test
sameNormal label source actual expected = expectEq label (Right True) $ do
  program <- compile source
  sameNormalIn program actual expected

collision :: String -> Either String Bool
collision source = case compile source of
  Left message -> Right ("top-level name repeateþ" `isInfixOf` message)
  Right _ -> Right False
