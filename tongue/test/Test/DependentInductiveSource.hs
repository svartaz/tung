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
  [ sameNormal "source natural induction computeth" naturalSource naturalFold "(zero heir) heir",
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
    sameNormal "source indexed induction preserveth the result index" (naturalSource ++ vectorSource) vectorFold vectorOne,
    sameNormal "a constructor index is unified with each constructor's index" (naturalSource ++ vectorSource ++ vectorHead) ("(" ++ vectorOne ++ ") head") "zero",
    expectEq "same successors have same predecessors" (Right ()) $
      () <$ compile (naturalSource ++ identitySource ++ "let predecessor:[@a:nat, @b:nat, refl:(a heir) hath_≍ @nat (b heir), a hath_≍ @nat b] ≔ refl\n"),
    expectEq "zero is not a heir" (Right ()) $
      () <$ compile (naturalSource ++ identitySource ++ "ilk void:* {}\nlet distinct:[zero hath_≍ @nat (zero heir), void] ≔ {}\n"),
    sameNormal "a field after a recursive child retaineth its original dependencies" (naturalSource ++ identitySource ++ vectorProofSource) vectorProofFold vectorProofOne,
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
    sameNormal "source selfness transport computeth on reflexivity" (naturalSource ++ identitySource ++ transportSource) "transport" "{F:[nat, *] ^ {worth:(zero F) ^ worth}}",
    expectEq "types and constructors share one namespace" (Right [True, True]) $
      traverse
        collision
        [ "let nat ≔ *\n" ++ naturalSource,
          "let zero ≔ *\n" ++ naturalSource
        ],
    rejectContaining "only an ilk or flock can be unbuilt" "cannot be unbuilt" $
      compile (naturalSource ++ "let origin ≔ zero\nlet bad ≔ unbuild origin\n"),
    rejectContaining "a transparent alias cannot hide undernaught source selfcalling" "strictly positive" $
      compile
        ( naturalSource
            ++ """
               let undernaught:[α:*, *] ≔ [α, nat]
               ilk bad:* { make:[worth:bad undernaught, bad] }

               """
        ),
    -- `α` is an index, so a match on `α tagged` is accepted.
    expectEq "a header slot that a constructor changeth becometh an index" (Right ()) $
      () <$ compile (naturalSource ++ "ilk tagged:[α:*, *] { make:nat tagged }\nlet probe:[@α:*, α tagged, nat] ≔ { make ^ zero }\n"),
    rejectContaining "source constructor results must name their own family" "direct saturated family application" $
      compile (naturalSource ++ "ilk bad:* { make:nat }\n"),
    rejectContaining "local inductive declarations cannot enter a let block" "must be top-level" $
      compile "let outer ≔ (let worth ≔ * ilk local:* {} yield worth)",
    rejectContaining "a constructor requireth a written type" "requireth a type" $
      compile (naturalSource ++ "ilk tag:[nat, *] { missing }\n")
  ]

naturalSource, listSource, vectorSource, vectorProofSource, identitySource, transportSource, vectorHead :: String
naturalSource = "ilk nat:* { zero: nat, heir:[n:nat, nat] }\n"
listSource = "ilk list:[α:*, *] { empty: α list, cons:[head:α, tail:α list, α list] }\n"
vectorSource = "ilk vec:[α:*, [nat, *]] { nil:α vec zero, cons:[n:nat, head:α, tail:α vec n, α vec (n heir)] }\n"
vectorProofSource = "ilk vec_proof:[α:*, [nat, *]] { nil:α vec_proof zero, cons:[n:nat, tail:α vec_proof n, proof:(n hath_≍ @nat n), α vec_proof (n heir)] }\n"
identitySource = "ilk hath_≍:[@α:*, x:α, [α, *]] { refl:(x hath_≍ @α x) }\n"
vectorHead = "let head:[@α:*, @n:nat, v:α vec (n heir), α] ≔ match v { _ cons a _ ^ a }\n"
transportSource = "let transport:[F:[nat, *], worth:zero F, zero F] ≔ {y:nat ^ {proof:(zero hath_≍ @nat y) ^ y F}} unbuild hath_≍ @nat @zero worth zero (refl @nat @zero)\n"

naturalFold, vectorOne, vectorFold, vectorProofOne, vectorProofFold :: String
naturalFold = "{n:nat ^ nat} unbuild nat zero {n:nat ^ {ih:nat ^ ih heir}} ((zero heir) heir)"
vectorOne = "zero cons @nat zero (nil @nat)"
vectorFold = "{n:nat ^ {worth:(nat vec n) ^ nat vec n}} unbuild vec @nat (nil @nat) {n:nat ^ {head:nat ^ {tail:(nat vec n) ^ {ih:(nat vec n) ^ n cons @nat head ih}}}} (zero heir) (" ++ vectorOne ++ ")"
vectorProofOne = "zero cons @nat (nil @nat) (refl @nat @zero)"
vectorProofFold = "{n:nat ^ {worth:(nat vec_proof n) ^ nat vec_proof n}} unbuild vec_proof @nat (nil @nat) {n:nat ^ {tail:(nat vec_proof n) ^ {ih:(nat vec_proof n) ^ {proof:(n hath_≍ @nat n) ^ n cons @nat ih proof}}}} (zero heir) (" ++ vectorProofOne ++ ")"

compile :: String -> Either String SourceProgram
compile = compileAs "inductive_example.tung"

sameNormal :: String -> String -> String -> String -> Test
sameNormal label source actual expected = expectEq label (Right True) $ do
  program <- compile source
  sameNormalIn program actual expected

collision :: String -> Either String Bool
collision source = case compile source of
  Left message -> Right ("top-level name repeateth" `isInfixOf` message)
  Right _ -> Right False
