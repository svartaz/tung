-- source declarations exercise the same inductive kernel through elaboration.
module Test.DependentInductiveSource (group) where

import Control.Monad (forM_)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent
import Tung.Dependent.Source (SourceProgram, inferSourceExpression, sourceDefinitions, sourceEnvironment)

group :: IO Harness.Group
group = do
  mutual <- exampleSource "mutual.tung"
  nested <- exampleSource "nested.tung"
  Harness.group "dependent-inductive-source" (tests ++ mutualTests mutual ++ nestedTests nested)

tests :: [Test]
tests =
  [ sameNormal "source natural induction computeth" naturalSource naturalFold "(zero next) next",
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
      () <$ compile (naturalSource ++ identitySource ++ "let predecessor:[@a:nat, @b:nat, refl:(a next) hath_≍ @nat (b next), a hath_≍ @nat b] ≔ refl\n"),
    expectEq "zero is not a successor" (Right ()) $
      () <$ compile (naturalSource ++ identitySource ++ "type void:* {}\nlet distinct:[zero hath_≍ @nat (zero next), void] ≔ {}\n"),
    sameNormal "a field after a recursive child retaineth its original dependencies" (naturalSource ++ identitySource ++ vectorProofSource) vectorProofFold vectorProofOne,
    rejectContaining "an indexed constructor cannot inhabit another index" "cannot unify" $ do
      program <-
        compile
          ( naturalSource
              ++ """
                 type bool:* { no: bool, yes: bool }
                 type tag:[*, *] { natural_tag:nat tag }

                 """
          )
      inferSourceExpression program "(natural_tag:bool tag)",
    sameNormal "source identity throughbear computeth on reflexivity" (naturalSource ++ identitySource ++ transportSource) "throughbear" "{F:[nat, *] ^ {value:(zero F) ^ value}}",
    expectEq "types and constructors share one namespace" (Right [True, True]) $
      traverse
        collision
        [ "let nat ≔ *\n" ++ naturalSource,
          "let zero ≔ *\n" ++ naturalSource
        ],
    rejectContaining "only a type or class can be unbuilt" "cannot be unbuilt" $
      compile (naturalSource ++ "let origin ≔ zero\nlet bad ≔ unbuild origin\n"),
    rejectContaining "a transparent alias cannot hide negative source recursion" "strictly positive" $
      compile
        ( naturalSource
            ++ """
               let negative:[α:*, *] ≔ [α, nat]
               type bad:* { make:[value:bad negative, bad] }

               """
        ),
    -- `α` is an index, so a match on `α tagged` is accepted.
    expectEq "a header slot that a constructor changeth becometh an index" (Right ()) $
      () <$ compile (naturalSource ++ "type tagged:[α:*, *] { make:nat tagged }\nlet probe:[@α:*, α tagged, nat] ≔ { make ^ zero }\n"),
    rejectContaining "source constructor results must name their own family" "direct saturated family application" $
      compile (naturalSource ++ "type bad:* { make:nat }\n"),
    rejectContaining "local inductive declarations cannot enter a let block" "must be top-level" $
      compile "let outer ≔ (let value ≔ * type local:* {} yield value)",
    rejectContaining "a constructor requireth a written type" "requireth a type" $
      compile (naturalSource ++ "type tag:[nat, *] { missing }\n")
  ]

mutualTests :: String -> [Test]
mutualTests example =
  expectEq
    "mutual eliminators compute sibling and function-field hypotheses"
    (Right (replicate 10 True))
    ( do
        basic <- compile (example ++ deep ++ "type unit: * { only: unit }\nlet empty_record:[even,unit] ≔ {_ ^ only}\n")
        basicResults <- traverse (uncurry (sameNormalIn basic)) [("(" ++ evenTwo ++ ") count_even", "2"), ("(zero_even from_even) count_odd", "1"), ("(zero_even from_even) parent", "zero_even"), ("(((" ++ evenTwo ++ ") from_even) from_odd) deep", "2"), ("zero_even empty_record", "only")]
        parameterised <- compile parameterisedSource
        parameterisedResults <-
          traverse
            (uncurry (sameNormalIn parameterised))
            [ ("(+7 node {_ ^ empty}) probe", "1"),
              ("(* node @* {_ ^ empty}) probe", "1"),
              ("((+7 node {_ ^ empty}) link ((+8 node {_ ^ empty}) link empty)) length", "2")
            ]
        indexed <- compile indexedSource
        indexedResult <- sameNormalIn indexed "1 depth (0 to_one (0 to_two initial))" "2"
        reversed <- compile (unlines (reverse mutualDeclarations) ++ "let parent:[odd, even] ≔ { e from_even ^ e }\n")
        reversedResult <- sameNormalIn reversed "(zero_even from_even) parent" "zero_even"
        pure (basicResults ++ parameterisedResults ++ [indexedResult, reversedResult])
    )
    : ( do
          actual <- Harness.evaluateSource (indexedSource ++ "yield 1 depth (0 to_one (0 to_two initial))") Map.empty
          expectEq "the runner dispatcheth mutual hypotheses across distinct index telescopes" "eval ok: 2" actual
      )
    : ( do
          actual <- Harness.evaluateSource (example ++ deep ++ "yield (((" ++ evenTwo ++ ") from_even) from_odd) deep") Map.empty
          expectEq "the runner followeth descendants across a mutual family" "eval ok: 2" actual
      )
    : reject "an auxiliary unit result cannot justify a sibling call" (compile (example ++ "type unit: * { only: unit }\nlet bad:[even,unit] ≔ { zero_even ^ only, o from_odd ^ o bad }"))
    : [ rejectContaining label reason (compile source)
      | (label, reason, source) <-
          [ ("a sibling family cannot occur negatively", "strictly positive", "type a:* { make:[[b, ℕ], a] }\ntype b:* { wrap:[a, b] }"),
            ("an alias cannot hide a negative sibling occurrence", "strictly positive", "let negative:[α:*, *] ≔ [α, ℕ]\ntype a:* { make:[b negative, a] }\ntype b:* { wrap:[a, b] }"),
            ("cross-family recursive lets remain a declaration cycle", "declaration cycle", example ++ "let walk_even:[even, ℕ] ≔ { zero_even ^ 0, o from_odd ^ o walk_odd }\nlet walk_odd:[odd, ℕ] ≔ { e from_even ^ e walk_even }"),
            ("a sibling child cannot be passed to the same recursive function", "direct child", example ++ "let bad:[even, ℕ] ≔ { zero_even ^ 0, o from_odd ^ o bad }"),
            ("quantified inputs cannot turn a sibling hypothesis into recursion", "direct child", example ++ "let bad:[v:even, change:[ℕ, ℕ], ℕ] ≔ match v { zero_even ^ 0, o from_odd ^ o bad change }")
          ]
      ]
  where
    evenTwo = "(zero_even from_even) from_odd"
    deep = "let deep:[even, ℕ] ≔ { zero_even ^ 0, (e from_even) from_odd ^ (e deep) next }\n"
    mutualDeclarations = ["type even:* { zero_even:even, from_odd:[odd, even] }", "type odd:* { from_even:[even, odd] }"]
    parameterisedSource =
      """
      type branch:[α:*, *] { node:[value:α, children:[ℕ, α forest], α branch] }
      type forest:[α:*, *] { empty:α forest, link:[first:α branch, leftover:α forest, α forest] }
      let probe:[@α:*, α branch, ℕ] ≔
        {_:α branch ^ ℕ} unbuild branch @α {_:α forest ^ ℕ}
          {value:α ^ {children:[ℕ, α forest] ^ {below:[ℕ, ℕ] ^ (0 below) next}}}
          0
          {first:α branch ^ {first_below:ℕ ^ {leftover:α forest ^ {leftover_below:ℕ ^ first_below}}}}
      let length:[@α:*, α forest, ℕ] ≔ {
        empty ^ 0,
        _ link leftover ^ (leftover length) next
      }

      """
    indexedSource =
      """
      type one_index:[ℕ, *] { initial:0 one_index, to_one:[n:ℕ, p:n two_index n, (n next) one_index] }
      type two_index:[ℕ, ℕ, *] { to_two:[n:ℕ, p:n one_index, n two_index n] }
      let depth:[n:ℕ, n one_index, ℕ] ≔
        {n:ℕ ^ {_:n one_index ^ ℕ}} unbuild one_index
          {n:ℕ ^ {m:ℕ ^ {_:n two_index m ^ ℕ}}}
          0
          {n:ℕ ^ {p:n two_index n ^ {below:ℕ ^ below next}}}
          {n:ℕ ^ {p:n one_index ^ {below:ℕ ^ below next}}}
          n

      """

nestedTests :: String -> [Test]
nestedTests example =
  [ expectEq "nested induction, patterns, and automatic descendants compute" (Right (replicate 6 True)) $ do
      program <- compile example
      traverse (uncurry (sameNormalIn program)) [("leaf count", "1"), ("fork count", "3"), ("fork first", "leaf"), ("fork children", "leaf ‥ @rose (leaf ‥ @rose (empty @rose))"), ("leaf height", "1"), ("fork height", "2")],
    do
      actual <- Harness.evaluateSource (example ++ "\nyield fork count") Map.empty
      expectEq "the runner executes the same nested induction rules" "eval ok: 3" actual,
    do
      actual <- Harness.evaluateSource (example ++ "\nyield fork height") Map.empty
      expectEq "the runner followeth children through ordinary containers" "eval ok: 2" actual,
    expectEq "nested mutual root declarations retain ordinary list fields" (Right ()) $
      () <$ compile (listSource ++ "type a:* { make:[b list, a] }\ntype b:* { wrap:[a, b] }"),
    expectEq "container aliases expose nested occurrences" (Right ()) $
      () <$ compile (listSource ++ "let children:[α:*, *] ≔ α list\ntype rose:* { node:[rose children, rose] }"),
    expectEq "automatic recursion may use the second container parameter" (Right True) $ do
      program <- compile "type pair:[α:*, β:*, *] { both:[α, β, α pair β] }\ntype tree:* { tip:tree, node:[ℕ pair tree, tree] }\nlet depth:[tree,ℕ] ≔ { tip ^ 0, (_ both t) node ^ (t depth) next }"
      sameNormalIn program "((0 both tip) node) depth" "1",
    expectEq "distinct nested specialisations sharing constructor identities compute" (Right (replicate 4 True)) $ do
      program <- compile (listSource ++ layered)
      traverse
        (uncurry (sameNormalIn program))
        [ ("((empty @(tree list)) node) count", "1"),
          ("(((((empty @(tree list)) node) cons @tree (empty @tree)) cons @(tree list) (empty @(tree list))) node) count", "2"),
          ("((empty @(tree list)) node) depth", "1"),
          ("(((((empty @(tree list)) node) cons @tree (empty @tree)) cons @(tree list) (empty @(tree list))) node) depth", "2")
        ],
    expectEq "shared parameters and higher universes survive nested restoration and recursion" (Right [True, True]) $ do
      program <-
        compile
          ( listSource
              ++ """
                 type tree:[α:*, *] { tip:[α, α tree], node:[(α tree) list, α tree] }
                 let leaf:* tree ≔ * tip @*
                 let sample:* tree ≔ (leaf cons @(* tree) (empty @(* tree))) node @*
                 let keep:[@α:*, α tree, α tree] ≔ {x ^ x}
                 let depth:[@α:*, α tree, ℕ] ≔ {
                   _ tip ^ 0,
                   empty node ^ 1,
                   (first cons _) node ^ (first depth) next
                 }
                 """
          )
      traverse (uncurry (sameNormalIn program)) [("sample keep @*", "sample"), ("sample depth @*", "1")],
    sameNormal "positive container function fields retain pointwise induction" functions "(({_ ^ tip} hold @tree) node) count" "1"
  ]
    ++ [ rejectContaining label reason (compile source)
       | (label, reason, source) <-
           [ ("negative container parameters are not certified", "strictly positive", "type consumer:[α:*, *] { hold:[[α, ℕ], α consumer] }\ntype bad:* { make:[bad consumer, bad] }"),
             ("an abstract container cannot claim positivity", "direct saturated", "type bad:[f:[*, *], *] { make:[(f bad) f, f bad] }"),
             ("nested recursive parameters cannot change", "uniform", listSource ++ "type bad:[α:*, *] { make:[(ℕ bad) list, α bad] }"),
             ("nested container arguments cannot use a constructor field", "constructor-local", "type container:[α:*, n:ℕ, *] { hold:[α, α container n] }\ntype bad:* { make:[n:ℕ, bad container n, bad] }")
           ]
       ]
    ++ [ rejectContaining label "direct child of the matched input" (compile (example ++ source))
       | (label, source) <-
           [ ("nested evidence cannot justify the whole input", "let bad:[v:rose,ℕ] ≔ match v { empty node ^ 0, (_ ‥ _) node ^ v bad }"),
             ("nested evidence cannot justify the reconstructed root", "let bad:[rose,ℕ] ≔ { empty node ^ 0, (x ‥ leftover) node ^ ((x ‥ @rose leftover) node) bad }"),
             ("nested evidence cannot justify an unrelated input", "let bad:[v:rose,other:rose,ℕ] ≔ match v { empty node ^ 0, (_ ‥ _) node ^ other bad other }"),
             ( "a generic list helper cannot inherit outer descendant evidence",
               """
               let bad:[rose,ℕ] ≔ { xs node ^
                 (let sum:[rose list,ℕ] ≔ {
                   empty ^ 0,
                   first ‥ leftover ^ (first bad) add (leftover sum)
                 } yield xs sum)
               }
               """
             )
           ]
       ]
  where
    functions =
      """
      type thunk:[α:*, *] { hold:[[ℕ, α], α thunk] }
      type tree:* { tip:tree, node:[tree thunk, tree] }
      let count:[tree, ℕ] ≔
        {_:tree ^ ℕ} unbuild tree {_:tree thunk ^ ℕ}
          0 {stored:tree thunk ^ {below:ℕ ^ below next}}
          {call:[ℕ, tree] ^ {below:[ℕ, ℕ] ^ 0 below}}

      """
    layered =
      """
      type tree:* { node:[(tree list) list, tree] }
      let depth:[tree,ℕ] ≔ {
        empty node ^ 1,
        (empty cons _) node ^ 1,
        ((first cons _) cons _) node ^ (first depth) next
      }
      let count:[tree, ℕ] ≔
        {_:tree ^ ℕ} unbuild tree
          {_: (tree list) list ^ ℕ} {_:tree list ^ ℕ}
          {xs:(tree list) list ^ {below:ℕ ^ below next}}
          0
          {first:tree list ^ {first_below:ℕ ^ {leftover:(tree list) list ^ {leftover_below:ℕ ^ first_below add leftover_below}}}}
          0
          {first:tree ^ {first_below:ℕ ^ {leftover:tree list ^ {leftover_below:ℕ ^ first_below add leftover_below}}}}
      let add:[n:ℕ, m:ℕ, ℕ] ≔
        {_:ℕ ^ ℕ} unbuild ℕ m {_:ℕ ^ {below:ℕ ^ below next}} n

      """

naturalSource, listSource, vectorSource, vectorProofSource, identitySource, transportSource, vectorHead :: String
naturalSource = "type nat:* { zero: nat, next:[n:nat, nat] }\n"
listSource = "type list:[α:*, *] { empty: α list, cons:[head:α, tail:α list, α list] }\n"
vectorSource = "type vec:[α:*, [nat, *]] { nil:α vec zero, cons:[n:nat, head:α, tail:α vec n, α vec (n next)] }\n"
vectorProofSource = "type vec_proof:[α:*, [nat, *]] { nil:α vec_proof zero, cons:[n:nat, tail:α vec_proof n, proof:(n hath_≍ @nat n), α vec_proof (n next)] }\n"
identitySource = "type hath_≍:[@α:*, x:α, [α, *]] { refl:(x hath_≍ @α x) }\n"
vectorHead = "let head:[@α:*, @n:nat, v:α vec (n next), α] ≔ match v { _ cons a _ ^ a }\n"
transportSource = "let throughbear:[F:[nat, *], value:zero F, zero F] ≔ {y:nat ^ {proof:(zero hath_≍ @nat y) ^ y F}} unbuild hath_≍ @nat @zero value zero (refl @nat @zero)\n"

naturalFold, vectorOne, vectorFold, vectorProofOne, vectorProofFold :: String
naturalFold = "{n:nat ^ nat} unbuild nat zero {n:nat ^ {ih:nat ^ ih next}} ((zero next) next)"
vectorOne = "zero cons @nat zero (nil @nat)"
vectorFold = "{n:nat ^ {value:(nat vec n) ^ nat vec n}} unbuild vec @nat (nil @nat) {n:nat ^ {head:nat ^ {tail:(nat vec n) ^ {ih:(nat vec n) ^ n cons @nat head ih}}}} (zero next) (" ++ vectorOne ++ ")"
vectorProofOne = "zero cons @nat (nil @nat) (refl @nat @zero)"
vectorProofFold = "{n:nat ^ {value:(nat vec_proof n) ^ nat vec_proof n}} unbuild vec_proof @nat (nil @nat) {n:nat ^ {tail:(nat vec_proof n) ^ {ih:(nat vec_proof n) ^ {proof:(n hath_≍ @nat n) ^ n cons @nat ih proof}}}} (zero next) (" ++ vectorProofOne ++ ")"

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
