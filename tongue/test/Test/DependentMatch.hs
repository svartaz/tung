-- pattern matching and structural recursion compile to checked eliminators.
module Test.DependentMatch (group) where

import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent.Source (SourceProgram)

group :: IO Harness.Group
group = do
  example <- exampleSource "dependent_match.tung"
  Harness.group "dependent_match" (tests example ++ recursiveArityTests ++ repeatedScrutineeTests)

tests :: String -> [Test]
tests example =
  [ computes "a case function selecteth its row" "yes not" "no",
    computes "';' rows share one result" "yes both no" "no",
    computes "';' alternatives each select the shared result" "no both yes" "no",
    computes "the first matching row winneth" "yes both yes" "yes",
    computes "selfcalling on a direct child computeth" (two ++ " plus " ++ two) four,
    computes "a fixed implicit input stayeth outside the selfcalling" "(>{‥, zero, zero, ∅}) length" two,
    computes "a changing input actth as an accumulator" "(>{‥, zero, zero heir, ∅}) reverse_onto ∅" ">{‥, zero heir, zero, ∅}",
    computes "a function input is passed to each recursive call" "(>{‥, zero, zero heir, ∅}) warp heir" ">{‥, zero heir, (zero heir) heir, ∅}",
    computes "several columns recurse together" (two ++ " same " ++ two) "yes",
    computes "several columns and alternatives" (two ++ " same zero") "no",
    computes "nested patterns select deeper constructors" (two ++ " at_least_two") "yes",
    computes "a wildcard row catcheth shallower values" "(zero heir) at_least_two" "no",
    computes "selfcalling may pass a grandchild and a rebuilt child" ("(" ++ four ++ " heir) fibonacci") ("(" ++ four ++ " heir)"),
    computes "deep selfcalling keepeth an accumulator" "(>{‥, zero, zero, zero, ∅}) pairs zero" "zero heir",
    expectEq "a match result type may depend on the matched worth" (Right True) $
      compiled
        ( example
            ++ """
               let choice:[bool, *] ≔ { yes ^ nat, no ^ bool }
               let pick:[b:bool, b choice] ≔ match b { yes ^ zero, no ^ no }

               """
        )
        >>= \program -> sameNormalIn program "yes pick" "zero",
    expectEq "a case function argument waiteth for a later argument to fix its input" (Right True) $
      compiled (example ++ "let apply_to:[@α:*, @β:*, f:[α, β], a:α, β] ≔ a f\nlet answer ≔ { yes ^ no, no ^ yes } apply_to yes\n")
        >>= \program -> sameNormalIn program "answer" "no",
    expectEq "a computed scrutinee is replaced in the goal by each row's constructor" (Right ()) $
      ()
        <$ compiled
          ( example
              ++ """
                 let constant:[b:bool, bool] ≔ match b { yes ^ no, no ^ no }
                 let law:[b:bool, (b not $ constant) = no] ≔ match b not { yes ^ backbend, no ^ backbend }

                 """
          ),
    expectEq "selfcalling may pass through a function field" (Right True) $
      compiled
        ( example
            ++ """
               ilk tree:* { leaf: tree, node: [[nat, tree], tree] }
               let height:[t: tree, n: nat, nat] ≔ match t { leaf ^ zero, branch node ^ ((n branch) height n) heir }

               """
        )
        >>= \program -> sameNormalIn program "({_ ^ leaf} node) height zero" "zero heir",
    expectEq "indexed branches refine another input before checking its body" (Right [True, True]) do
      program <-
        compiled
          """
          ilk tag:[α:*, *] { integer:ℤ tag, textual:text tag }
          let +:[ℤ, ℤ, ℤ] ≔ 'eke_integer' fremmed
          let choose:[@α:*, label:α tag, x:α, α] ≔ match label {
            integer ^ x + +1,
            textual ^ x
          }
          """
      traverse (uncurry (sameNormalIn program)) [("integer choose +1", "+2"), ("textual choose 'word'", "'word'")],
    rejectContaining "a family must occur strictly positively" "strictly positive" $
      compiled (example ++ "ilk bad:* { make:[[bad, nat], bad] }\n"),
    rejectContaining "a missing constructor is reported" "missing no" $
      compiled (example ++ "let bad:[bool, bool] ≔ { yes ^ no }\n"),
    rejectContaining "a row covered by earlier rows is redundant" "case 3 is redundant" $
      compiled (example ++ "let bad:[bool, bool] ≔ { no ^ yes, yes ^ no, _ ^ yes }\n"),
    rejectContaining "selfcalling on the matched worth is rejected" "must pass a direct child" $
      compiled (example ++ "let loop:[x:nat, nat] ≔ match x { zero ^ zero, n heir ^ (n heir) loop }\n"),
    rejectContaining "selfcalling on a rebuilt matched worth is rejected" "must pass a direct child" $
      compiled (example ++ "let loop:[nat, nat] ≔ { zero ^ zero, zero heir ^ zero, (n heir) heir ^ ((n heir) heir) loop }\n"),
    rejectContaining "a recursive definition needs an annotation" "needs a type annotation" $
      compiled (example ++ "let loop ≔ loop\n"),
    rejectContaining "a recursive name is not a worth" "must only be called" $
      compiled (example ++ "let bad:[x:nat, [nat, nat]] ≔ match x { zero ^ {y ^ y}, n heir ^ bad }\n"),
    rejectContaining "constructor patterns need every explicit field" "needs 1 explicit arguments" $
      compiled (example ++ "let bad:[nat, bool] ≔ { heir ^ yes, zero ^ no }\n"),
    rejectContaining "a constructor function needs an annotation" "needs a type annotation" $
      compiled (example ++ "let bad ≔ { no ^ yes, yes ^ no }\n"),
    expectEq "a constructor index keepeth the constructors that fit it" (Right True) $
      compiled (example ++ tags ++ "let marked:[yes tag, bool] ≔ { mark ^ yes }\n")
        >>= \program -> sameNormalIn program "mark marked" "yes",
    expectEq "an index no constructor fits maketh an empty match" (Right ()) $
      () <$ compiled (example ++ "ilk tag:[bool, *] { mark:yes tag }\nlet none:[no tag, bool] ≔ {}\n"),
    rejectContaining "a row for a constructor that cannot fit is redundant" "case 2 is redundant" $
      compiled (example ++ tags ++ "let bad:[yes tag, bool] ≔ { mark ^ yes, other ^ no }\n"),
    rejectContaining "an index computed by a function cannot be matched" "a variable or a constructor applied to variables" $
      compiled (example ++ tags ++ "let bad:[b:bool, (b not) tag, bool] ≔ { mark ^ yes, other ^ no }\n"),
    rejectContaining "an index a parameter also useth needeth orsetting K" "axiom K" $
      compiled ("let k:[@α:*, @a:α, p:a = a, p = backbend] ≔ match p { backbend ^ backbend }\n")
  ]
  where
    tags = "ilk tag:[bool, *] { mark:yes tag, other:no tag }\n"
    two = "((zero heir) heir)"
    four = "((((zero heir) heir) heir) heir)"
    computes label expression expected = expectEq label (Right True) do
      program <- compiled example
      sameNormalIn program expression expected

recursiveArityTests :: [Test]
recursiveArityTests =
  [ rejectContaining "recursive matches validate written columns" reason $
      compiled ("ilk nat:* { zero:nat, heir:[nat, nat] } let count:[x:nat, nat] ≔ match x { " ++ rows ++ " }")
  | (reason, rows) <-
      [ ("one pattern per scrutinee", "zero, _ ^ zero, n heir, _ ^ n count"),
        ("every case must have the same number of patterns", "zero ^ zero, n heir, _ ^ n count")
      ]
  ]

repeatedScrutineeTests :: [Test]
repeatedScrutineeTests =
  expectEq
    "repeated inputs share patterns, aliases, and recursive descendants"
    (Right (replicate 8 True))
    ( do
        program <- compiled (natural ++ definitions)
        traverse
          (uncurry (sameNormalIn program))
          [ (two ++ " pick", one),
            (two ++ " whole", two),
            (two ++ " count", two),
            (four ++ " deep", two),
            (two ++ " accumulate " ++ one, "(" ++ two ++ " heir)"),
            ("(" ++ one ++ " wrap @zero) extract", one),
            ("+0 literal", "+1"),
            ("+1 literal", "+2")
          ]
    )
    : [ rejectContaining label reason (compiled (natural ++ source))
      | (label, reason, source) <-
          [ ("inconsistent repeated patterns keep their written row selfness", "case 1 is redundant", "let bad:[x:nat,nat] ≔ match x,x { zero,_ heir ^zero, zero,zero ^zero, n heir,m heir ^m }"),
            ("recursive inconsistent patterns keep their written row selfness", "case 1 is redundant", "let bad:[x:nat,nat] ≔ match x,x { zero,_ heir ^zero, zero,zero ^zero, n heir,m heir ^m bad }"),
            ("repeated inputs still bind each row name once", "'n' is bound twice", "let bad:[x:nat,nat] ≔ match x,x { zero,zero ^zero, n heir,n heir ^n bad }"),
            ("every repeated constructor pattern is validated before intersection", "needs 1 explicit arguments", "let bad:[x:nat,nat] ≔ match x,x { zero,zero ^zero, n heir,heir ^n bad }")
          ]
      ]
  where
    one = "(zero heir)"
    two = "(" ++ one ++ " heir)"
    four = "((" ++ two ++ " heir) heir)"
    natural = "ilk nat:* { zero:nat, heir:[nat, nat] }\n"
    definitions =
      """
      let pick:[x:nat, nat] ≔ match x,x {
        zero,zero ^ zero,
        n heir,m heir ^ m
      }
      let whole:[x:nat, nat] ≔ match x,x {
        zero,_ ^ zero,
        _ heir,worth ^ worth
      }
      let count:[x:nat, nat] ≔ match x,x {
        _,zero ^ zero,
        n heir,m heir ^ (m count) heir
      }
      let deep:[x:nat, nat] ≔ match x,x {
        zero,_ ^ zero,
        zero heir,_ ^ zero,
        (n heir) heir,(m heir) heir ^ (m deep) heir
      }
      let accumulate:[x:nat, y:nat, nat] ≔ match y,x,x {
        _,zero,zero ^ y,
        z,n heir,m heir ^ (m accumulate z) heir
      }
      ilk box:* { wrap:[@hidden:nat, worth:nat, box] }
      let extract:[x:box, nat] ≔ match x,x { a wrap,b wrap @h ^ b }
      let literal:[x:ℤ, ℤ] ≔ match x,x {
        +0,_ ^ +1,
        _,+1 ^ +2,
        _,_ ^ +3
      }
      """

compiled :: String -> Either String SourceProgram
compiled = compileAs "dependent_match.tung"
