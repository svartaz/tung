-- recursion selection useþ checked bindings, including aliases and shadowing.
module Test.DependentRecursion (group) where

import Test.DependentSupport
import Test.Harness (Group, Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent.Source (SourceProgram)

group :: IO Group
group = Harness.group "dependent-recursion" (positiveTests ++ rejectionTests)

positiveTests :: [Test]
positiveTests =
  [ expectEq label (Right True) do
      program <- compile source
      sameNormalIn program actual expected
  | (label, source, actual, expected) <-
      [ ("a lambda may shadow the recursive binding", count "(n count) keep ({z ^ z} {count:[nat,nat] ^ zero count})", two ++ " count", two),
        ("a case variable may shadow the recursive binding", count "(n count) keep (zero {count ^ count})", two ++ " count", two),
        ("a local binding may shadow the recursive binding", count "(let value ≔ n count let count ≔ zero yield value keep count)", two ++ " count", two),
        ("a local initialiser still seeþ the outer recursive binding", count "(let count ≔ n count yield count)", two ++ " count", two),
        ("a direct child's alias denoteþ the same recursive input", count "(let smaller ≔ n yield smaller count)", two ++ " count", two),
        ( "a rebound first child leaveþ the second input structural",
          """
          let right:[x:nat, y:nat, nat] ≔ match x,y {
            zero,_ ^ zero,
            n successor,zero ^ zero,
            n successor,m successor ^ (let n ≔ n successor yield n right m) successor
          }
          """,
          two ++ " right " ++ three,
          three
        ),
        ( "nested recursion retaineþ an outer induction hypothesis",
          count
            """
            (let local:[nat,nat] ≔ {
              zero ^ n count,
              m successor ^ m local
            } yield n local)
            """,
          two ++ " count",
          two
        ),
        ( "nested deep recursion retaineþ an outer memoised hypothesis",
          """
          let deep:[nat,nat] ≔ {
            zero ^ zero,
            zero successor ^ zero successor,
            (n successor) successor ^ (let local:[nat,nat] ≔ {
              zero ^ (n successor) deep,
              zero successor ^ (n successor) deep,
              (m successor) successor ^ (m successor) local
            } yield n local) successor
          }
          """,
          four ++ " deep",
          four
        ),
        ( "overlapping memo records preserve their respective recursive results",
          """
          let deep:[nat,nat] ≔ {
            zero ^ zero,
            zero successor ^ zero successor,
            (n successor) successor ^ match n {
              zero ^ (let inner:[nat,nat] ≔ {
                zero ^ zero successor,
                zero successor ^ zero successor,
                (m successor) successor ^ match m {
                  zero ^ match zero {
                    zero ^ (zero deep) keep (zero inner),
                    _ successor ^ zero
                  },
                  k successor ^ (k inner) successor
                }
              } yield ((zero successor) successor) inner) successor,
              k successor ^ (k deep) successor
            }
          }
          """,
          two ++ " deep",
          "zero successor"
        ),
        ( "a recursive lambda retaineþ its binder annotation",
          "let count:[nat,nat] ≔ {x:nat ^ match x {zero ^ zero, n successor ^ (n count) successor}}",
          two ++ " count",
          two
        )
      ]
  ]

rejectionTests :: [Test]
rejectionTests =
  [ reject label (compile source)
  | (label, source) <-
      [ ("a shadowing value is not the former child", count "(let n ≔ zero yield n count)"),
        ("a recursive lambda cannot ignore a wrong binder annotation", "let count:[nat,nat] ≔ {x:text ^ match x {zero ^ zero, n successor ^ (n count) successor}}"),
        ("a rebuilt matched input is not a descendant", count "(n successor) count"),
        ( "an inner child is not an outer induction hypothesis",
          count
            """
            (let local:[nat,nat] ≔ {
              zero ^ zero,
              m successor ^ (m count) keep (m local)
            } yield n local)
            """
        )
      ]
  ]

count :: String -> String
count body = "let count:[x:nat,nat] ≔ match x { zero ^ zero, n successor ^ (" ++ body ++ ") successor }"

two, three, four :: String
two = "((zero successor) successor)"
three = "(" ++ two ++ " successor)"
four = "(" ++ three ++ " successor)"

compile :: String -> Either String SourceProgram
compile = compileAs "dependent_recursion.tung" . (prefix ++)
  where
    prefix =
      """
      ilk nat:* { zero:nat, successor:[nat,nat] }
      let keep:[x:nat,y:nat,nat] ≔ x

      """
