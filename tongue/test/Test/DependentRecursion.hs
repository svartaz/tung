-- recursion selection useth checked bindings, including aliases and shadowing.
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
        ("a local binding may shadow the recursive binding", count "(let worth ≔ n count let count ≔ zero yield worth keep count)", two ++ " count", two),
        ("a local initialiser still seeth the outer recursive binding", count "(let count ≔ n count yield count)", two ++ " count", two),
        ("a direct child's alias denoteth the same recursive input", count "(let smaller ≔ n yield smaller count)", two ++ " count", two),
        ( "a rebound first child leaveth the second input structural",
          """
          let right:[x:nat, y:nat, nat] ≔ match x,y {
            zero,_ ^ zero,
            n heir,zero ^ zero,
            n heir,m heir ^ (let n ≔ n heir yield n right m) heir
          }
          """,
          two ++ " right " ++ three,
          three
        ),
        ( "nested selfcalling retaineth an outer induction hypothesis",
          count
            """
            (let local:[nat,nat] ≔ {
              zero ^ n count,
              m heir ^ m local
            } yield n local)
            """,
          two ++ " count",
          two
        ),
        ( "nested deep selfcalling retaineth an outer memoised hypothesis",
          """
          let deep:[nat,nat] ≔ {
            zero ^ zero,
            zero heir ^ zero heir,
            (n heir) heir ^ (let local:[nat,nat] ≔ {
              zero ^ (n heir) deep,
              zero heir ^ (n heir) deep,
              (m heir) heir ^ (m heir) local
            } yield n local) heir
          }
          """,
          four ++ " deep",
          four
        ),
        ( "overlapping memo records preserve their respective recursive results",
          """
          let deep:[nat,nat] ≔ {
            zero ^ zero,
            zero heir ^ zero heir,
            (n heir) heir ^ match n {
              zero ^ (let inner:[nat,nat] ≔ {
                zero ^ zero heir,
                zero heir ^ zero heir,
                (m heir) heir ^ match m {
                  zero ^ match zero {
                    zero ^ (zero deep) keep (zero inner),
                    _ heir ^ zero
                  },
                  k heir ^ (k inner) heir
                }
              } yield ((zero heir) heir) inner) heir,
              k heir ^ (k deep) heir
            }
          }
          """,
          two ++ " deep",
          "zero heir"
        ),
        ( "a recursive lambda retaineth its binder annotation",
          "let count:[nat,nat] ≔ {x:nat ^ match x {zero ^ zero, n heir ^ (n count) heir}}",
          two ++ " count",
          two
        ),
        -- an indexed structural input whose indices are earlier inputs.
        ("recursion may match an indexed value whose index is an implicit input", vector ++ "let length:[@α:*, @n:nat, v:α vec n, nat] ≔ match v { nil ^ zero, _ cons _ t ^ (t length) heir }", pair ++ " length", two),
        ("an indexed recursion's result may mention the index", vector ++ "let warp:[@α:*, @β:*, @n:nat, v:α vec n, f:[α, β], β vec n] ≔ match v { nil ^ nil, k cons a t ^ k cons (a f) (t warp f) }", pair ++ " warp {x ^ x heir}", "(zero heir) cons @nat (zero heir) ((zero cons @nat (zero heir) (nil @nat)))"),
        ("an explicit index input is refined in each branch", vector ++ "let size:[@α:*, n:nat, v:α vec n, nat] ≔ match v { nil ^ n, k cons _ t ^ (k size t) heir }", two ++ " size " ++ pair, two)
      ]
  ]

rejectionTests :: [Test]
rejectionTests =
  [ reject label (compile source)
  | (label, source) <-
      [ ("a shadowing worth is not the former child", count "(let n ≔ zero yield n count)"),
        ("an explicit index argument must be the child's index", vector ++ "let size:[@α:*, n:nat, v:α vec n, nat] ≔ match v { nil ^ n, k cons _ t ^ (zero size t) heir }"),
        ("an index input cannot be matched by a constructor", vector ++ "let size:[@α:*, n:nat, v:α vec n, nat] ≔ { zero, nil ^ zero, _, k cons _ t ^ (k size t) heir }"),
        ("a recursive lambda cannot ignore a wrong binder annotation", "let count:[nat,nat] ≔ {x:text ^ match x {zero ^ zero, n heir ^ (n count) heir}}"),
        ("a rebuilt matched input is not a descendant", count "(n heir) count"),
        ( "an inner child is not an outer induction hypothesis",
          count
            """
            (let local:[nat,nat] ≔ {
              zero ^ zero,
              m heir ^ (m count) keep (m local)
            } yield n local)
            """
        )
      ]
  ]

count :: String -> String
count body = "let count:[x:nat,nat] ≔ match x { zero ^ zero, n heir ^ (" ++ body ++ ") heir }"

vector, pair :: String
vector = "ilk vec:[α:*, [nat, *]] { nil:α vec zero, cons:[n:nat, head:α, tail:α vec n, α vec (n heir)] }\n"
pair = "((zero heir) cons @nat zero (zero cons @nat zero (nil @nat)))"

two, three, four :: String
two = "((zero heir) heir)"
three = "(" ++ two ++ " heir)"
four = "(" ++ three ++ " heir)"

compile :: String -> Either String SourceProgram
compile = compileAs "dependent_selfcalling.tung" . (prefix ++)
  where
    prefix =
      """
      ilk nat:* { zero:nat, heir:[nat,nat] }
      let keep:[x:nat,y:nat,nat] ≔ x

      """
