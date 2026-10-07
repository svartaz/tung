-- generated and representative programs run to the exact value printed by
-- `yield`; a host exception is a failure, not a rejection.
module Test.Program (group) where

import Control.Exception qualified as Exception
import Control.Monad (replicateM)
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Test.Harness (Group, Test, evaluateSource, integerSource)
import Test.Harness qualified as Harness

group :: IO Group
group = Harness.group "program" (map integerCase integerTerms ++ map languageCase (languagePrograms ++ booleanProductPrograms))

integerCase :: (String, Integer) -> Test
integerCase (source, expected) = safeResult ("generated ℤ " ++ source) ("use ground.tung yield " ++ source) ("eval ok: " ++ integerSource expected)

languageCase :: (String, String, String) -> Test
languageCase (name, source, expected) = safeResult name source expected

safeResult :: String -> String -> String -> Test
safeResult name source expected = do
  outcome <- Exception.try (evaluateSource source Map.empty) :: IO (Either Exception.SomeException String)
  pure $ case outcome of
    Left exception -> Just (name ++ ": host exception: " ++ Exception.displayException exception)
    Right actual
      | actual == expected -> Nothing
      | otherwise -> Just (name ++ ": expected " ++ expected ++ ", got " ++ actual)

integerTerms :: [(String, Integer)]
integerTerms = atoms ++ binary ++ nested
  where
    atom value = (integerSource value, value)
    atoms = map atom [-3, 0, 4, 2 ^ (80 :: Int)]
    operators = [("+", (+)), ("-", (-)), ("×", (*))]
    binary = [combine op left right | op <- operators, left <- atoms, right <- atoms]
    nested =
      [ term
      | outer <- operators,
        inner <- operators,
        term <- [combine outer (combine inner (atom 7) (atom 2)) (atom 3), combine outer (atom 7) (combine inner (atom 2) (atom 3))]
      ]
    combine (operator, operation) (leftSource, left) (rightSource, right) =
      ("(" ++ leftSource ++ " " ++ operator ++ " " ++ rightSource ++ ")", operation left right)

languagePrograms :: [(String, String, String)]
languagePrograms =
  [ ("checked declaration annotations and inferred functions", "use ground.tung let count:* ≔ ℤ let selfness: [@α: *, x: α, α] ≔ x let choose:[@α:*, @β:*, x:α, _:β, α] ≔ x let hath_+: [x:, y:count, count] ≔ x + y let number:count ≔ (let worth ≔ +3 yield worth selfness) let result ≔ number hath_+ (+4 choose @ℤ @text 'ignored') yield result", "eval ok: +7"),
    ("checked record access", "let worth ≔ r{left ≔ +1, right ≔ +2} yield worth.right", "eval ok: +2"),
    ("checked record update", "let worth ≔ r{left ≔ +1, right ≔ +2} yield r{≔ worth, right ≔ +3, - left}", "eval ok: r{right ≔ +3}"),
    ("checked exhaustive match", "ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } yield match nay { yea ^ +1, nay ^ +2 }", "eval ok: +2"),
    ("checked ℤ match", "yield match +1 { +0 ^ +10, +1 ^ +20, _ ^ +30 }", "eval ok: +20"),
    ("checked class evidence", "flock hath_selfness:[a:*, *] { let selfness:[a, a] } bizen:ℤ hath_selfness { let selfness: [x:] ≔ x } yield +7 selfness", "eval ok: +7"),
    ("checked record retaineth unused required evidence", "flock capability:[a:*, *] {} bizen:ℤ capability {} let empty:[@a:*, @:a capability, r{}] ≔ r{} yield empty @ℤ", "eval ok: r{}"),
    ("checked annotated local selfcalling", "use ground.tung yield (let count:[ℕ, ℕ] ≔ { 0 ^ 0, n heir ^ n count } yield 2 count)", "eval ok: 0"),
    ( "checked nested deep selfcalling with repeated scrutinees",
      """
      ilk nat:* { zero:nat, heir:[nat,nat] }
      let +:[ℤ,ℤ,ℤ] ≔ 'eke_integer' fremmed
      let number:[nat,ℤ] ≔ { zero ^ +0, n heir ^ (n number) + +1 }
      let deep:[x:nat,nat] ≔ match x,x {
        zero,_ ^ zero,
        zero heir,_ ^ zero heir,
        (n heir) heir,(m heir) heir ^ (let local:[nat,nat] ≔ {
          zero ^ (m heir) deep,
          zero heir ^ (m heir) deep,
          (k heir) heir ^ (k heir) local
        } yield m local) heir
      }
      yield (((((zero heir) heir) heir) heir) deep) number
      """,
      "eval ok: +4"
    ),
    ("checked annotated initializer seeth its preceding binding", "use ground.tung yield (let worth:ℤ ≔ +1 let worth:ℤ ≔ worth + +1 yield worth)", "eval ok: +2"),
    ("checked binders sharing a declaration's name", "let +:[ℤ, ℤ, ℤ] ≔ 'eke_integer' fremmed let keep:[keep:ℤ, ℤ] ≔ keep let outer:[ℤ, ℤ] ≔ {x ^ (let inner ≔ {inner ^ inner} yield x inner)} let worth ≔ (let worth ≔ +1 yield worth) yield (+1 keep) + (worth outer)", "eval ok: +2"),
    ("checked bizen member calleth sibling", "flock linked:[a:*, *] { let first:[a, a] let second:[a, a] } bizen:ℤ linked { let first: [x:] ≔ x let second: [x:] ≔ x first } yield +7 second", "eval ok: +7"),
    ("checked non-finite floor yieldeth none", "use ground.tung use ilk/maybe.tung let parsed:float maybe ≔ 'Infinity' from_text yield match parsed warp_flat ⌊ { n some ^ n, none ^ +0 }", "eval ok: +0")
  ]

booleanProductPrograms :: [(String, String, String)]
booleanProductPrograms =
  [ ( "checked boolean product " ++ unwords input,
      boolData ++ "yield match " ++ intercalate ", " input ++ " { " ++ cases ++ " }",
      "eval ok: " ++ integerSource expected
    )
  | arity <- [1 .. 3],
    input <- booleanRows arity,
    let rows = booleanRows arity
        expected = foldl (\index value -> 2 * index + if value == "nay" then 1 else 0) (0 :: Int) input
        cases = intercalate ", " [intercalate ", " row ++ " ^ " ++ integerSource result | (row, result) <- zip rows [0 :: Int ..]]
  ]
  where
    boolData = "ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } "
    booleanRows arity = replicateM arity ["yea", "nay"]
