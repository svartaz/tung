-- generated and representative programs run to the exact value printed by
-- `yield`; a host exception is a failure, not a rejection.
module Test.Program (group) where

import Control.Exception qualified as Exception
import Control.Monad (replicateM)
import Data.List (intercalate, isPrefixOf)
import Data.Map.Strict qualified as Map
import Test.DependentSupport (Library, compileWith, loadLibrary, runSimulated)
import Test.Harness (Group, Test, evaluateSource, expectEq, integerSource)
import Test.Harness qualified as Harness

group :: IO Group
group = do
  library <- loadLibrary ["often.tung", "effect/fallible.tung", "type/hade.tung"]
  Harness.group
    "program"
    ( map integerCase integerTerms
        ++ map languageCase (languagePrograms ++ booleanProductPrograms ++ dictionaryPrograms)
        ++ map importCase importPrograms
        ++ map (effectCase library) effectPrograms
        ++ map (layeredCase library) layeredPrograms
        ++ map lawCase lawPrograms
    )

integerCase :: (String, Integer) -> Test
integerCase (source, expected) = safeResult ("generated ℤ " ++ source) ("bring often.tung yield " ++ source) ("eval ok: " ++ integerSource expected)

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
integerTerms = binary ++ nested
  where
    atom value = (integerSource value, value)
    boundaries = [(-3, 4), (0, -3), (4, 0), (2 ^ (80 :: Int), 2 ^ (80 :: Int))]
    operators = [("+", (+)), ("-+", flip (-)), ("·", (*))]
    binary = [combine op (atom left) (atom right) | op <- operators, (left, right) <- boundaries]
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
  [ ("checked declaration annotations and inferred functions", "bring often.tung let count:* ≔ ℤ let identity: [@α: *, x: α, α] ≔ x let choose:[@α:*, @β:*, x:α, _:β, α] ≔ x let hath_+: [x:, y:count, count] ≔ x + y let tale:count ≔ (let value ≔ +3 yield value identity) let outcome ≔ tale hath_+ (+4 choose @ℤ @string 'ignored') yield outcome", "eval ok: +7"),
    ("checked field access", "type pair: * { pair_of: [left: ℤ, right: ℤ, pair] } let value ≔ +1 pair_of +2 yield value.right", "eval ok: +2"),
    ("checked exhaustive match", "type 𝟚: * { yea: 𝟚, nay: 𝟚 } yield match nay { yea ^ +1, nay ^ +2 }", "eval ok: +2"),
    ("checked ℤ match", "yield match +1 { +0 ^ +10, +1 ^ +20, _ ^ +30 }", "eval ok: +20"),
    ("checked class evidence", "class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x } yield +7 identity", "eval ok: +7"),
    ("checked value retaineth unused required evidence", "type unit: * { only: unit } class capability:[a:*, *] {} bizen:ℤ capability {} let empty:[@a:*, @:a capability, unit] ≔ only yield empty @ℤ", "eval ok: only"),
    ("checked annotated local recursion", "bring often.tung yield (let count:[ℕ, ℕ] ≔ { 0 ^ 0, n next ^ n count } yield 2 count)", "eval ok: 0"),
    ( "checked nested deep recursion with repeated scrutinees",
      """
      type nat:* { zero:nat, next:[nat,nat] }
      let +:[ℤ,ℤ,ℤ] ≔ 'add_integer' foreign
      let tale:[nat,ℤ] ≔ { zero ^ +0, n next ^ (n tale) + +1 }
      let deep:[x:nat,nat] ≔ match x,x {
        zero,_ ^ zero,
        zero next,_ ^ zero next,
        (n next) next,(m next) next ^ (let local:[nat,nat] ≔ {
          zero ^ (m next) deep,
          zero next ^ (m next) deep,
          (k next) next ^ (k next) local
        } yield m local) next
      }
      yield (((((zero next) next) next) next) deep) tale
      """,
      "eval ok: +4"
    ),
    ("checked annotated initializer seeth its preceding binding", "bring often.tung yield (let value:ℤ ≔ +1 let value:ℤ ≔ value + +1 yield value)", "eval ok: +2"),
    ("checked binders sharing a declaration's name", "let +:[ℤ, ℤ, ℤ] ≔ 'add_integer' foreign let keep:[keep:ℤ, ℤ] ≔ keep let outer:[ℤ, ℤ] ≔ {x ^ (let inner ≔ {inner ^ inner} yield x inner)} let value ≔ (let value ≔ +1 yield value) yield (+1 keep) + (value outer)", "eval ok: +2"),
    ("checked bizen member calleth sibling", "class linked:[a:*, *] { let first:[a, a] let second:[a, a] } bizen:ℤ linked { let first: [x:] ≔ x let second: [x:] ≔ x first } yield +7 second", "eval ok: +7"),
    ("checked non-finite floor yieldeth none", "bring often.tung bring type/optional.tung let parsed:float optional ≔ 'Infinity' from_string yield match parsed bind ⌊ { n some ^ n, none ^ +0 }", "eval ok: +0")
  ]

booleanProductPrograms :: [(String, String, String)]
booleanProductPrograms =
  [ ( "checked boolean product " ++ unwords input,
      boolData ++ "yield match " ++ intercalate ", " input ++ " { " ++ cases ++ " }",
      "eval ok: " ++ integerSource expected
    )
  | input <- booleanRows 3,
    let rows = booleanRows 3
        expected = foldl (\index value -> 2 * index + if value == "nay" then 1 else 0) (0 :: Int) input
        cases = intercalate ", " [intercalate ", " row ++ " ^ " ++ integerSource result | (row, result) <- zip rows [0 :: Int ..]]
  ]
  where
    boolData = "type 𝟚: * { yea: 𝟚, nay: 𝟚 } "
    booleanRows arity = replicateM arity ["yea", "nay"]

-- each law's two sides are evaluated over every small input, and the printed
-- lists must agree. a mismatch printeth the generated source.
lawCase :: (String, String, String) -> Test
lawCase (name, left, right) = do
  outcomes <- traverse (\source -> Exception.try (evaluateSource source Map.empty)) [left, right] :: IO [Either Exception.SomeException String]
  pure $ case outcomes of
    [Right leftResult, Right rightResult]
      | leftResult == rightResult && "eval ok: " `isPrefixOf` leftResult -> Nothing
      | otherwise -> Just (name ++ ": " ++ leftResult ++ " differeth from " ++ rightResult ++ "\nleft:\n" ++ left ++ "\nright:\n" ++ right)
    _ -> Just (name ++ ": host exception\nleft:\n" ++ left ++ "\nright:\n" ++ right)

lawPrograms :: [(String, String, String)]
lawPrograms = twoLaws ++ concatMap carrierLaws carriers
  where
    prelude =
      unlines
        [ "bring combinator.tung",
          "bring class/algebra/partial/category.tung",
          "bring class/algebra/partial/semigroupoid.tung",
          "bring often.tung",
          "bring type/list.tung",
          "bring type/optional.tung",
          "let f: [ℤ, ℤ] ≔ {x ^ x + +1}",
          "let g: [ℤ, ℤ] ≔ {x ^ x · +2}"
        ]
    listed items = "yield >{‥, " ++ concatMap (++ ", ") items ++ "empty}"
    law name inputs left right = (name, prelude ++ listed (map left inputs), prelude ++ listed (map right inputs))
    values = ["+0", "+1", "-2"]
    twos = ["yea", "nay"]
    twoLaws =
      [ law "𝟚 ≤ is reflexive" twos (\a -> a ++ " ≤ " ++ a) (const "yea"),
        law "𝟚 ≤ is antisymmetric" (pairs twos) (\(a, b) -> ">{≤, " ++ a ++ " ≤ " ++ b ++ ", " ++ b ++ " ≤ " ++ a ++ ", " ++ a ++ " ≍ " ++ b ++ "}") (const "yea"),
        law "𝟚 ≤ is transitive" (triples twos) (\(a, b, c) -> ">{≤, " ++ a ++ " ≤ " ++ b ++ ", " ++ b ++ " ≤ " ++ c ++ ", " ++ a ++ ", " ++ c ++ "}") (const "yea"),
        law "𝟚 ≤ is total" (pairs twos) (\(a, b) -> "((" ++ a ++ " ≤ " ++ b ++ ") ≍ nay) ≤ (" ++ b ++ " ≤ " ++ a ++ ")") (const "yea"),
        law "𝟚 ≍ is reflexive" twos (\a -> a ++ " ≍ " ++ a) (const "yea")
      ]
    pairs items = [(a, b) | a <- items, b <- items]
    triples items = [(a, b, c) | a <- items, b <- items, c <- items]
    -- a carrier's name, its small bracketed, its `pure` type, and a function
    -- into it.
    carriers =
      [ ("list", ["empty", "+0 ‥ empty", "+1 ‥ (-2 ‥ empty)", "+1 ‥ (+1 ‥ (+0 ‥ empty))"], "ℤ list", "{x: ℤ ^ x ‥ ((x + +1) ‥ empty)}", "f ‥ (g ‥ empty)"),
        ("optional", ["none", "+0 some", "-2 some"], "ℤ optional", "{x: ℤ ^ (x ≍ +0) if none ((x + +1) some)}", "f some")
      ]
    carrierLaws (carrier, written, pureType, k, fs) =
      [ law (carrier ++ " map keepeth identity") bracketed (\l -> l ++ " map identity") id,
        law (carrier ++ " map composeth") bracketed (\l -> "(" ++ l ++ " map f) map g") (\l -> l ++ " map (f ▷ g)"),
        law (carrier ++ " apply keepeth pure identity") bracketed (\l -> l ++ " apply ((identity: [ℤ, ℤ]) pure)") id,
        law (carrier ++ " pure apply pure") values (\a -> "((" ++ a ++ " pure): " ++ pureType ++ ") apply (f pure)") (\a -> "((" ++ a ++ " f) pure: " ++ pureType ++ ")"),
        law (carrier ++ " pure apply") values (\a -> "((" ++ a ++ " pure): " ++ pureType ++ ") apply (" ++ fs ++ ")") (\a -> "(" ++ fs ++ ") map (" ++ a ++ " ▶)"),
        law (carrier ++ " pure bind") values (\a -> "((" ++ a ++ " pure): " ++ pureType ++ ") bind " ++ k) (\a -> a ++ " " ++ k),
        law (carrier ++ " bind pure") bracketed (\l -> l ++ " bind pure") id,
        law (carrier ++ " bind associateth") bracketed (\l -> "(" ++ l ++ " bind " ++ k ++ ") bind " ++ k) (\l -> l ++ " bind {y: ℤ ^ (y " ++ k ++ ") bind " ++ k ++ "}"),
        law (carrier ++ " map pure flat") bracketed (\l -> "(" ++ l ++ " map pure) flat") id
      ]
      where
        bracketed = ["(" ++ item ++ ")" | item <- written]

-- generated classes, each with a bizen for ℤ, used through a generic
-- requirement; the value is the start plus twice each step.
dictionaryPrograms :: [(String, String, String)]
dictionaryPrograms =
  [ ( "generated dictionary " ++ show step ++ " from " ++ show start,
      "bring often.tung class hath_bump:[α: *, *] { let bump:[α, α] } bizen:ℤ hath_bump { let bump: [x:] ≔ x + "
        ++ integerSource step
        ++ " } let twice:[@α: *, @: α hath_bump, x: α, α] ≔ (x bump) bump yield "
        ++ integerSource start
        ++ " twice",
      "eval ok: " ++ integerSource (start + 2 * step)
    )
  | (step, start) <- [(-2, 4), (0, -1), (3, -1)]
  ]

-- a chain of modules, each adding its index to the value it importeth.
importPrograms :: [(String, Integer, Map.Map String String)]
importPrograms =
  [ ("generated import chain of " ++ show count, sum [1 .. count], Map.fromList [module' index | index <- [1 .. count]])
  | count <- [1, 4]
  ]
  where
    module' index =
      ( "chain" ++ show index ++ ".tung",
        "bring often.tung\n"
          ++ (if index > 1 then "bring chain" ++ show (index - 1) ++ ".tung\nshow let value: ℤ ≔ chain" ++ show (index - 1) ++ "~value + " else "show let value: ℤ ≔ +0 + ")
          ++ integerSource index
          ++ "\n"
      )

importCase :: (String, Integer, Map.Map String String) -> Test
importCase (name, expected, modules) = do
  let count = Map.size modules
  actual <- evaluateSource ("bring chain" ++ show count ++ ".tung\nyield chain" ++ show count ++ "~value") modules
  pure (if actual == "eval ok: " ++ integerSource expected then Nothing else Just (name ++ ": expected " ++ integerSource expected ++ ", got " ++ actual))

-- a single effect and a sequence preserve the exact writing order.
-- state and failure are library monads over `effect`; each program writeth its
-- exact output.
layeredPrograms :: [(String, String, String)]
layeredPrograms =
  [ ("hade handeth each step the state left by the last", "(>{then, tick, tick, get} hade~unwrap 10) bind {p ^ p project₀ $ to_string $ write}", "12"),
    ("put replaceth and lift keepeth the state", "(>{then, 4 put, ('x' write) hade~lift, get} hade~unwrap 0) bind {p ^ p project₀ $ to_string $ write}", "x4"),
    ("a failure skippeth every later effect", "(>{then, ('a' write) fallible~lift, ('stop' fail: string fallible 𝟙), ('b' write) fallible~lift} fallible~unwrap) bind unwrap", "astop"),
    ("handle runneth its handler only on a failure", "(>{then, ('a' write) fallible~lift, 'stop' fail} handle {e ^ (e write) fallible~lift} $ fallible~unwrap) bind unwrap", "astop!"),
    ("handle leaveth a result alone", "((('a' write) fallible~lift: 𝟙 fallible 𝟙) handle {_ ^ ('never' write) fallible~lift} $ fallible~unwrap) bind unwrap", "a!")
  ]

layeredCase :: Library -> (String, String, String) -> Test
layeredCase library (name, performed, expected) =
  expectEq name (Right (Right 0, expected)) do
    program <- compileWith library "layered.tung" (prelude ++ "show let main: 𝟙 effect ≔ " ++ performed ++ "\n")
    runSimulated program []
  where
    prelude =
      """
      bring effect/fallible.tung
      bring type/hade.tung
      bring class/functor/monad.tung
      bring often.tung
      bring type/and.tung
      bring type/or.tung
      let tick: ℕ hade effect 𝟙 ≔ {n ^ n + 1} tweak
      let unwrap: [string ∨ 𝟙, 𝟙 effect] ≔ {e inject₀ ^ e write, _ inject₁ ^ '!' write}

      """

effectPrograms :: [[String]]
effectPrograms = [["north"], ["north", "south", "north"]]

effectCase :: Library -> [String] -> Test
effectCase library written =
  expectEq ("generated effect " ++ unwords written) (Right (Right 0, concat written)) do
    let effects = ["('" ++ word ++ "' write)" | word <- written]
        performed = case effects of
          [single] -> single
          _ -> ">{then, " ++ intercalate ", " effects ++ "}"
    program <- compileWith library "effects.tung" ("bring often.tung\nshow let main: 𝟙 effect ≔ " ++ performed ++ "\n")
    runSimulated program []
