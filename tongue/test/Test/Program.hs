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
  library <- loadLibrary ["often.tung", "deed/misfaresome.tung", "deed/onstand.tung"]
  Harness.group
    "program"
    ( map integerCase integerTerms
        ++ map languageCase (languagePrograms ++ booleanProductPrograms ++ dictionaryPrograms)
        ++ map importCase importPrograms
        ++ map (deedCase library) deedPrograms
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
  [ ("checked declaration annotations and inferred functions", "bring often.tung let rime:* ≔ ℤ let sameness: [@α: *, x: α, α] ≔ x let choose:[@α:*, @β:*, x:α, _:β, α] ≔ x let hath_+: [x:, y:rime, rime] ≔ x + y let tale:rime ≔ (let worth ≔ +3 yield worth sameness) let outcome ≔ tale hath_+ (+4 choose @ℤ @string 'ignored') yield outcome", "eval ok: +7"),
    ("checked field access", "ilk pair: * { pair_of: [left: ℤ, right: ℤ, pair] } let worth ≔ +1 pair_of +2 yield worth.right", "eval ok: +2"),
    ("checked exhaustive match", "ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } yield match nay { yea ^ +1, nay ^ +2 }", "eval ok: +2"),
    ("checked ℤ match", "yield match +1 { +0 ^ +10, +1 ^ +20, _ ^ +30 }", "eval ok: +20"),
    ("checked class evidence", "flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x } yield +7 sameness", "eval ok: +7"),
    ("checked value retaineth unused required evidence", "ilk unit: * { only: unit } flock capability:[a:*, *] {} bizen:ℤ capability {} let empty:[@a:*, @:a capability, unit] ≔ only yield empty @ℤ", "eval ok: only"),
    ("checked annotated local selfcalling", "bring often.tung yield (let rime:[ℕ, ℕ] ≔ { 0 ^ 0, n heir ^ n rime } yield 2 rime)", "eval ok: 0"),
    ( "checked nested deep selfcalling with repeated scrutinees",
      """
      ilk nat:* { naught:nat, heir:[nat,nat] }
      let +:[ℤ,ℤ,ℤ] ≔ 'eke_wholetale' fremmed
      let tale:[nat,ℤ] ≔ { naught ^ +0, n heir ^ (n tale) + +1 }
      let deep:[x:nat,nat] ≔ match x,x {
        naught,_ ^ naught,
        naught heir,_ ^ naught heir,
        (n heir) heir,(m heir) heir ^ (let local:[nat,nat] ≔ {
          naught ^ (m heir) deep,
          naught heir ^ (m heir) deep,
          (k heir) heir ^ (k heir) local
        } yield m local) heir
      }
      yield (((((naught heir) heir) heir) heir) deep) tale
      """,
      "eval ok: +4"
    ),
    ("checked annotated initializer seeth its preceding binding", "bring often.tung yield (let worth:ℤ ≔ +1 let worth:ℤ ≔ worth + +1 yield worth)", "eval ok: +2"),
    ("checked binders sharing a declaration's name", "let +:[ℤ, ℤ, ℤ] ≔ 'eke_wholetale' fremmed let keep:[keep:ℤ, ℤ] ≔ keep let outer:[ℤ, ℤ] ≔ {x ^ (let inner ≔ {inner ^ inner} yield x inner)} let worth ≔ (let worth ≔ +1 yield worth) yield (+1 keep) + (worth outer)", "eval ok: +2"),
    ("checked bizen member calleth sibling", "flock linked:[a:*, *] { let first:[a, a] let second:[a, a] } bizen:ℤ linked { let first: [x:] ≔ x let second: [x:] ≔ x first } yield +7 second", "eval ok: +7"),
    ("checked non-finite floor yieldeth none", "bring often.tung bring ilk/maybe.tung let parsed:float maybe ≔ 'Infinity' from_string yield match parsed bind ⌊ { n some ^ n, none ^ +0 }", "eval ok: +0")
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
    boolData = "ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } "
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
          "bring flock/algebra/half/category.tung",
          "bring flock/algebra/half/semigroupoid.tung",
          "bring often.tung",
          "bring ilk/list.tung",
          "bring ilk/maybe.tung",
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
    -- a carrier's name, its small worths, its `sheer` type, and a function
    -- into it.
    carriers =
      [ ("list", ["empty", "+0 ‥ empty", "+1 ‥ (-2 ‥ empty)", "+1 ‥ (+1 ‥ (+0 ‥ empty))"], "ℤ list", "{x: ℤ ^ x ‥ ((x + +1) ‥ empty)}", "f ‥ (g ‥ empty)"),
        ("maybe", ["none", "+0 some", "-2 some"], "ℤ maybe", "{x: ℤ ^ (x ≍ +0) if none ((x + +1) some)}", "f some")
      ]
    carrierLaws (carrier, written, sheerType, k, fs) =
      [ law (carrier ++ " warp keepeth sameness") worths (\l -> l ++ " warp sameness") id,
        law (carrier ++ " warp composeth") worths (\l -> "(" ++ l ++ " warp f) warp g") (\l -> l ++ " warp (f ▷ g)"),
        law (carrier ++ " atfold keepeth sheer sameness") worths (\l -> l ++ " atfold ((sameness: [ℤ, ℤ]) sheer)") id,
        law (carrier ++ " sheer atfold sheer") values (\a -> "((" ++ a ++ " sheer): " ++ sheerType ++ ") atfold (f sheer)") (\a -> "((" ++ a ++ " f) sheer: " ++ sheerType ++ ")"),
        law (carrier ++ " sheer atfold") values (\a -> "((" ++ a ++ " sheer): " ++ sheerType ++ ") atfold (" ++ fs ++ ")") (\a -> "(" ++ fs ++ ") warp (" ++ a ++ " call)"),
        law (carrier ++ " sheer bind") values (\a -> "((" ++ a ++ " sheer): " ++ sheerType ++ ") bind " ++ k) (\a -> a ++ " " ++ k),
        law (carrier ++ " bind sheer") worths (\l -> l ++ " bind sheer") id,
        law (carrier ++ " bind associateth") worths (\l -> "(" ++ l ++ " bind " ++ k ++ ") bind " ++ k) (\l -> l ++ " bind {y: ℤ ^ (y " ++ k ++ ") bind " ++ k ++ "}"),
        law (carrier ++ " warp sheer flat") worths (\l -> "(" ++ l ++ " warp sheer) flat") id
      ]
      where
        worths = ["(" ++ worth ++ ")" | worth <- written]

-- generated flocks, each with a bizen for ℤ, used through a generic
-- requirement; the worth is the start plus twice each step.
dictionaryPrograms :: [(String, String, String)]
dictionaryPrograms =
  [ ( "generated dictionary " ++ show step ++ " from " ++ show start,
      "bring often.tung flock hath_bump:[α: *, *] { let bump:[α, α] } bizen:ℤ hath_bump { let bump: [x:] ≔ x + "
        ++ integerSource step
        ++ " } let twice:[@α: *, @: α hath_bump, x: α, α] ≔ (x bump) bump yield "
        ++ integerSource start
        ++ " twice",
      "eval ok: " ++ integerSource (start + 2 * step)
    )
  | (step, start) <- [(-2, 4), (0, -1), (3, -1)]
  ]

-- a chain of modules, each adding its index to the worth it importeth.
importPrograms :: [(String, Integer, Map.Map String String)]
importPrograms =
  [ ("generated import chain of " ++ show count, sum [1 .. count], Map.fromList [module' index | index <- [1 .. count]])
  | count <- [1, 4]
  ]
  where
    module' index =
      ( "chain" ++ show index ++ ".tung",
        "bring often.tung\n"
          ++ (if index > 1 then "bring chain" ++ show (index - 1) ++ ".tung\nshow let worth: ℤ ≔ chain" ++ show (index - 1) ++ "~worth + " else "show let worth: ℤ ≔ +0 + ")
          ++ integerSource index
          ++ "\n"
      )

importCase :: (String, Integer, Map.Map String String) -> Test
importCase (name, expected, modules) = do
  let count = Map.size modules
  actual <- evaluateSource ("bring chain" ++ show count ++ ".tung\nyield chain" ++ show count ++ "~worth") modules
  pure (if actual == "eval ok: " ++ integerSource expected then Nothing else Just (name ++ ": expected " ++ integerSource expected ++ ", got " ++ actual))

-- a single deed and a sequence preserve the exact writing order.
-- state and failure are library monads over `deed`; each program writeth its
-- exact output.
layeredPrograms :: [(String, String, String)]
layeredPrograms =
  [ ("onstand handeth each step the state left by the last", "(>{then, tick, tick, get} onstand~run 10) bind {p ^ p forthcast₀ $ to_string $ write}", "12"),
    ("put replaceth and lift keepeth the state", "(>{then, 4 put, ('x' write) onstand~lift, get} onstand~run 0) bind {p ^ p forthcast₀ $ to_string $ write}", "x4"),
    ("a misfare skippeth every later deed", "(>{then, ('a' write) misfaresome~lift, ('stop' misfare: string misfaresome 𝟙), ('b' write) misfaresome~lift} misfaresome~run) bind eftbare", "astop"),
    ("handle runneth its handler only on a misfare", "(>{then, ('a' write) misfaresome~lift, 'stop' misfare} handle {e ^ (e write) misfaresome~lift} $ misfaresome~run) bind eftbare", "astop!"),
    ("handle leaveth a result alone", "((('a' write) misfaresome~lift: 𝟙 misfaresome 𝟙) handle {_ ^ ('never' write) misfaresome~lift} $ misfaresome~run) bind eftbare", "a!")
  ]

layeredCase :: Library -> (String, String, String) -> Test
layeredCase library (name, performed, expected) =
  expectEq name (Right (Right 0, expected)) do
    program <- compileWith library "layered.tung" (prelude ++ "show let main: 𝟙 deed ≔ " ++ performed ++ "\n")
    runSimulated program []
  where
    prelude =
      """
      bring deed/misfaresome.tung
      bring deed/onstand.tung
      bring flock/functor/monad.tung
      bring often.tung
      bring ilk/product.tung
      bring ilk/sum.tung
      let tick: ℕ onstand 𝟙 ≔ {n ^ n + 1} tweak
      let eftbare: [string ∑ 𝟙, 𝟙 deed] ≔ {e incast₀ ^ e write, _ incast₁ ^ '!' write}

      """

deedPrograms :: [[String]]
deedPrograms = [["north"], ["north", "south", "north"]]

deedCase :: Library -> [String] -> Test
deedCase library written =
  expectEq ("generated deed " ++ unwords written) (Right (Right 0, concat written)) do
    let deeds = ["('" ++ word ++ "' write)" | word <- written]
        performed = case deeds of
          [single] -> single
          _ -> ">{then, " ++ intercalate ", " deeds ++ "}"
    program <- compileWith library "deeds.tung" ("bring often.tung\nshow let main: 𝟙 deed ≔ " ++ performed ++ "\n")
    runSimulated program []
