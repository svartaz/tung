-- recursion selection useth checked bindings, including aliases and shadowing.
module Test.DependentRecursion (group) where

import Control.Monad (forM_)
import Data.Map.Strict qualified as Map
import Test.DependentSupport
import Test.Harness (Group, Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent (validate)
import Tung.Dependent.Source (SourceProgram, sourceDefinitions, sourceEnvironment)

group :: IO Group
group = do
  indexed <- exampleSource "index_recursion.tung"
  memo <- exampleSource "index_memo.tung"
  functions <- exampleSource "function_recursion.tung"
  wellFounded <- exampleSource "wellgrounded.tung"
  grounded <- loadLibrary ["ilk/grounded.tung", "ilk/list_setting.tung", "ilk/kindful.tung", "often.tung"]
  Harness.group "dependent-recursion" (wellFoundedTests grounded wellFounded ++ boundedTests grounded ++ positiveTests ++ indexRecursionTests grounded indexed ++ indexMemoTests memo ++ functionRecursionTests grounded functions ++ rejectionTests)

-- library measure recursion retaineth checked decrease proofs and dependent results.
wellFoundedTests :: Library -> String -> [Test]
wellFoundedTests library example =
  expectEq
    "measure recursion computeth for direct, computed and rebuilt inputs"
    (Right (replicate 5 True))
    ( do
        program <- compile example
        forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd)
        traverse
          (uncurry (sameNormalIn program))
          [ ("three rime", "three"),
            ("three eke (nought after)", "three after"),
            ("three shifted", "three"),
            ("(three pack) unpack_rime", "three"),
            ("(three pack) selfsame", "(eftbend:(three pack) = (three pack))")
          ]
    )
    : [ rejectContaining label "cannot unify" (compile (example ++ source))
      | (label, source) <-
          [ ("a callback cannot recurse at the same measure", "let bad:[n:onestead, onestead] ≔ {_ ^ onestead} wellgrounded_selfcall_by {x ^ x} reach {n, selfcall ^ match n { nought ^ nought, m after ^ (m after) selfcall step }} n"),
            ("a callback requires the decrease proof", "let bad:[n:onestead, onestead] ≔ {_ ^ onestead} wellgrounded_selfcall_by {x ^ x} reach {n, selfcall ^ match n { nought ^ nought, m after ^ m selfcall }} n")
          ]
      ]
  where
    compile = compileWith library "dependent_wellgrounded.tung"

-- bookhoard's well-founded `under` on `ℕ` serveth numeric and size measures.
boundedTests :: Library -> [Test]
boundedTests library =
  [ expectEq
      "under measures count down by two and over list manyhood"
      (Right [True, True])
      ( do
          program <- compile ""
          traverse (uncurry (sameNormalIn program)) [("7 halve", "3"), ("(1 ‥ (2 ‥ (3 ‥ empty))) total", "6")]
      ),
    ( do
        actual <- Harness.evaluateSource (prelude ++ "yield (1 ‥ (2 ‥ (3 ‥ empty))) total") Map.empty
        expectEq "the runner computeth library measure recursion" "eval ok: 6" actual
    ),
    rejectContaining "a number is not under itself" "cannot unify" (compile "let bad: [n: ℕ, n under n] ≔ n under_next"),
    rejectContaining "a list is not under its own manyhood" "cannot unify" (compile "let bad: [x: ℕ, l: ℕ list, ((x ‥ l) manyhood) under ((x ‥ l) manyhood)] ≔ x ‥_manyhood_under l")
  ]
  where
    compile extra = compileWith library "under.tung" (prelude ++ extra)
    prelude =
      """
      bring flock/hath_manyhood.tung
      bring often.tung
      bring ilk/grounded.tung
      bring ilk/list.tung
      bring ilk/list_setting.tung
      bring ilk/kindful.tung
      let halve: [n:ℕ, ℕ] ≔
        {_ ^ ℕ} wellgrounded_selfcall_by {x ^ x} under_wellgrounded
          {n, selfcall ^ match n {
            0 ^ 0,
            1 ^ 0,
            (k next) next ^ (k selfcall (k under_throughgo (k next) ((k next) next) (k under_next) ((k next) under_next))) + 1
          }} n
      let total: [l:ℕ list, ℕ] ≔
        {_:ℕ list ^ ℕ} wellgrounded_selfcall_by manyhood under_wellgrounded
          {l, selfcall ^ match l {
            empty ^ 0,
            x ‥ leftover ^ x + (leftover selfcall (x ‥_manyhood_under leftover))
          }} l

      """

functionRecursionTests :: Library -> String -> [Test]
functionRecursionTests library example =
  expectEq
    "function descendants and partial recursive calls retain checked induction evidence"
    (Right (replicate 8 True))
    ( do
        program <- compileFunctions example
        forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd)
        traverse
          (uncurry (sameNormalIn program))
          [ ("sample depth", "2"),
            ("sample deep_hoard 4", "6"),
            ("3 hoard 4", "7"),
            ("leaf depth", "1"),
            ("sample soothing", "(eftbend:sample = sample)"),
            ("fan_sample fan_depth", "2"),
            ("rose_sample height", "2"),
            ("2 retain eftbend", "0")
          ]
    )
    : ( do
          actual <- Harness.evaluateSource (example ++ "yield sample deep_hoard 4") Map.empty
          expectEq "the runner computeth pointwise descendant records" "eval ok: 6" actual
      )
    : [ reject label (compileFunctions (example ++ source))
      | (label, source) <-
          [ ("an unrelated function cannot supply descendant evidence", "let bad:[x:tree, other:[ℕ,tree], ℕ] ≔ match x {tip ^ 0, _ node children ^ (0 other) bad other}"),
            ("a shadowing function cannot supply descendant evidence", "let bad:[x:tree,ℕ] ≔ match x {tip ^ 0, _ node children ^ (let children:[ℕ,tree] ≔ {_ ^ x} yield (0 children) bad)}"),
            ("a function field must return the decreasing value before a recursive call", "let bad:[tree,ℕ] ≔ {tip ^ 0, _ node children ^ children bad}"),
            ("a generic function input cannot inherit pointwise evidence", "let bad:[tree,ℕ] ≔ {tip ^ 0, _ node children ^ (let run:[call:[ℕ,tree],ℕ] ≔ (0 call) bad yield children run)}"),
            ("a function descendant must retain its actual index", "let bad:[n:ℕ,x:n fan,ℕ] ≔ match x {stop ^ 0, children more ^ match eftbend children @0 {stop ^ 1, smaller more ^ 0 bad (eftbend smaller @1)}}"),
            ("a recursive name without a decreasing input cannot be passed as a value", "let bad:[ℕ,ℕ] ≔ {0 ^ 0, n next ^ (let run ≔ bad yield n run)}"),
            ("a partial call cannot omit its structural input", "ilk chain:[ℕ,*] {stop:0 chain, step:[n:ℕ,n chain,(n next) chain]}\nlet bad:[n:ℕ,x:n chain,total:ℕ,ℕ] ≔ match x {stop ^ total, k step child ^ (let leftover ≔ k bad yield 0 leftover)}")
          ]
      ]
  where
    compileFunctions = compileWith library "dependent_function_recursion.tung"

indexRecursionTests :: Library -> String -> [Test]
indexRecursionTests library example =
  expectEq
    "constructor-index recursion retaineth fixed domains, dependent results, and quantified inputs"
    (Right (replicate 6 True))
    ( do
        program <- compileIndex (example ++ vectorSource ++ nonemptyDefinitions)
        forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd)
        traverse
          (uncurry (sameNormalIn program))
          [ (grown ++ " depth", "2"),
            (grown ++ " copy", "(eftbend:" ++ grown ++ " = " ++ grown ++ ")"),
            (grown ++ " hoard 3", "5"),
            ("0 shifted " ++ grown, "2"),
            (vectorPair ++ " unempty_length", "2"),
            (vectorPair ++ " unempty_copy", vectorPair)
          ]
    )
    : ( do
          actual <- Harness.evaluateSource (example ++ "yield " ++ grown ++ " hoard 3") Map.empty
          expectEq "the runner computeth recursive hypotheses at constructor indices" "eval ok: 5" actual
      )
    : [ reject label (compileIndex (example ++ source))
      | (label, source) <-
          [ ("a recursive call must pass the child's matching index leaf", "let bad:[k:ℕ, x:(k next) tag, ℕ] ≔ match x { one_case ^ 0, child grow ^ 1 bad child }"),
            ("a fixed-index root is not its own child", "let bad:[x:1 tag, ℕ] ≔ match x { one_case ^ 0, child grow ^ x bad }"),
            ("a rebuilt fixed-index root is not a child", "let bad:[1 tag, ℕ] ≔ { one_case ^ 0, child grow ^ (child grow) bad }"),
            ("an unrelated fixed-index input is not a child", "let bad:[1 tag, y:1 tag, ℕ] ≔ { one_case,_ ^ 0, child grow,y ^ y bad y }"),
            ("a fixed vector's tail cannot change its recursive domain", vectorSource ++ "let bad:[@α:*, α vec 2, ℕ] ≔ { _ cons _ tail ^ tail bad }"),
            ("a unempty vector's arbitrary tail need not be unempty", vectorSource ++ "let bad:[@α:*, @n:ℕ, α vec (n next), ℕ] ≔ { _ cons _ tail ^ tail bad }"),
            ("reverted induction evidence cannot justify an unrelated vector", vectorSource ++ "let bad:[@α:*, @n:ℕ, v:α vec (n next), other:α vec (n next), ℕ] ≔ match v { k cons _ tail ^ match k { 0 ^ 0, m next ^ other bad other } }")
          ]
      ]
  where
    compileIndex = compileWith library "dependent_index_recursion.tung"
    grown = "((one_case grow) grow)"
    vectorPair = "(1 cons @ℕ 3 (0 cons @ℕ 7 (nil @ℕ)))"
    vectorSource = "ilk vec:[α:*, [ℕ, *]] { nil:α vec 0, cons:[n:ℕ, head:α, tail:α vec n, α vec (n next)] }\n"
    nonemptyDefinitions =
      """
      let unempty_length:[@α:*, @n:ℕ, v:α vec (n next), ℕ] ≔ match v {
        k cons _ tail ^ match k {
          0 ^ 1,
          m next ^ (tail unempty_length) next
        }
      }
      let unempty_copy:[@α:*, @n:ℕ, v:α vec (n next), α vec (n next)] ≔ match v {
        0 cons _ _ ^ v,
        (m next) cons _ tail ^ (let known:α vec (m next) ≔ tail unempty_copy yield v)
      }
      """

indexMemoTests :: String -> [Test]
indexMemoTests example =
  expectEq
    "indexed descendant records retain indices, dependent results, and joint targets"
    (Right (replicate 8 True))
    ( do
        program <- compileMemo (example ++ aliases ++ nested ++ mutual)
        forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd)
        traverse
          (uncurry (sameNormalIn program))
          [ (chain3 ++ " depth", "3"),
            (chain3 ++ " copy", chain3),
            (chain3 ++ " named_depth", "3"),
            ("3 hoard " ++ chain3 ++ " 4", "7"),
            ("((((stop up) down) up) down) laps", "2"),
            ("0 spins (((stop up) down) up)", "1"),
            ("((leaf cons nil) node) height", "1"),
            ("(0 to_one 2 (2 to_two @0 initial)) rime", "1")
          ]
    )
    : ( do
          actual <- Harness.evaluateSource (example ++ "yield 3 hoard " ++ chain3 ++ " 4") Map.empty
          expectEq "the runner computeth indexed descendant records" "eval ok: 7" actual
      )
    : [ reject label (compileMemo (example ++ source))
      | (label, source) <-
          [ ("a constructor-shaped memo call must pass the matching leaf", "let bad:[k:ℕ,x:(k next) cycle,ℕ] ≔ match x {stop up ^ 0,(child down) up ^ 1 bad child}"),
            ("an off-domain memo result cannot be used as the source result", "let bad:[0 cycle,ℕ] ≔ {stop ^ 0, child down ^ (child bad) 0}"),
            ("a deep indexed recursive call must pass the child's actual index", "let bad:[n:ℕ,x:n chain,ℕ] ≔ match x {empty ^ 0,_ link empty ^ 1,_ link (_ link child) ^ 0 bad child}"),
            ("an unrelated indexed value carrieth no descendant evidence", "let bad:[@n:ℕ,v:n chain,other:n chain,ℕ] ≔ match v {empty ^ 0,_ link _ ^ other bad other}"),
            ("a rebuilt indexed root carrieth no descendant evidence", "let bad:[@n:ℕ,n chain,ℕ] ≔ {empty ^ 0,k link child ^ (k link child) bad}")
          ]
      ]
  where
    compileMemo = compileAs "dependent_index_memo.tung"
    chain3 = "(2 link (1 link (0 link empty)))"
    aliases =
      """
      let named_depth:[@n:ℕ,x:n chain,ℕ] ≔ match x {
        empty ^ 0,
        _ link tail ^ (let alias ≔ tail yield match alias {
          empty ^ 1,
          _ link child ^ (let known ≔ child yield ((known named_depth) next) next)
        })
      }
      """
    nested =
      """
      ilk links:[α:*,*] {nil:α links, cons:[α,α links,α links]}
      ilk tree:[ℕ,*] {naught_leaf:0 tree,leaf:1 tree,node:[(1 tree) links,1 tree]}
      let height:[@n:ℕ,n tree,ℕ] ≔ {
        naught_leaf ^ 0,
        leaf ^ 0,
        nil node ^ 0,
        (child cons _) node ^ (child height) next
      }
      """
    mutual =
      """
      ilk one:[ℕ,*] {
        initial:0 one,
        to_one:[n:ℕ,m:ℕ,m two @(n next),(n next) one]
      }
      ilk two:[@j:ℕ,m:ℕ,*] {
        to_two:[@n:ℕ,m:ℕ,n one,m two @(n next)]
      }
      let rime:[@n:ℕ,n one,ℕ] ≔ {
        initial ^ 0,
        _ to_one _ (_ to_two child) ^ (child rime) next
      }
      """

positiveTests :: [Test]
positiveTests =
  [ expectEq label (Right True) do
      program <- compile source
      sameNormalIn program actual expected
  | (label, source, actual, expected) <-
      [ ( "the input the first row matcheth is split first",
          "let sub:[nat, nat, nat] ≔ {m, naught ^ m, naught, _ next ^ naught, j next, k next ^ j sub k}\n",
          "{x: nat ^ x sub naught}",
          "{x: nat ^ x}"
        ),
        ("a lambda may shadow the recursive binding", count "(n rime) keep ({z ^ z} {rime:[nat,nat] ^ naught rime})", two ++ " rime", two),
        ("a case variable may shadow the recursive binding", count "(n rime) keep (naught {rime ^ rime})", two ++ " rime", two),
        ("a local binding may shadow the recursive binding", count "(let worth ≔ n rime let rime ≔ naught yield worth keep rime)", two ++ " rime", two),
        ("a local initialiser still seeth the outer recursive binding", count "(let rime ≔ n rime yield rime)", two ++ " rime", two),
        ("a direct child's alias denoteth the same recursive input", count "(let smaller ≔ n yield smaller rime)", two ++ " rime", two),
        ( "a rebound first child leaveth the second input structural",
          """
          let right:[x:nat, y:nat, nat] ≔ match x,y {
            naught,_ ^ naught,
            n next,naught ^ naught,
            n next,m next ^ (let n ≔ n next yield n right m) next
          }
          """,
          two ++ " right " ++ three,
          three
        ),
        ( "nested selfcalling retaineth an outer induction hypothesis",
          count
            """
            (let local:[nat,nat] ≔ {
              naught ^ n rime,
              m next ^ m local
            } yield n local)
            """,
          two ++ " rime",
          two
        ),
        ( "nested deep selfcalling retaineth an outer memoised hypothesis",
          """
          let deep:[nat,nat] ≔ {
            naught ^ naught,
            naught next ^ naught next,
            (n next) next ^ (let local:[nat,nat] ≔ {
              naught ^ (n next) deep,
              naught next ^ (n next) deep,
              (m next) next ^ (m next) local
            } yield n local) next
          }
          """,
          four ++ " deep",
          four
        ),
        ( "overlapping memo records preserve their respective recursive results",
          """
          let deep:[nat,nat] ≔ {
            naught ^ naught,
            naught next ^ naught next,
            (n next) next ^ match n {
              naught ^ (let inner:[nat,nat] ≔ {
                naught ^ naught next,
                naught next ^ naught next,
                (m next) next ^ match m {
                  naught ^ match naught {
                    naught ^ (naught deep) keep (naught inner),
                    _ next ^ naught
                  },
                  k next ^ (k inner) next
                }
              } yield ((naught next) next) inner) next,
              k next ^ (k deep) next
            }
          }
          """,
          two ++ " deep",
          "naught next"
        ),
        ( "a recursive lambda retaineth its binder annotation",
          "let rime:[nat,nat] ≔ {x:nat ^ match x {naught ^ naught, n next ^ (n rime) next}}",
          two ++ " rime",
          two
        ),
        ( "mutual descendant records retain quantified accumulators",
          """
          ilk left:* { stop:left, step:[right,left] }
          ilk right:* { back:[left,right] }
          let hoard:[left,nat,nat] ≔ {
            stop,total ^ total,
            (child back) step,total ^ child hoard (total next)
          }
          """,
          "((stop back) step) hoard (naught next)",
          two
        ),
        ( "course-of-values recursion crosses an indexed peer",
          """
          ilk plain:* { stop:plain, from_indexed:[naught indexed,plain] }
          ilk indexed:[nat,*] { to_indexed:[plain,naught indexed] }
          let deep:[plain,nat] ≔ {
            stop ^ naught,
            (child to_indexed) from_indexed ^ (child deep) next
          }
          """,
          "((stop to_indexed) from_indexed) deep",
          "naught next"
        ),
        -- an indexed structural input whose indices are earlier inputs.
        ("recursion may match an indexed value whose index is an implicit input", vector ++ "let length:[@α:*, @n:nat, v:α vec n, nat] ≔ match v { nil ^ naught, _ cons _ t ^ (t length) next }", pair ++ " length", two),
        ("an indexed recursion's result may mention the index", vector ++ "let warp:[@α:*, @β:*, @n:nat, v:α vec n, f:[α, β], β vec n] ≔ match v { nil ^ nil, k cons a t ^ k cons (a f) (t warp f) }", pair ++ " warp {x ^ x next}", "(naught next) cons @nat (naught next) ((naught cons @nat (naught next) (nil @nat)))"),
        ("an explicit index input is refined in each branch", vector ++ "let manyhood:[@α:*, n:nat, v:α vec n, nat] ≔ match v { nil ^ n, k cons _ t ^ (k manyhood t) next }", two ++ " manyhood " ++ pair, two)
      ]
  ]

rejectionTests :: [Test]
rejectionTests =
  [ reject label (compile source)
  | (label, source) <-
      [ ("a shadowing worth is not the former child", count "(let n ≔ naught yield n rime)"),
        ("an explicit index argument must be the child's index", vector ++ "let manyhood:[@α:*, n:nat, v:α vec n, nat] ≔ match v { nil ^ n, k cons _ t ^ (naught manyhood t) next }"),
        ("an index input cannot be matched by a constructor", vector ++ "let manyhood:[@α:*, n:nat, v:α vec n, nat] ≔ { naught, nil ^ naught, _, k cons _ t ^ (k manyhood t) next }"),
        ("a recursive lambda cannot ignore a wrong binder annotation", "let rime:[nat,nat] ≔ {x:string ^ match x {naught ^ naught, n next ^ (n rime) next}}"),
        ("a rebuilt matched input is not a descendant", count "(n next) rime"),
        ( "an inner child is not an outer induction hypothesis",
          count
            """
            (let local:[nat,nat] ≔ {
              naught ^ naught,
              m next ^ (m rime) keep (m local)
            } yield n local)
            """
        )
      ]
  ]

count :: String -> String
count body = "let rime:[x:nat,nat] ≔ match x { naught ^ naught, n next ^ (" ++ body ++ ") next }"

vector, pair :: String
vector = "ilk vec:[α:*, [nat, *]] { nil:α vec naught, cons:[n:nat, head:α, tail:α vec n, α vec (n next)] }\n"
pair = "((naught next) cons @nat naught (naught cons @nat naught (nil @nat)))"

two, three, four :: String
two = "((naught next) next)"
three = "(" ++ two ++ " next)"
four = "(" ++ three ++ " next)"

compile :: String -> Either String SourceProgram
compile = compileAs "dependent_selfcall.tung" . (prefix ++)
  where
    prefix =
      """
      ilk nat:* { naught:nat, next:[nat,nat] }
      let keep:[x:nat,y:nat,nat] ≔ x

      """
