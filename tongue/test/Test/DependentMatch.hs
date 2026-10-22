-- pattern matching and structural recursion compile to checked eliminators.
module Test.DependentMatch (group) where

import Data.Map.Strict qualified as Map
import Test.Compile (compileProject)
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent (ModuleId (..))
import Tung.Dependent.Source (SourceProgram)

group :: IO Harness.Group
group = do
  example <- exampleSource "match.tung"
  Harness.group "dependent_match" (tests example ++ fixedIndexTests example ++ recursiveArityTests ++ repeatedScrutineeTests ++ etaTests)

tests :: String -> [Test]
tests example =
  [ computes "a case function selecteth its row" "yes not" "no",
    computes "';' rows share one result" "yes both no" "no",
    computes "';' alternatives each select the shared result" "no both yes" "no",
    computes "the first matching row winneth" "yes both yes" "yes",
    computes "selfcalling on a direct child computeth" (two ++ " plus " ++ two) four,
    computes "a fixed implicit input stayeth outside the selfcalling" "(>{‥, naught, naught, ∅}) length" two,
    computes "a changing input actth as an accumulator" "(>{‥, naught, naught next, ∅}) eftwend_onto ∅" ">{‥, naught next, naught, ∅}",
    computes "a function input is passed to each recursive call" "(>{‥, naught, naught next, ∅}) warp next" ">{‥, naught next, (naught next) next, ∅}",
    computes "several columns recurse together" (two ++ " same " ++ two) "yes",
    computes "several columns and alternatives" (two ++ " same naught") "no",
    -- a repeated bare name is a constructor pattern, not a lambda binder.
    expectEq "one row may repeat a constructor" (Right True) $
      compiled (example ++ "ilk one:* { only:one }\nlet pair:[one, one, bool] ≔ {only, only ^ yes}\n")
        >>= \program -> sameNormalIn program "only pair only" "yes",
    -- a local scrutinee is rebound at its refined type in each row.
    expectEq "a branch seeth a local scrutinee at its refined index" (Right ()) $
      () <$ compiled (example ++ "let keep:[@α:*, @n:nat, v:α vec n, α vec n] ≔ match v { nil ^ v, _ ‥′ _ _ ^ v }\n"),
    rejectContaining "one row cannot bind a variable twice" "'x' is bound twice in one row" $
      compiled (example ++ "let first:[bool, bool, bool] ≔ {x, x ^ x}\n"),
    expectEq "one bracket may repeat a constructor slot" (Right True) $
      compiled (example ++ "ilk one:* { only:one }\nlet pair:[only:one, only:one, bool] ≔ yes\n")
        >>= \program -> sameNormalIn program "only pair only" "yes",
    rejectContaining "one bracket cannot bind a variable twice" "'x' is bound twice in one row" $
      compiled (example ++ "let first:[x:bool, x:bool, bool] ≔ x\n"),
    computes "nested patterns select deeper constructors" (two ++ " at_least_two") "yes",
    computes "a wildcard row catcheth shallower values" "(naught next) at_least_two" "no",
    computes "selfcalling may pass a grandchild and a rebuilt child" ("(" ++ four ++ " next) fibonacci") ("(" ++ four ++ " next)"),
    computes "deep selfcalling keepeth an accumulator" "(>{‥, naught, naught, naught, ∅}) pairs naught" "naught next",
    expectEq "a match result type may depend on the matched worth" (Right True) $
      compiled
        ( example
            ++ """
               let choice:[bool, *] ≔ { yes ^ nat, no ^ bool }
               let pick:[b:bool, b choice] ≔ match b { yes ^ naught, no ^ no }

               """
        )
        >>= \program -> sameNormalIn program "yes pick" "naught",
    expectEq "a case function argument waiteth for a later argument to fix its input" (Right True) $
      compiled (example ++ "let onwend_to:[@α:*, @β:*, f:[α, β], a:α, β] ≔ a f\nlet answer ≔ { yes ^ no, no ^ yes } onwend_to yes\n")
        >>= \program -> sameNormalIn program "answer" "no",
    expectEq "a computed scrutinee is replaced in the goal by each row's constructor" (Right ()) $
      ()
        <$ compiled
          ( example
              ++ """
                 let constant:[b:bool, bool] ≔ match b { yes ^ no, no ^ no }
                 let law:[b:bool, (b not $ constant) = no] ≔ match b not { yes ^ eftbend, no ^ eftbend }

                 """
          ),
    expectEq "selfcalling may pass through a function field" (Right True) $
      compiled
        ( example
            ++ """
               ilk tree:* { leaf: tree, node: [[nat, tree], tree] }
               let height:[t: tree, n: nat, nat] ≔ match t { leaf ^ naught, branch node ^ ((n branch) height n) next }

               """
        )
        >>= \program -> sameNormalIn program "({_ ^ leaf} node) height naught" "naught next",
    expectEq "indexed branches refine another input before checking its body" (Right [True, True]) do
      program <-
        compiled
          """
          ilk tag:[α:*, *] { integer:ℤ tag, textual:string tag }
          let +:[ℤ, ℤ, ℤ] ≔ 'eke_wholetale' fremmed
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
    rejectContaining "selfcalling on the matched worth is rejected" "must pass a direct child" $
      compiled (example ++ "let loop:[x:nat, nat] ≔ match x { naught ^ naught, n next ^ (n next) loop }\n"),
    rejectContaining "selfcalling on a rebuilt matched worth is rejected" "must pass a direct child" $
      compiled (example ++ "let loop:[nat, nat] ≔ { naught ^ naught, naught next ^ naught, (n next) next ^ ((n next) next) loop }\n"),
    rejectContaining "a recursive definition needs an annotation" "needs an ilk annotation" $
      compiled (example ++ "let loop ≔ loop\n"),
    rejectContaining "a recursive name is not a worth" "must only be called" $
      compiled (example ++ "let bad:[x:nat, [nat, nat]] ≔ match x { naught ^ {y ^ y}, n next ^ bad }\n"),
    rejectContaining "constructor patterns need every explicit field" "needs 1 explicit arguments" $
      compiled (example ++ "let bad:[nat, bool] ≔ { next ^ yes, naught ^ no }\n"),
    rejectContaining "a constructor function needs an annotation" "needs an ilk annotation" $
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
      compiled ("let k:[@α:*, @a:α, p:a = a, p = eftbend] ≔ match p { eftbend ^ eftbend }\n")
  ]
  where
    tags = "ilk tag:[bool, *] { mark:yes tag, other:no tag }\n"
    two = "((naught next) next)"
    four = "((((naught next) next) next) next)"
    base = compiled example
    computes label expression expected = expectEq label (Right True) do
      program <- base
      sameNormalIn program expression expected

fixedIndexTests :: String -> [Test]
fixedIndexTests example =
  expectEq
    "fixed indices refine fields, their dependent tails, and whole inputs"
    (Right (replicate 12 True))
    ( do
        program <- compiled (vector ++ definitions ++ dependentFields ++ dependentIndices ++ diagonal ++ "let impossible:[0 diagonal 1, ℕ] ≔ {}\n")
        literalResults <-
          traverse
            (uncurry (sameNormalIn program))
            [ (pair ++ " predecessor", "1"),
              (pair ++ " tail", "0 cons @ℤ +7 (nil @ℤ)"),
              (pair ++ " second", "+7"),
              (pair ++ " keep", pair),
              (pair ++ " known_input eftbend", "1"),
              (pair ++ " forced_tail", "0 cons @ℤ +7 (nil @ℤ)"),
              ("0 shifted_tail " ++ pair, "0 cons @ℤ +7 (nil @ℤ)"),
              ("(yes pack 0) extract", "0"),
              ("0 pick (0 first) (1 indexed_pack (0 first))", "0 first"),
              (pair ++ " high (0 cons @* ℕ (nil @*))", "1")
            ]
        custom <- compiled example
        customResults <-
          traverse
            (uncurry (sameNormalIn custom))
            [ (customPair ++ " predecessor_two", "naught next"),
              (customPair ++ " tail_two", "naught ‥′ @nat (naught next) (nil @nat)")
            ]
        pure (literalResults ++ customResults)
    )
    : ( do
          actual <- Harness.evaluateSource ("bring is.tung\n" ++ vector ++ definitions ++ "yield " ++ pair ++ " second") Map.empty
          expectEq "the runner computeth fixed-index constructor fields" "eval ok: +7" actual
      )
    : [ rejectContaining label reason (compiled (vector ++ source))
      | (label, reason, source) <-
          [ ("a fixed index still needeth every possible constructor", "not exhaustive", "let bad:[ℤ vec 2, ℤ] ≔ {}"),
            ("a fixed index maketh the empty constructor redundant", "case 1 is redundant", "let bad:[ℤ vec 2, ℤ] ≔ { nil ^ +0, _ cons _ _ ^ +1 }"),
            ("a refined tail cannot inhabit the wrong index", "cannot unify", "let bad:[ℤ vec 2, ℤ vec 1] ≔ { _ cons _ _ ^ nil }"),
            ("one field cannot satisfy incompatible constructor indices", "case 1 is redundant", diagonal ++ "let bad:[0 diagonal 1, ℕ] ≔ { _ same ^ 0 }"),
            ("a computed constructor index stayeth undecidable", "matching cannot decide", "let back:[ℕ, ℕ] ≔ { 0 ^ 0, n next ^ n }\nilk stuck:[ℕ, *] { pack:[n:ℕ, (n back) stuck] }\nlet bad:[0 stuck, ℕ] ≔ { n pack ^ n }"),
            ("written index variables must remain distinct", "variables in the indices of an indexed family to be distinct", diagonal ++ "let bad:[n:ℕ, n diagonal n, ℕ] ≔ { _ same ^ n }"),
            ("refining an early field preserveth the later field's type", "cannot unify", dependentFields ++ "let bad:[(yes make 0) witness, bool] ≔ { _ pack x ^ x }")
          ]
      ]
  where
    vector = "ilk vec:[α:*, [ℕ, *]] { nil:α vec 0, cons:[n:ℕ, head:α, tail:α vec n, α vec (n next)] }\n"
    diagonal = "ilk diagonal:[ℕ, ℕ, *] { same:[n:ℕ, n diagonal n] }\n"
    pair = "(1 cons @ℤ +3 (0 cons @ℤ +7 (nil @ℤ)))"
    customPair = "((naught next) ‥′ @nat naught (naught ‥′ @nat (naught next) (nil @nat)))"
    definitions =
      """
      let predecessor:[@α:*, v:α vec 2, ℕ] ≔ match v { n cons _ _ ^ n }
      let tail:[@α:*, v:α vec 2, α vec 1] ≔ match v {
        n cons _ t ^ (let known:n = 1 ≔ eftbend yield t)
      }
      let second:[@α:*, α vec 2, α] ≔ { _ cons _ (_ cons x nil) ^ x }
      let keep:[@α:*, v:α vec 2, α vec 2] ≔ match v { _ cons _ _ ^ v }
      let known_input:[@α:*, v:α vec 2, known:(v predecessor) = 1, ℕ] ≔ match v {
        _ cons _ _ ^ match known { eftbend ^ 1 }
      }
      let forced_tail:[@α:*, α vec 2, α vec 1] ≔ { 1 cons _ t ^ t }
      let shifted_tail:[@α:*, k:ℕ, v:α vec ((k next) next), α vec (k next)] ≔ match v {
        n cons _ t ^ (let known:n = (k next) ≔ eftbend yield t)
      }
      let high:[@α:*, v:α vec 2, p:* vec (v predecessor), ℕ] ≔ match v { _ cons _ _ ^ 1 }

      """
    dependentFields =
      """
      ilk bool:* { no:bool, yes:bool }
      let choice:[bool, *] ≔ { yes ^ ℕ, no ^ bool }
      ilk dependent:* { make:[b:bool, x:b choice, dependent] }
      ilk witness:[dependent, *] { pack:[b:bool, x:b choice, (b make x) witness] }
      let extract:[(yes make 0) witness, ℕ] ≔ { b pack x ^ x }

      """
    dependentIndices =
      """
      ilk fin:[ℕ, *] { first:[n:ℕ, (n next) fin] }
      ilk indexed_witness:[n:ℕ, n fin, *] { indexed_pack:[k:ℕ, p:k fin, k indexed_witness p] }
      let pick:[n:ℕ, q:(n next) fin, v:(n next) indexed_witness q, (n next) fin] ≔ match v {
        k indexed_pack p ^ q
      }

      """

recursiveArityTests :: [Test]
recursiveArityTests =
  [ rejectContaining "recursive matches validate written columns" reason $
      compiled ("ilk nat:* { naught:nat, next:[nat, nat] } let rime:[x:nat, nat] ≔ match x { " ++ rows ++ " }")
  | (reason, rows) <-
      [ ("one pattern per scrutinee", "naught, _ ^ naught, n next, _ ^ n rime"),
        ("every case must have the same number of patterns", "naught ^ naught, n next, _ ^ n rime")
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
            (two ++ " rime", two),
            (four ++ " deep", two),
            (two ++ " hoard " ++ one, "(" ++ two ++ " next)"),
            ("(" ++ one ++ " wrap @naught) extract", one),
            ("+0 literal", "+1"),
            ("+1 literal", "+2")
          ]
    )
    : [ rejectContaining label reason (compiled (natural ++ source))
      | (label, reason, source) <-
          [ ("inconsistent repeated patterns keep their written row sameness", "case 1 is redundant", "let bad:[x:nat,nat] ≔ match x,x { naught,_ next ^naught, naught,naught ^naught, n next,m next ^m }"),
            ("recursive inconsistent patterns keep their written row sameness", "case 1 is redundant", "let bad:[x:nat,nat] ≔ match x,x { naught,_ next ^naught, naught,naught ^naught, n next,m next ^m bad }"),
            ("repeated inputs still bind each row name once", "'n' is bound twice", "let bad:[x:nat,nat] ≔ match x,x { naught,naught ^naught, n next,n next ^n bad }"),
            ("every repeated constructor pattern is validated before intersection", "needs 1 explicit arguments", "let bad:[x:nat,nat] ≔ match x,x { naught,naught ^naught, n next,next ^n bad }")
          ]
      ]
  where
    one = "(naught next)"
    two = "(" ++ one ++ " next)"
    four = "((" ++ two ++ " next) next)"
    natural = "ilk nat:* { naught:nat, next:[nat, nat] }\n"
    definitions =
      """
      let pick:[x:nat, nat] ≔ match x,x {
        naught,naught ^ naught,
        n next,m next ^ m
      }
      let whole:[x:nat, nat] ≔ match x,x {
        naught,_ ^ naught,
        _ next,worth ^ worth
      }
      let rime:[x:nat, nat] ≔ match x,x {
        _,naught ^ naught,
        n next,m next ^ (m rime) next
      }
      let deep:[x:nat, nat] ≔ match x,x {
        naught,_ ^ naught,
        naught next,_ ^ naught,
        (n next) next,(m next) next ^ (m deep) next
      }
      let hoard:[x:nat, y:nat, nat] ≔ match y,x,x {
        _,naught,naught ^ y,
        z,n next,m next ^ (m hoard z) next
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
compiled source = compileProject (SourceModule "dependent_match.tung") ("bring is.tung\n" ++ source) (Map.singleton "is.tung" equalitySource)

-- a family with one constructor, no indices, and no recursive field hath η:
-- a worth equaleth its constructor applied to its fields, and a match on an
-- unknown worth reduceth through them. other families keep their neutrals.
etaTests :: [Test]
etaTests =
  [ expectEq "a pair equaleth its fields, and a match on an unknown pair reduceth" (Right ()) $
      () <$ compileAs "eta.tung" (families ++ "let eta: [@α: *, @β: *, p: α ∧ β, p = ((p first) ⸴ (p second))] ≔ eftbend\nlet swap: [@α: *, @β: *, α ∧ β, β ∧ α] ≔ {a ⸴ b ^ b ⸴ a}\nlet swap_swap: [@α: *, @β: *, p: α ∧ β, ((p swap) swap) = p] ≔ eftbend\nlet unit: [a: one, a = only] ≔ eftbend\n"),
    -- without fields, any two worths are equal; only their types tell so.
    expectEq "any two worths of a fieldless family are equal" (Right ()) $
      () <$ compileAs "eta.tung" (families ++ "let units: [a: one, b: one, a = b] ≔ eftbend\nlet under: [f: [two, one], g: [two, one], b: two, (b f) = (b g)] ≔ eftbend\n"),
    rejectContaining "a pair is not determined by its type" "cannot unify" $
      compileAs "eta.tung" (families ++ "let bad: [p: one ∧ two, q: one ∧ two, p = q] ≔ eftbend\n"),
    rejectContaining "a family of two constructors hath no η" "cannot unify" $
      compileAs "eta.tung" (families ++ "let bad: [a: two, a = yea] ≔ eftbend\n"),
    rejectContaining "a recursive family hath no η" "cannot unify" $
      compileAs "eta.tung" (families ++ "let bad: [s: stream, s = ((match s { a more _ ^ a }) more s)] ≔ eftbend\n"),
    rejectContaining "an indexed family hath no η" "cannot unify" $
      compileAs "eta.tung" (families ++ "let bad: [v: yea vec, v = nil] ≔ eftbend\n")
  ]
  where
    families =
      """
      ilk =: [@α: *, x: α, α, *] { eftbend: x = x }
      ilk ∧: [α: *, β: *, *] { ⸴: [α, β, α ∧ β] }
      ilk one: * { only: one }
      ilk two: * { yea: two, nay: two }
      ilk stream: * { more: [two, stream, stream] }
      ilk vec: [two, *] { nil: yea vec, cons: [two, nay vec] }
      let first: [@α: *, @β: *, a ⸴ _: α ∧ β, α] ≔ a
      let second: [@α: *, @β: *, _ ⸴ b: α ∧ β, β] ≔ b

      """
