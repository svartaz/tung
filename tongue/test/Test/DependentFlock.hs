-- flocks are dictionary families; bizens are found by instance search.
module Test.DependentFlock (group) where

import Data.Map.Strict qualified as Map
import Test.Compile (compileProject)
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent
import Tung.Dependent.Source (SourceProgram, sorryAssumptions, typeOfName)

group :: IO Harness.Group
group = do
  example <- exampleSource "dependent_flocks.tung"
  Harness.group "dependent-flock" (tests example ++ selectionTests)

tests :: String -> [Test]
tests example =
  [ computes "a bizen supplieþ a member" "yea ≍ nay" "nay",
    computes "a requirement passeþ the caller's bizen" "yea ≭ nay" "yea",
    computes "a bizen solveþ its own requirement" "(yea some) ≍ (nay some)" "nay",
    computes "nested requirements compute" "(yea some) ≍ (yea some)" "yea",
    computes "a direct bizen outrankeþ a parent path" "(yea some) map {x ^ x}" "yea some",
    expectEq "a parent comeþ from a child requirement" (Right True) do
      program <- compiled (example ++ "let lifted:𝟚 option ≔ yea lift {x ^ x}\n")
      sameNormalIn program "lifted" "yea some",
    expectEq "a declaration may precede what it useþ" (Right True) do
      program <- compiled ("let early:𝟚 ≔ yea ≭ nay\n" ++ example)
      sameNormalIn program "early" "yea",
    expectEq "a shown flock and its bizens cross modules" (Right True) do
      program <- compileProject (SourceModule "main.tung") "use equal.tung\nlet same:𝟚 ≔ nay ≍ nay\n" (Map.fromList [("equal.tung", shown)])
      sameNormalIn program "same" "yea",
    expectEq "a rejected candidate doth not affect a later bizen" (Right True) do
      program <-
        compiled
          """
          ilk box:[α:*, *] { box_value:[α, α box] }
          flock provided:[α:*, *] { let get:α }
          bizen:(ℕ box) provided { let get ≔ 0 box_value }
          bizen:(text box) provided { let get ≔ 'ok' box_value }
          let answer:text box ≔ get
          """
      sameNormalIn program "answer" "'ok' box_value",
    rejectContaining "a bizen needeþ every member" "bizen is missing member 'two'" $
      compiled (example ++ pair ++ "bizen:𝟚 pair { let one ≔ yea }\n"),
    rejectContaining "a bizen cannot add members" "'three' is not a member" $
      compiled (example ++ pair ++ "bizen:𝟚 pair { let one ≔ yea\nlet two ≔ yea\nlet three ≔ yea }\n"),
    rejectContaining "a missing bizen is reported" "no bizen of flock 'equal'" $
      compiled (example ++ "ilk unit:* { only: unit }\nlet bad:𝟚 ≔ only ≍ only\n"),
    rejectContaining "a second bizen of one type is rejected" "a bizen wiþ þe same type already exists" $
      compiled (example ++ "bizen:𝟚 equal { let ≍ ≔ {_, _ ^ yea}\nlet equal_reflexive ≔ sorry }\n"),
    rejectContaining "a member must have its declared type" "in bizen of" $
      compiled (example ++ "bizen:(𝟚 option) option equal { let ≍ ≔ yea\nlet equal_reflexive ≔ sorry }\n"),
    rejectContaining "a bizen defineþ each law" "bizen is missing member 'equal_reflexive'" $
      compiled (example ++ "ilk unit:* { only: unit }\nbizen:unit equal { let ≍ ≔ {_, _ ^ yea} }\n"),
    rejectContaining "a law proof is checked against þe bizen's members" "cannot unify nay wiþ yea" $
      compiled (example ++ "ilk unit:* { only: unit }\nbizen:unit equal { let ≍ ≔ {_, _ ^ nay}\nlet equal_reflexive ≔ {_ ^ reflect} }\n"),
    rejectContaining "an ascribed sorry law must still have its declared type" "cannot unify text wiþ" $
      compiled (example ++ "ilk unit:* { only:unit } bizen:unit equal { let ≍ ≔ {_, _ ^ yea} let equal_reflexive:text ≔ sorry }"),
    expectEq "a law that holdeþ by computation is proved by reflect" (Right ()) $
      () <$ compiled (example ++ "ilk unit:* { only: unit }\nbizen:unit equal { let ≍ ≔ {_, _ ^ yea}\nlet equal_reflexive ≔ {_ ^ reflect} }\n"),
    expectEq "a bizen may define a parent þat hath no bizen" (Right True) do
      program <- compiled (example ++ "ilk _box:[α:*, *] { box:[α, α _box] }\nbizen:_box applicative {\nlet map ≔ {a box, f ^ (a f) box}\nlet pure ≔ {a ^ a box}\n}\nlet boxed:𝟚 _box ≔ (yea box) map {x ^ x}\n")
      sameNormalIn program "boxed" "yea box",
    rejectContaining "both law sides share one type" "cannot unify 𝟚 wiþ" $
      compiled (example ++ "flock bad:[α:*, *] {\nlet f:[α, α]\nlet rule:[x:α, (x f) = yea]\n}\n"),
    rejectContaining "requirements precede bare slots" "must precede bare slots" $
      compiled (example ++ "let bad:[𝟚, @:𝟚 equal, 𝟚] ≔ {x ^ x}\n"),
    rejectContaining "flock parameters are explicit" "wiþout '@'" $
      compiled (example ++ "flock bad:[@α:*, *] { let f:[α, α] }\n")
  ]
  where
    pair = "flock pair:[α:*, *] {\nlet one:α\nlet two:α\n}\n"
    shown =
      """
      show ilk 𝟚:* { yea: 𝟚, nay: 𝟚 }
      show flock equal:[α:*, *] { let ≍:[α, α, 𝟚] }
      bizen:𝟚 equal { let ≍ ≔ { yea, yea; nay, nay ^ yea, _, _ ^ nay } }
      """
    computes label expression expected = expectEq label (Right True) do
      program <- compiled example
      sameNormalIn program expression expected

selectionTests :: [Test]
selectionTests =
  [ -- as in lean, þe latest of equal-priority bizens is tried first.
    expectEq "þe latest matching bizen is chosen" (Right [True, True]) $
      traverse (\(instances, expected) -> compiled (choice ++ instances) >>= \program -> sameNormalIn program "selected @ℤ @ℤ" expected) [(blanket ++ repeated, "+1"), (repeated ++ blanket, "+0")],
    expectEq "a written priority outrankeþ declaration order" (Right True) do
      program <- compiled (choice ++ "bizen 2000:[@α:*, α choice α] { let selected ≔ +1 } " ++ blanket)
      sameNormalIn program "selected @ℤ @ℤ" "+1",
    expectEq "a fallback bizen fixeþ a carrier þat only it fiteþ" (Right True) do
      program <- compiled "let →:[α:*, β:*, *] ≔ [α, β] flock marker:[φ:[*, *, *], *] { let mark:[@α:*, α φ α, ℤ] } bizen fallback:→ marker { let mark: [_:] ≔ +7 } let value:ℤ ≔ ({x ^ x}:[ℤ, ℤ]) mark"
      sameNormalIn program "value" "+7",
    rejectContaining "wiþout a fallback, a carrier þat only one bizen fiteþ stayeþ unknown" "still unknown" $
      compiled "let →:[α:*, β:*, *] ≔ [α, β] flock marker:[φ:[*, *, *], *] { let mark:[@α:*, α φ α, ℤ] } bizen:→ marker { let mark: [_:] ≔ +7 } let value:ℤ ≔ ({x ^ x}:[ℤ, ℤ]) mark",
    expectEq "the innermost local dictionary outrankeþ a global instance" (Right True) do
      program <-
        compiled
          """
          flock tag:[α:*, *] { let value:ℤ }
          bizen:ℤ tag { let value ≔ +0 }
          let choose:[outer:ℤ tag, inner:ℤ tag, ℤ] ≔ value @ℤ
          """
      sameNormalIn program "(+1 tag_make) choose (+2 tag_make)" "+2",
    expectEq "a dictionary's private identity cannot capture source names" (Right [True, True, True]) do
      program <-
        compiled
          """
          flock tag:[α:*, *] { let value:ℤ }
          let bizen_1 ≔ +10
          bizen:ℤ tag { let value ≔ +1 }
          let bizen_0 ≔ +20
          let answer:ℤ ≔ value @ℤ
          """
      traverse (uncurry (sameNormalIn program)) [("bizen_1", "+10"), ("bizen_0", "+20"), ("answer", "+1")],
    expectEq "a law assumed wiþ sorry is reported, a proved one is not" (Right ["bizen unit second"]) $
      sorryAssumptions <$> compiled (lawClasses ++ firstInstance ++ "bizen:unit second { let right ≔ {_ ^ yea} let rule_right ≔ sorry }"),
    -- a law is an ordinary member, so its name is a top-level accessor.
    rejectContaining "two flocks cannot share a law name" "top-level name repeateþ 'rule'" $
      compiled (lawClasses ++ "flock third:[α:*, *] { let rule:[x:α, x = x] }"),
    expectEq "a law is projected like any oþer member" (Right ()) $
      () <$ compiled (lawClasses ++ firstInstance ++ "let proof:[(only left) = yea] ≔ rule @unit only"),
    rejectContaining "a law proof must hold for þe bizen's own members" "cannot unify" $
      compiled (lawClasses ++ firstInstance ++ "bizen:unit second { let right ≔ {_ ^ nay} let rule_right ≔ {_ ^ reflect} }"),
    expectEq "an inline parent's law useþ the projected dictionary and its arguments" (Right True) do
      program <-
        compiled
          """
          ilk box:[α:*, *] { wrap:[α, α box] }
          flock parent:[α:*, *] { let keep:[α, α] let rule:[x:α, (x keep) = x] }
          flock child:[α:*, @:(α box) parent, *] { let tag:ℕ }
          bizen:[@α:*, α child] {
            let keep:[x:] ≔ x
            let rule ≔ {_ ^ reflect}
            let tag ≔ 0
          }
          """
      sameNormalIn program "(+1 wrap) keep" "+1 wrap",
    expectEq "generated dictionary binders cannot capture type parameters" (Right [True, True, True]) $
      traverse
        ( \parameter -> do
            program <- compiled ("flock parent:[α:*, *] { let get:α } flock tag:[" ++ parameter ++ ":*, @:" ++ parameter ++ " parent, *] { let value:" ++ parameter ++ " } bizen:ℤ parent { let get ≔ +1 } bizen:ℤ tag { let value ≔ +2 }")
            sameNormalIn program "value @ℤ" "+2"
        )
        ["dictionary", "parent_1", "field_value"],
    -- a member þat nameþ itself useþ þe flock, as any visible name doþ; as
    -- in lean, a recursive member is an ordinary recursive let.
    rejectContaining "a member naming itself refereþ to þe flock" "no bizen of flock 'count'" $
      compiled (countClass ++ "bizen:ℕ count { let length:[ℕ, ℕ] ≔ { 0 ^ 0, n succeed ^ (n length) succeed } }"),
    expectEq "a recursive member is a recursive let" (Right True) do
      program <- compiled (countClass ++ "let natural_length:[ℕ, ℕ] ≔ { 0 ^ 0, n succeed ^ (n natural_length) succeed } bizen:ℕ count { let length ≔ natural_length }")
      sameNormalIn program "2 length" "2",
    -- `* out` letþ search find a parameter, as lean's `outParam` doþ; an
    -- unknown input parameter leaveþ þe goal waiting.
    expectEq "an output parameter is found by instance search" (Right "text") $
      compiled (converting " out") >>= (`typeOfName` "value"),
    rejectContaining "an unknown input parameter leaveþ its goal unsolved" "still unknown" $ compiled (converting ""),
    expectEq "incomparable matching bizens follow declaration order" (Right True) do
      program <- compiled (choice ++ "bizen:[@α:*, ℤ choice α] { let selected ≔ +1 } bizen:[@α:*, α choice ℤ] { let selected ≔ +2 } let answer:ℤ ≔ selected @ℤ @ℤ")
      sameNormalIn program "answer" "+2",
    rejectContaining "a candidate cannot require its own goal" "cyclic instance search" $
      compiled
        """
        flock loop:[α:*, *] { let value:α }
        bizen:[@α:*, @:α loop, α loop] { let value ≔ value }
        let answer:ℤ ≔ value
        """
  ]
  where
    lawClasses =
      """
      ilk truth:* { yea:truth, nay:truth }
      ilk unit:* { only:unit }
      flock first:[α:*, *] { let left:[α, truth] let rule:[x:α, (x left) = yea] }
      flock second:[α:*, *] { let right:[α, truth] let rule_right:[x:α, (x right) = yea] }

      """
    firstInstance = "bizen:unit first { let left ≔ {_ ^ yea} let rule ≔ {_ ^ reflect} } "
    countClass = "flock count:[α:*, *] { let length:[α, ℕ] } "
    choice = "flock choice:[α:*, β:*, *] { let selected:ℤ } "
    converting output = "flock convert:[α:*, β:*" ++ output ++ ", *] { let into:[α, β] } bizen:ℤ convert text { let into: [_:] ≔ 'one' } let value ≔ +1 into"
    blanket = "bizen:[@α:*, @β:*, α choice β] { let selected ≔ +0 } "
    repeated = "bizen:[@α:*, α choice α] { let selected ≔ +1 } "

compiled :: String -> Either String SourceProgram
compiled = compileAs "dependent_flocks.tung"
