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
  example <- exampleSource "flocks.tung"
  Harness.group "dependent-flock" (tests example ++ selectionTests ++ constructionTests)

tests :: String -> [Test]
tests example =
  [ computes "a bizen supplieth a member" "yea ≍ nay" "nay",
    computes "a requirement passeth the caller's bizen" "yea ≭ nay" "yea",
    computes "a bizen solveth its own requirement" "(yea some) ≍ (nay some)" "nay",
    computes "nested requirements compute" "(yea some) ≍ (yea some)" "yea",
    computes "a direct bizen outranketh a parent path" "(yea some) warp {x ^ x}" "yea some",
    expectEq "a parent cometh from a child requirement" (Right True) do
      program <- compiled (example ++ "let lifted:𝟚 maybe ≔ yea lift {x ^ x}\n")
      sameNormalIn program "lifted" "yea some",
    expectEq "a declaration may precede what it useth" (Right True) do
      program <- compiled ("let early:𝟚 ≔ yea ≭ nay\n" ++ example)
      sameNormalIn program "early" "yea",
    expectEq "a call of an imported function that requireth a flock waiteth for the module's bizen" (Right True) do
      program <-
        compileProject
          (SourceModule "main.tung")
          "bring named.tung\nlet early:box ≔ chosen\nilk box:* { make:box }\nbizen:box named { let name ≔ make }\n"
          (Map.singleton "named.tung" "show flock named:[α:*, *] { let name:α }\nshow let chosen:[@α:*, @:α named, α] ≔ name\n")
      sameNormalIn program "early" "make",
    expectEq "a shown flock, its laws and bizens cross modules" (Right True) do
      program <- compileProject (SourceModule "main.tung") "bring is.tung\nlet soothing:(nay ≍ nay) = yea ≔ nay ≍_eftbend\nbring same.tung\nlet hath_≍:𝟚 ≔ nay ≍ nay\n" (Map.fromList [("same.tung", "bring is.tung\n" ++ shown), ("is.tung", equalitySource)])
      sameNormalIn program "hath_≍" "yea",
    expectEq "a rejected candidate doth not affect a later bizen" (Right True) do
      program <-
        compiled
          """
          ilk box:[α:*, *] { box_worth:[α, α box] }
          flock provided:[α:*, *] { let get:α }
          bizen:(ℕ box) provided { let get ≔ 0 box_worth }
          bizen:(string box) provided { let get ≔ 'ok' box_worth }
          let answer:string box ≔ get
          """
      sameNormalIn program "answer" "'ok' box_worth",
    rejectContaining "a bizen needeth every member" "bizen is missing member 'two'" $
      compiled (example ++ pair ++ "bizen:𝟚 pair { let one ≔ yea }\n"),
    rejectContaining "a bizen cannot eke members" "'three' is not a member" $
      compiled (example ++ pair ++ "bizen:𝟚 pair { let one ≔ yea\nlet two ≔ yea\nlet three ≔ yea }\n"),
    rejectContaining "a missing bizen is reported" "no bizen of flock 'hath_≍'" $
      compiled (example ++ "ilk unit:* { only: unit }\nlet bad:𝟚 ≔ only ≍ only\n"),
    rejectContaining "a second bizen of one type is rejected" "a bizen with the same ilk already exists" $
      compiled (example ++ "bizen:𝟚 hath_≍ { let ≍ ≔ {_, _ ^ yea}\nlet ≍_eftbend ≔ sorry }\n"),
    rejectContaining "a member must have its declared type" "in bizen of" $
      compiled (example ++ "bizen:(𝟚 maybe) maybe hath_≍ { let ≍ ≔ yea\nlet ≍_eftbend ≔ sorry }\n"),
    rejectContaining "a bizen defineth each law" "bizen is missing member '≍_eftbend'" $
      compiled (example ++ "ilk unit:* { only: unit }\nbizen:unit hath_≍ { let ≍ ≔ {_, _ ^ yea} }\n"),
    rejectContaining "a law proof is checked against the bizen's members" "cannot unify nay with yea" $
      compiled (example ++ "ilk unit:* { only: unit }\nbizen:unit hath_≍ { let ≍ ≔ {_, _ ^ nay}\nlet ≍_eftbend ≔ {_ ^ eftbend} }\n"),
    rejectContaining "an ascribed sorry law must still have its declared type" "cannot unify string with" $
      compiled (example ++ "ilk unit:* { only:unit } bizen:unit hath_≍ { let ≍ ≔ {_, _ ^ yea} let ≍_eftbend:string ≔ sorry }"),
    expectEq "a bizen may define a parent that hath no bizen" (Right True) do
      program <- compiled (example ++ "ilk _box:[α:*, *] { box:[α, α _box] }\nbizen:_box atfoldsome {\nlet warp ≔ {a box, f ^ (a f) box}\nlet sheer ≔ {a ^ a box}\n}\nlet boxed:𝟚 _box ≔ (yea box) warp {x ^ x}\n")
      sameNormalIn program "boxed" "yea box",
    expectEq "a law proof may match in its proposition" (Right ()) $
      ()
        <$ compiled
          """
          ilk box:[α:*, *] { wrap:[α, α box] }
          flock reflexive:[α:*, *] {
            let rule:[left:α box, right:α box, match left, right { x wrap, y wrap ^ x = x }]
          }
          bizen:ℤ reflexive { let rule ≔ { x wrap, y wrap ^ eftbend } }
          let soothing:+1 = +1 ≔ (+1 wrap) rule (+2 wrap)
          """,
    rejectContaining "both law sides share one type" "cannot unify 𝟚 with" $
      compiled (example ++ "flock bad:[α:*, *] {\nlet f:[α, α]\nlet rule:[x:α, (x f) = yea]\n}\n"),
    rejectContaining "requirements precede bare slots" "must precede bare slots" $
      compiled (example ++ "let bad:[𝟚, @:𝟚 hath_≍, 𝟚] ≔ {x ^ x}\n"),
    rejectContaining "flock parameters are explicit" "without '@'" $
      compiled (example ++ "flock bad:[@α:*, *] { let f:[α, α] }\n")
  ]
  where
    pair = "flock pair:[α:*, *] {\nlet one:α\nlet two:α\n}\n"
    shown =
      """
      show ilk 𝟚:* { yea: 𝟚, nay: 𝟚 }
      show flock hath_≍:[α:*, *] { let ≍:[α, α, 𝟚] let ≍_eftbend:[x:α, (x ≍ x) = yea] }
      bizen:𝟚 hath_≍ {
        let ≍ ≔ { yea, yea; nay, nay ^ yea, _, _ ^ nay }
        let ≍_eftbend ≔ { yea; nay ^ eftbend }
      }
      """
    computes label expression expected = expectEq label (Right True) do
      program <- compiled example
      sameNormalIn program expression expected

selectionTests :: [Test]
selectionTests =
  [ -- as in lean, the latest of equal-priority bizens is tried first.
    expectEq "the latest matching bizen is chosen" (Right [True, True]) $
      traverse (\(instances, expected) -> compiled (choice ++ instances) >>= \program -> sameNormalIn program "selected @ℤ @ℤ" expected) [(blanket ++ repeated, "+1"), (repeated ++ blanket, "+0")],
    expectEq "a written priority outranketh declaration order" (Right True) do
      program <- compiled (choice ++ "bizen 2000:[@α:*, α choice α] { let selected ≔ +1 } " ++ blanket)
      sameNormalIn program "selected @ℤ @ℤ" "+1",
    expectEq "a fallback bizen fixeth a carrier that only it fiteth" (Right True) do
      program <- compiled "let →:[α:*, β:*, *] ≔ [α, β] flock marker:[φ:[*, *, *], *] { let mark:[@α:*, α φ α, ℤ] } bizen fallback:→ marker { let mark: [_:] ≔ +7 } let worth:ℤ ≔ ({x ^ x}:[ℤ, ℤ]) mark"
      sameNormalIn program "worth" "+7",
    rejectContaining "without a fallback, a carrier that only one bizen fiteth stayeth unknown" "still unknown" $
      compiled "let →:[α:*, β:*, *] ≔ [α, β] flock marker:[φ:[*, *, *], *] { let mark:[@α:*, α φ α, ℤ] } bizen:→ marker { let mark: [_:] ≔ +7 } let worth:ℤ ≔ ({x ^ x}:[ℤ, ℤ]) mark",
    expectEq "the innermost local dictionary outranketh a global instance" (Right True) do
      program <-
        compiled
          """
          flock tag:[α:*, *] { let worth:ℤ }
          bizen:ℤ tag { let worth ≔ +0 }
          let choose:[outer:ℤ tag, inner:ℤ tag, ℤ] ≔ worth @ℤ
          """
      sameNormalIn program "(+1 tag_make) choose (+2 tag_make)" "+2",
    expectEq "a dictionary's private identity cannot capture source names" (Right [True, True, True]) do
      program <-
        compiled
          """
          flock tag:[α:*, *] { let worth:ℤ }
          let bizen_1 ≔ +10
          bizen:ℤ tag { let worth ≔ +1 }
          let bizen_0 ≔ +20
          let answer:ℤ ≔ worth @ℤ
          """
      traverse (uncurry (sameNormalIn program)) [("bizen_1", "+10"), ("bizen_0", "+20"), ("answer", "+1")],
    expectEq "a law assumed with sorry is reported, a proved one is not" (Right ["bizen unit second"]) $
      sorryAssumptions <$> compiled (lawClasses ++ firstInstance ++ "bizen:unit second { let right ≔ {_ ^ yea} let rule_right ≔ sorry }"),
    -- a law is an ordinary member, so its name is a top-level accessor.
    rejectContaining "two flocks cannot share a law name" "top-level name repeateth 'rule'" $
      compiled (lawClasses ++ "flock third:[α:*, *] { let rule:[x:α, x = x] }"),
    expectEq "a law is projected like any other member" (Right ()) $
      () <$ compiled (lawClasses ++ firstInstance ++ "let soothing:[(only left) = yea] ≔ rule @unit only"),
    expectEq "an inline parent's law useth the projected dictionary and its arguments" (Right True) do
      program <-
        compiled
          """
          ilk box:[α:*, *] { wrap:[α, α box] }
          flock parent:[α:*, *] { let keep:[α, α] let rule:[x:α, (x keep) = x] }
          flock child:[α:*, @:(α box) parent, *] { let tag:ℕ }
          bizen:[@α:*, α child] {
            let keep:[x:] ≔ x
            let rule ≔ {_ ^ eftbend}
            let tag ≔ 0
          }
          """
      sameNormalIn program "(+1 wrap) keep" "+1 wrap",
    expectEq "generated dictionary binders cannot capture type parameters" (Right [True, True, True]) $
      traverse
        ( \parameter -> do
            program <- compiled ("flock parent:[α:*, *] { let get:α } flock tag:[" ++ parameter ++ ":*, @:" ++ parameter ++ " parent, *] { let worth:" ++ parameter ++ " } bizen:ℤ parent { let get ≔ +1 } bizen:ℤ tag { let worth ≔ +2 }")
            sameNormalIn program "worth @ℤ" "+2"
        )
        ["dictionary", "parent_1", "field_worth"],
    -- a member that nameth itself useth the flock, as any visible name doth; as
    -- in lean, a recursive member is an ordinary recursive let.
    rejectContaining "a member naming itself refereth to the flock" "no bizen of flock 'rime'" $
      compiled (countClass ++ "bizen:ℕ rime { let length:[ℕ, ℕ] ≔ { 0 ^ 0, n heir ^ (n length) heir } }"),
    expectEq "a recursive member is a recursive let" (Right True) do
      program <- compiled (countClass ++ "let kindful_length:[ℕ, ℕ] ≔ { 0 ^ 0, n heir ^ (n kindful_length) heir } bizen:ℕ rime { let length ≔ kindful_length }")
      sameNormalIn program "2 length" "2",
    -- `* out` letth search find a parameter, as lean's `outParam` doth; an
    -- unknown input parameter leaveth the goal waiting.
    expectEq "an output parameter is found by instance search" (Right "string") $
      compiled (converting " out") >>= (`typeOfName` "worth"),
    rejectContaining "an unknown input parameter leaveth its goal unsolved" "still unknown" $ compiled (converting ""),
    expectEq "incomparable matching bizens follow declaration order" (Right True) do
      program <- compiled (choice ++ "bizen:[@α:*, ℤ choice α] { let selected ≔ +1 } bizen:[@α:*, α choice ℤ] { let selected ≔ +2 } let answer:ℤ ≔ selected @ℤ @ℤ")
      sameNormalIn program "answer" "+2",
    expectEq "a nested requirement left open faileth its candidate rather than waiting" (Right ()) $
      ()
        <$ compiled
          """
          flock named:[α:*, *] { let name:α }
          flock base:[α:*, *] {}
          bizen:[@α:*, @:α base, α named] { let name ≔ sorry }
          flock carrying:[ρ:*, μ:*, @:ρ base, @:μ named, *] {}
          let pick:[@ρ:*, @μ:*, @:ρ carrying μ, μ] ≔ name
          """,
    rejectContaining "a candidate cannot require its own goal" "cyclic instance search" $
      compiled
        """
        flock loop:[α:*, *] { let worth:α }
        bizen:[@α:*, @:α loop, α loop] { let worth ≔ worth }
        let answer:ℤ ≔ worth
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
    firstInstance = "bizen:unit first { let left ≔ {_ ^ yea} let rule ≔ {_ ^ eftbend} } "
    countClass = "flock rime:[α:*, *] { let length:[α, ℕ] } "
    choice = "flock choice:[α:*, β:*, *] { let selected:ℤ } "
    converting output = "flock convert:[α:*, β:*" ++ output ++ ", *] { let into:[α, β] } bizen:ℤ convert string { let into: [_:] ≔ 'one' } let worth ≔ +1 into"
    blanket = "bizen:[@α:*, @β:*, α choice β] { let selected ≔ +0 } "
    repeated = "bizen:[@α:*, α choice α] { let selected ≔ +1 } "

constructionTests :: [Test]
constructionTests =
  [ expectEq "a bizen may reuse an ordinary dictionary defined before its flock" (Right True) do
      program <-
        compiled
          """
          let dictionary ≔ 7 tag_make
          flock tag:* { let worth:ℕ }
          let read_worth:[dictionary:tag, ℕ] ≔ worth
          bizen:tag { let worth ≔ dictionary read_worth }
          let answer:ℕ ≔ worth
          """
      sameNormalIn program "answer" "7",
    expectEq "named members supply an ordinary dictionary and its dependent law" (Right True) do
      program <-
        compiled
          """
          flock stable:[α:*, *] { let keep:[α, α] let rule:[x:α, (x keep) = x] }
          bizen:[@α:*, α stable] {
            let keep:[x:] ≔ x
            let rule:[x:] ≔ eftbend
          }
          let soothing:3 = 3 ≔ 3 rule
          """
      sameNormalIn program "soothing" "(eftbend:3 = 3)",
    expectEq "dictionary fields may supply a type, its value, and a dependent proof" (Right True) do
      program <-
        compiled
          """
          flock chosen:* { let carrier:* let item:carrier let rule:item = item }
          bizen:chosen { let rule ≔ eftbend let item ≔ 3 let carrier ≔ ℕ }
          let soothing:3 = 3 ≔ rule
          """
      sameNormalIn program "soothing" "(eftbend:3 = 3)"
  ]

compiled :: String -> Either String SourceProgram
compiled source = compileProject (SourceModule "dependent_flocks.tung") ("bring is.tung\n" ++ source) (Map.singleton "is.tung" equalitySource)
