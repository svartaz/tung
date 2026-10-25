-- classes are dictionary families; bizens are found by instance search.
module Test.DependentClass (group) where

import Data.Map.Strict qualified as Map
import Test.Compile (compileProject)
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent
import Tung.Dependent.Source (SourceProgram, sorryAssumptions, typeOfName)

group :: IO Harness.Group
group = do
  example <- exampleSource "classes.tung"
  Harness.group "dependent-class" (tests example ++ selectionTests ++ constructionTests)

tests :: String -> [Test]
tests example =
  [ computes "a bizen supplieth a member" "yea ≍ nay" "nay",
    computes "a requirement passeth the caller's bizen" "yea ≭ nay" "yea",
    computes "a bizen solveth its own requirement" "(yea some) ≍ (nay some)" "nay",
    computes "nested requirements compute" "(yea some) ≍ (yea some)" "yea",
    computes "a direct bizen outranketh a parent path" "(yea some) map {x ^ x}" "yea some",
    expectEq "a parent cometh from a child requirement" (Right True) do
      program <- compiled (example ++ "let lifted:𝟚 optional ≔ yea lift {x ^ x}\n")
      sameNormalIn program "lifted" "yea some",
    expectEq "a declaration may precede what it useth" (Right True) do
      program <- compiled ("let early:𝟚 ≔ yea ≭ nay\n" ++ example)
      sameNormalIn program "early" "yea",
    expectEq "a call of an imported function that requireth a class waiteth for the module's bizen" (Right True) do
      program <-
        compileProject
          (SourceModule "main.tung")
          "bring named.tung\nlet early:box ≔ chosen\ntype box:* { make:box }\nbizen:box named { let name ≔ make }\n"
          (Map.singleton "named.tung" "show class named:[α:*, *] { let name:α }\nshow let chosen:[@α:*, @:α named, α] ≔ name\n")
      sameNormalIn program "early" "make",
    expectEq "a shown class, its laws and bizens cross modules" (Right True) do
      program <- compileProject (SourceModule "main.tung") "bring is.tung\nlet proof:(nay ≍ nay) = yea ≔ nay ≍_reflect\nbring same.tung\nlet hath_≍:𝟚 ≔ nay ≍ nay\n" (Map.fromList [("same.tung", "bring is.tung\n" ++ shown), ("is.tung", equalitySource)])
      sameNormalIn program "hath_≍" "yea",
    expectEq "a rejected candidate doth not affect a later bizen" (Right True) do
      program <-
        compiled
          """
          type box:[α:*, *] { box_value:[α, α box] }
          class provided:[α:*, *] { let get:α }
          bizen:(ℕ box) provided { let get ≔ 0 box_value }
          bizen:(string box) provided { let get ≔ 'ok' box_value }
          let answer:string box ≔ get
          """
      sameNormalIn program "answer" "'ok' box_value",
    rejectContaining "a bizen needeth every member" "bizen is missing member 'two'" $
      compiled (example ++ pair ++ "bizen:𝟚 pair { let one ≔ yea }\n"),
    rejectContaining "a bizen cannot add members" "'three' is not a member" $
      compiled (example ++ pair ++ "bizen:𝟚 pair { let one ≔ yea\nlet two ≔ yea\nlet three ≔ yea }\n"),
    rejectContaining "a missing bizen is reported" "no bizen of class 'hath_≍'" $
      compiled (example ++ "type unit:* { only: unit }\nlet bad:𝟚 ≔ only ≍ only\n"),
    rejectContaining "a second bizen of one type is rejected" "a bizen with the same type already exists" $
      compiled (example ++ "bizen:𝟚 hath_≍ { let ≍ ≔ {_, _ ^ yea}\nlet ≍_reflect ≔ sorry }\n"),
    -- neither module seeth the other's bizen, so bring order must not choose.
    rejectContaining "bizens of one type from two imports are rejected" "bizens of class 'pointed' from" $
      compileProject
        (SourceModule "both.tung")
        "bring left.tung\nbring right.tung\n"
        ( Map.fromList
            [ ("pointed.tung", "show type two:* { yea:two, nay:two }\nshow class pointed:[α:*, *] { let point:α }\n"),
              ("left.tung", "bring pointed.tung\nbizen:two pointed { let point ≔ yea }\n"),
              ("right.tung", "bring pointed.tung\nbizen:two pointed { let point ≔ nay }\n")
            ]
        ),
    rejectContaining "a member must have its declared type" "in bizen of" $
      compiled (example ++ "bizen:(𝟚 optional) optional hath_≍ { let ≍ ≔ yea\nlet ≍_reflect ≔ sorry }\n"),
    rejectContaining "a bizen defineth each law" "bizen is missing member '≍_reflect'" $
      compiled (example ++ "type unit:* { only: unit }\nbizen:unit hath_≍ { let ≍ ≔ {_, _ ^ yea} }\n"),
    rejectContaining "a law proof is checked against the bizen's members" "cannot unify nay with yea" $
      compiled (example ++ "type unit:* { only: unit }\nbizen:unit hath_≍ { let ≍ ≔ {_, _ ^ nay}\nlet ≍_reflect ≔ {_ ^ reflect} }\n"),
    rejectContaining "an ascribed sorry law must still have its declared type" "cannot unify string with" $
      compiled (example ++ "type unit:* { only:unit } bizen:unit hath_≍ { let ≍ ≔ {_, _ ^ yea} let ≍_reflect:string ≔ sorry }"),
    expectEq "a bizen may define a parent that hath no bizen" (Right True) do
      program <- compiled (example ++ "type _box:[α:*, *] { box:[α, α _box] }\nbizen:_box applicative {\nlet map ≔ {a box, f ^ (a f) box}\nlet pure ≔ {a ^ a box}\n}\nlet boxed:𝟚 _box ≔ (yea box) map {x ^ x}\n")
      sameNormalIn program "boxed" "yea box",
    expectEq "a law proof may match in its proposition" (Right ()) $
      ()
        <$ compiled
          """
          type box:[α:*, *] { wrap:[α, α box] }
          class reflexive:[α:*, *] {
            let rule:[left:α box, right:α box, match left, right { x wrap, y wrap ^ x = x }]
          }
          bizen:ℤ reflexive { let rule ≔ { x wrap, y wrap ^ reflect } }
          let proof:+1 = +1 ≔ (+1 wrap) rule (+2 wrap)
          """,
    rejectContaining "both law sides share one type" "cannot unify 𝟚 with" $
      compiled (example ++ "class bad:[α:*, *] {\nlet f:[α, α]\nlet rule:[x:α, (x f) = yea]\n}\n"),
    rejectContaining "requirements precede bare slots" "must precede bare slots" $
      compiled (example ++ "let bad:[𝟚, @:𝟚 hath_≍, 𝟚] ≔ {x ^ x}\n"),
    rejectContaining "class parameters are explicit" "without '@'" $
      compiled (example ++ "class bad:[@α:*, *] { let f:[α, α] }\n")
  ]
  where
    pair = "class pair:[α:*, *] {\nlet one:α\nlet two:α\n}\n"
    shown =
      """
      show type 𝟚:* { yea: 𝟚, nay: 𝟚 }
      show class hath_≍:[α:*, *] { let ≍:[α, α, 𝟚] let ≍_reflect:[x:α, (x ≍ x) = yea] }
      bizen:𝟚 hath_≍ {
        let ≍ ≔ { yea, yea; nay, nay ^ yea, _, _ ^ nay }
        let ≍_reflect ≔ { yea; nay ^ reflect }
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
      program <- compiled "let →:[α:*, β:*, *] ≔ [α, β] class marker:[φ:[*, *, *], *] { let mark:[@α:*, α φ α, ℤ] } bizen fallback:→ marker { let mark: [_:] ≔ +7 } let value:ℤ ≔ ({x ^ x}:[ℤ, ℤ]) mark"
      sameNormalIn program "value" "+7",
    rejectContaining "without a fallback, a carrier that only one bizen fiteth stayeth unknown" "still unknown" $
      compiled "let →:[α:*, β:*, *] ≔ [α, β] class marker:[φ:[*, *, *], *] { let mark:[@α:*, α φ α, ℤ] } bizen:→ marker { let mark: [_:] ≔ +7 } let value:ℤ ≔ ({x ^ x}:[ℤ, ℤ]) mark",
    -- `?g x = k x equal` waiteth on `equal`'s dictionary. its first-order split
    -- `?g = k x` is ill-typed, so it is undone, and the fallback's
    -- dictionary letteth `?g` be abstracted.
    expectEq "an ill-typed approximation leaveth its equation to a fallback bizen" (Right ()) . (() <$) $
      compiled
        """
        let →:[α:*, β:*, *] ≔ [α, β]
        class marker:[φ:[*, *, *], *] { let same:[@α:*, α φ α] }
        bizen fallback:→ marker { let same: [a:] ≔ a }
        let pointwise:[@α:*, @β:*, x:α, @f:[α, β], @g:[α, β], each:[a:α, (a f) = (a g)], (x f) = (x g)] ≔ x each
        let probe:[x:ℤ, k:[ℤ, [ℤ, ℤ], ℤ], (x {p ^ p k same}) = (x {p ^ p k same})] ≔ x pointwise {p ^ reflect}
        """,
    expectEq "the innermost local dictionary outranketh a global instance" (Right True) do
      program <-
        compiled
          """
          class tag:[α:*, *] { let value:ℤ }
          bizen:ℤ tag { let value ≔ +0 }
          let choose:[outer:ℤ tag, inner:ℤ tag, ℤ] ≔ value @ℤ
          """
      sameNormalIn program "(+1 tag_make) choose (+2 tag_make)" "+2",
    expectEq "a dictionary's private identity cannot capture source names" (Right [True, True, True]) do
      program <-
        compiled
          """
          class tag:[α:*, *] { let value:ℤ }
          let bizen_1 ≔ +10
          bizen:ℤ tag { let value ≔ +1 }
          let bizen_0 ≔ +20
          let answer:ℤ ≔ value @ℤ
          """
      traverse (uncurry (sameNormalIn program)) [("bizen_1", "+10"), ("bizen_0", "+20"), ("answer", "+1")],
    expectEq "a law assumed with sorry is reported, a proved one is not" (Right ["bizen unit second"]) $
      sorryAssumptions <$> compiled (lawClasses ++ firstInstance ++ "bizen:unit second { let right ≔ {_ ^ yea} let rule_right ≔ sorry }"),
    -- a law is an ordinary member, so its name is a top-level accessor.
    rejectContaining "two classes cannot share a law name" "top-level name repeateth 'rule'" $
      compiled (lawClasses ++ "class third:[α:*, *] { let rule:[x:α, x = x] }"),
    expectEq "a law is projected like any other member" (Right ()) $
      () <$ compiled (lawClasses ++ firstInstance ++ "let proof:[(only left) = yea] ≔ rule @unit only"),
    expectEq "an inline parent's law useth the projected dictionary and its arguments" (Right True) do
      program <-
        compiled
          """
          type box:[α:*, *] { wrap:[α, α box] }
          class parent:[α:*, *] { let keep:[α, α] let rule:[x:α, (x keep) = x] }
          class child:[α:*, @:(α box) parent, *] { let tag:ℕ }
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
            program <- compiled ("class parent:[α:*, *] { let get:α } class tag:[" ++ parameter ++ ":*, @:" ++ parameter ++ " parent, *] { let value:" ++ parameter ++ " } bizen:ℤ parent { let get ≔ +1 } bizen:ℤ tag { let value ≔ +2 }")
            sameNormalIn program "value @ℤ" "+2"
        )
        ["dictionary", "parent_1", "field_value"],
    -- a member that nameth itself useth the class, as any visible name doth; as
    -- in lean, a recursive member is an ordinary recursive let.
    rejectContaining "a member naming itself refereth to the class" "no bizen of class 'count'" $
      compiled (countClass ++ "bizen:ℕ count { let length:[ℕ, ℕ] ≔ { 0 ^ 0, n next ^ (n length) next } }"),
    expectEq "a recursive member is a recursive let" (Right True) do
      program <- compiled (countClass ++ "let natural_length:[ℕ, ℕ] ≔ { 0 ^ 0, n next ^ (n natural_length) next } bizen:ℕ count { let length ≔ natural_length }")
      sameNormalIn program "2 length" "2",
    -- `* out` letth search find a parameter, as lean's `outParam` doth; an
    -- unknown input parameter leaveth the goal waiting.
    expectEq "an output parameter is found by instance search" (Right "string") $
      compiled (converting " out") >>= (`typeOfName` "value"),
    rejectContaining "an unknown input parameter leaveth its goal unsolved" "still unknown" $ compiled (converting ""),
    expectEq "incomparable matching bizens follow declaration order" (Right True) do
      program <- compiled (choice ++ "bizen:[@α:*, ℤ choice α] { let selected ≔ +1 } bizen:[@α:*, α choice ℤ] { let selected ≔ +2 } let answer:ℤ ≔ selected @ℤ @ℤ")
      sameNormalIn program "answer" "+2",
    expectEq "a nested requirement left open faileth its candidate rather than waiting" (Right ()) $
      ()
        <$ compiled
          """
          class named:[α:*, *] { let name:α }
          class base:[α:*, *] {}
          bizen:[@α:*, @:α base, α named] { let name ≔ sorry }
          class carrying:[ρ:*, μ:*, @:ρ base, @:μ named, *] {}
          let pick:[@ρ:*, @μ:*, @:ρ carrying μ, μ] ≔ name
          """,
    rejectContaining "a candidate cannot require its own goal" "cyclic instance search" $
      compiled
        """
        class loop:[α:*, *] { let value:α }
        bizen:[@α:*, @:α loop, α loop] { let value ≔ value }
        let answer:ℤ ≔ value
        """
  ]
  where
    lawClasses =
      """
      type truth:* { yea:truth, nay:truth }
      type unit:* { only:unit }
      class first:[α:*, *] { let left:[α, truth] let rule:[x:α, (x left) = yea] }
      class second:[α:*, *] { let right:[α, truth] let rule_right:[x:α, (x right) = yea] }

      """
    firstInstance = "bizen:unit first { let left ≔ {_ ^ yea} let rule ≔ {_ ^ reflect} } "
    countClass = "class count:[α:*, *] { let length:[α, ℕ] } "
    choice = "class choice:[α:*, β:*, *] { let selected:ℤ } "
    converting output = "class convert:[α:*, β:*" ++ output ++ ", *] { let into:[α, β] } bizen:ℤ convert string { let into: [_:] ≔ 'one' } let value ≔ +1 into"
    blanket = "bizen:[@α:*, @β:*, α choice β] { let selected ≔ +0 } "
    repeated = "bizen:[@α:*, α choice α] { let selected ≔ +1 } "

constructionTests :: [Test]
constructionTests =
  [ expectEq "a bizen may reuse an ordinary dictionary defined before its class" (Right True) do
      program <-
        compiled
          """
          let dictionary ≔ 7 tag_make
          class tag:* { let value:ℕ }
          let read_value:[dictionary:tag, ℕ] ≔ value
          bizen:tag { let value ≔ dictionary read_value }
          let answer:ℕ ≔ value
          """
      sameNormalIn program "answer" "7",
    expectEq "named members supply an ordinary dictionary and its dependent law" (Right True) do
      program <-
        compiled
          """
          class stable:[α:*, *] { let keep:[α, α] let rule:[x:α, (x keep) = x] }
          bizen:[@α:*, α stable] {
            let keep:[x:] ≔ x
            let rule:[x:] ≔ reflect
          }
          let proof:3 = 3 ≔ 3 rule
          """
      sameNormalIn program "proof" "(reflect:3 = 3)",
    expectEq "dictionary fields may supply a type, its value, and a dependent proof" (Right True) do
      program <-
        compiled
          """
          class chosen:* { let carrier:* let item:carrier let rule:item = item }
          bizen:chosen { let rule ≔ reflect let item ≔ 3 let carrier ≔ ℕ }
          let proof:3 = 3 ≔ rule
          """
      sameNormalIn program "proof" "(reflect:3 = 3)"
  ]

compiled :: String -> Either String SourceProgram
compiled source = compileProject (SourceModule "dependent_classes.tung") ("bring is.tung\n" ++ source) (Map.singleton "is.tung" equalitySource)
