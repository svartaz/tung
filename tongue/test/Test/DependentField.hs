-- named fields of a one-constructor ilk: generated accessors and projection.
module Test.DependentField (group) where

import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness

group :: IO Harness.Group
group = do
  example <- exampleSource "dependent_fields.tung"
  library <- loadLibrary ["ilk/one.tung", "is.tung"]
  Harness.group "dependent-field" (tests library example)

tests :: Library -> String -> [Test]
tests library example =
  [ computes "a projection selecteth its field" "someone.name" "'tung'",
    computes "a value built from old fields" "older.age" "+2",
    computes "projections chain leftward" "entry.who.age" "+2",
    computes "a parameterised ilk projecteth at its argument" "pair.other" "+2",
    computes "a dependent field retaineth earlier fields" "entry.sure" "(eftbend: 'x' = 'x')",
    computesSource
      "constructor-local implicit fields retain their positions and types"
      """
      ilk packed: * { pack: [@α: *, @tag: ℤ, value: α, sure: value = value, packed] }
      let item: packed ≔ pack @ℤ @+7 +1 eftbend
      let value: ℤ ≔ item.value
      let sure: +1 = +1 ≔ item.sure
      """
      [("value", "+1"), ("sure", "(eftbend: +1 = +1)")],
    computesSource
      "an implicit family parameter retaineth its plicity"
      """
      ilk wrapped: [@α: *, *] { wrap: [value: α, wrapped @α] }
      let item: wrapped @ℤ ≔ +2 wrap @ℤ
      let value: ℤ ≔ item.value
      """
      [("value", "+2")],
    computesSource
      "field names cannot capture generated accessor binders"
      """
      ilk holder: [field·value: *, *] {
        hold: [field·0: field·value, sure: field·0 = field·0, field·value holder]
      }
      let item: ℤ holder ≔ +3 hold eftbend
      let value: ℤ ≔ item.field·0
      let sure: +3 = +3 ≔ item.sure
      """
      [("value", "+3"), ("sure", "(eftbend: +3 = +3)")],
    computesSource
      "a dependent field may share a constructor's name"
      """
      ilk flag: * { yes: flag }
      ilk sample: * { sample_of: [yes: ℤ, sure: yes = yes, sample] }
      let item: sample ≔ +4 sample_of eftbend
      let value: ℤ ≔ item.yes
      let sure: +4 = +4 ≔ item.sure
      """
      [("value", "+4"), ("sure", "(eftbend: +4 = +4)")],
    computesSource
      "nested constructor brackets retain names and ordinary shadowing"
      """
      ilk nested: * { nested_of: [value: ℤ, [value: string, sure: value = value, nested]] }
      let item: nested ≔ +1 nested_of 'last' eftbend
      let value: string ≔ item.value
      let sure: 'last' = 'last' ≔ item.sure
      """
      [("value", "'last'"), ("sure", "(eftbend: 'last' = 'last')")],
    rejectContaining "a missing field cannot be projected" "hath no field 'height'" $
      compiled (example ++ "let bad ≔ someone.height\n"),
    rejectContaining "an ilk of two constructors hath no fields" "hath no field 'x'" $
      compiled (example ++ "ilk either: * { left: [x: ℤ, either], right: [x: ℤ, either] }\nlet bad ≔ (+1 left).x\n"),
    rejectContaining "an indexed ilk hath no fields" "hath no field 'n'" $
      compiled (example ++ "ilk by_greatness: [ℤ, *] { by_greatness_of: [n: ℤ, n by_greatness] }\nlet bad ≔ (+1 by_greatness_of).n\n"),
    rejectContaining "an accessor's hidden name cannot be written" "hath no field 'name'" $
      compiled (example ++ "let bad ≔ someone person.name\n"),
    expectEq "an importer projecteth a shown ilk's fields" (Right True) do
      let shown = withModules [("people.tung", "show ilk person: * { person_of: [name: string, age: ℤ, person] }\n")] library
      program <- compileWith shown "importer.tung" "use people.tung\nlet someone: person ≔ 'tung' person_of +1\nlet name: string ≔ someone.name\n"
      sameNormalIn program "name" "'tung'",
    expectEq "the runner projecteth fields" (Right (Right 0, "tung")) $
      compileWith library "dependent_fields.tung" (example ++ "use ilk/one.tung\nlet write:[string, 𝟙 deed] ≔ 'write' fremmed\nlet main:𝟙 deed ≔ someone.name write\n")
        >>= (`runSimulated` [])
  ]
  where
    compiled source = compileWith library "dependent_fields.tung" ("use is.tung\n" ++ source)
    computes label expression expected = expectEq label (Right True) do
      program <- compiled example
      sameNormalIn program expression expected

    computesSource label source expressions = expectEq label (Right (replicate (length expressions) True)) do
      program <- compiled source
      traverse (uncurry (sameNormalIn program)) expressions
