-- closed records: types, values, projection, and update.
module Test.DependentRecord (group) where

import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent.Source (SourceProgram)

group :: IO Harness.Group
group = do
  example <- exampleSource "dependent_records.tung"
  library <- loadLibrary ["ilk/one.tung"]
  Harness.group "dependent-record" (tests library example)

tests :: Library -> String -> [Test]
tests library example =
  [ computes "a projection selecteþ its field" "someone.name" "'tung'",
    computes "an update setþ a field from the old record" "older.age" "+2",
    computes "an update may remove a field" "anonymous" "r{age ≔ +1}",
    computes "projections chain leftward" "entry.who.age" "+2",
    computes "field order doth not change a record" "r{name ≔ 'tung', age ≔ +1}" "someone",
    computes "a projection of a variable stayeþ neutral" "{p:person ^ p.age}" "{p:person ^ p.age}",
    expectEq "field order doth not change a record type" (Right True) $
      True <$ compiled (example ++ "let same:r{age:ℤ, name:text} ≔ someone\n"),
    rejectContaining "a repeated field is an error" "record field 'age' is repeated" $
      compiled (example ++ "let bad ≔ r{age ≔ +1, age ≔ +2}\n"),
    rejectContaining "a missing field cannot be projected" "record hath no field 'height'" $
      compiled (example ++ "let bad ≔ someone.height\n"),
    rejectContaining "a record must match its expected fields" "record fields differ" $
      compiled (example ++ "let bad:person ≔ r{name ≔ 'x'}\n"),
    rejectContaining "an update cannot remove a missing field" "no field 'height' to remove" $
      compiled (example ++ "let bad ≔ r{≔ someone, - height}\n"),
    rejectContaining "projection needeþ a record" "requireþ a record" $
      compiled (example ++ "let bad ≔ name.age\n"),
    rejectContaining "a family cannot hide recursion in a record" "direct saturated family application" $
      compiled (example ++ "ilk bad:* { make:[r{next:bad}, bad] }\n"),
    expectEq "the runner projecteþ fields" (Right (Right 0, "tung")) $
      compiledWith (example ++ "use ilk/one.tung\nlet write:[text, 𝟙 deed] ≔ 'write' fremmed\nlet main:𝟙 deed ≔ name write\n")
        >>= (`runSimulated` [])
  ]
  where
    compiledWith = compileWith library "dependent_records.tung"
    computes label expression expected = expectEq label (Right True) do
      program <- compiled example
      sameNormalIn program expression expected

compiled :: String -> Either String SourceProgram
compiled = compileAs "dependent_records.tung"
