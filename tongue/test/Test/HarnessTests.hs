-- test selection must preserve group order and reject incomplete selections.
module Test.HarnessTests (group) where

import Control.Exception (evaluate)
import Data.List (isInfixOf)
import Data.Map.Strict qualified as Map
import Test.Harness qualified as Harness

group :: IO Harness.Group
group = Harness.group "harness" [selection, fixtureOverrides]
  where
    selection =
      Harness.expectEq
        "explicit selections reject unknown and empty groups"
        [Right [1, 2], Left "unknown test groups: absent", Left "unknown test groups: absent", Left "no test groups selected"]
        (map (Harness.selectGroups [("first", 1 :: Int), ("second", 2)]) ["second first", "absent", "first absent", " "])

-- a changed dependency must invalidate its importer without changing later tests.
fixtureOverrides :: Harness.Test
fixtureOverrides = do
  let direct = "use ilk/two.tung let answer:𝟚 ≔ nay"
      transitive = "use flock/algebra/whole/hath_naught.tung"
      changed = Map.singleton "ilk/two.tung" "show ilk 𝟚:* { true:𝟚, false:𝟚 }"
  before <- evaluate (Harness.checkSource False transitive Map.empty)
  directResult <- evaluate (Harness.checkSource False direct changed)
  transitiveResult <- evaluate (Harness.checkSource False transitive changed)
  after <- evaluate (Harness.checkSource False transitive Map.empty)
  Harness.expectEq
    "fixture overrides invalidate direct and transitive imports and stay isolated"
    ("type ok", [True, True], "type ok")
    (before, map (isInfixOf "unknown name 'nay'") [directResult, transitiveResult], after)
