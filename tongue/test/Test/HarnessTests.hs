-- test selection must preserve group order and reject incomplete selections.
module Test.HarnessTests (group) where

import Test.Harness qualified as Harness

group :: IO Harness.Group
group = Harness.group "harness" [selection]
  where
    selection =
      Harness.expectEq
        "explicit selections reject unknown and empty groups"
        [Right [1, 2], Left "unknown test groups: absent", Left "unknown test groups: absent", Left "no test groups selected"]
        (map (Harness.selectGroups [("first", 1 :: Int), ("second", 2)]) ["second first", "absent", "first absent", " "])
