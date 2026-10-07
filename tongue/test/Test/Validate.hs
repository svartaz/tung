-- structural reuse across scopes and duplicate labels, binders, operations, and members.
module Test.Validate (group) where

import Data.Map.Strict qualified as Map
import Test.Harness (Group, Test, checkSource)
import Test.Harness qualified as Harness
import Tung.Dependent.Source (snapshotImportPaths, sourceSnapshot)

group :: IO Group
group =
  Harness.group "validate" $
    map (uncurry validationOk) accepted
      ++ map (uncurry validationErr) rejected

accepted :: [(String, String)]
accepted =
  [ ("distinct declarations", "ilk _pair: * { pair: _pair } flock hath_≍:[a:*, *] { let same:[a, a] }"),
    ("explicit aliases override colliding defaults", "use ilk/list.tung data_list use syntax/list.tung syntax_list"),
    ("explicit aliases distinguish extension-sharing paths", "use a.tung one use a.extra.tung two"),
    ("explicit aliases distinguish dotted directories", "use pkg.one/query.tung one use pkg.two/query.tung two"),
    ("labels may repeat in separate records", "let first ≔ r{x ≔ +1} let second ≔ r{x ≔ +2}"),
    ("annotated fremmed let", "let plus:[ℤ, ℤ, ℤ] ≔ 'eke_integer' fremmed"),
    ("shared constructor heads in law parameters", "ilk _box: [a:*, *] { box: [a, a _box] } flock sameness:[a:*, *] { let rule:[x box:a _box, y box:a _box, x = y] }")
  ]

rejected :: [(String, String)]
rejected =
  [ ("colliding default use aliases", "use ilk/list.tung use syntax/list.tung"),
    ("duplicate class declarations", "show flock hath_≍:[a:*, *] {} flock hath_≍:[a:*, *] {}"),
    ("type alias and data declarations share a namespace", "ilk hath_≍: * {} let hath_≍:* ≔ ℤ"),
    ("a flock and its member share a namespace", "flock hath_≍:[a:*, *] { let hath_≍:[a, a] }"),
    ("an ilk and its constructor share a namespace", "ilk hath_≍: * { hath_≍: hath_≍ }"),
    ("a flock and a let share a namespace", "flock hath_≍:[a:*, *] {} let hath_≍ ≔ +1"),
    ("extension-sharing paths retain colliding default aliases", "use a.tung use a.extra.tung"),
    ("extensionless use path", "use ground"),
    ("qualified type alias name", "let left~right:* ≔ ℤ"),
    ("qualified data name", "ilk left~right: * { worth: left~right }"),
    ("qualified constructor name", "ilk worth: * { left~right: worth }"),
    ("duplicate data parameter", "ilk bad: [a:*, a:*, *] { bad: a bad a }"),
    ("duplicate type alias parameter", "let bad:[a:*, a:*, *] ≔ a"),
    ("duplicate constructor", "ilk bad: * { hath_≍: bad, hath_≍: bad }"),
    ("unannotated fremmed let", "let plus ≔ 'eke_integer' fremmed"),
    ("nested fremmed marker", "let bad:r{worth: ℤ} ≔ r{worth ≔ 'eke_integer' fremmed}"),
    ("qualified flock name", "flock left~right:[a:*, *] { let op:[a, a] }"),
    ("qualified flock member name", "flock left:[a:*, *] { let right~op:[a, a] }"),
    ("duplicate flock parameter", "flock bad:[a:*, a:*, *] { let op:[a, a] }"),
    ("duplicate flock member", "flock bad:[a:*, *] { let op:[a, a] let op:[a, a] }"),
    ("duplicate flock law parameter", "flock bad:[a:*, *] { let rule:[x: a, x: a, x = x] }"),
    ("a law and a member share one namespace", "flock bad:[a:*, *] { let hath_≍:[a, a] let hath_≍:[x: a, (x hath_≍) = x] }"),
    ("duplicate bizen member", "bizen:ℤ bad { let op: [x:] ≔ x let op: [y:] ≔ y }"),
    ("duplicate record type field", "let bad:r{x: ℤ, x: text} ≔ r{x ≔ +1}"),
    ("duplicate record field", "let bad ≔ r{x ≔ +1, x ≔ +2}")
  ]

validationOk, validationErr :: String -> String -> Test
validationOk name = validationCase name True
validationErr name = validationCase name False

-- a `use` path that nothing provideth is an empty module here.
validationCase :: String -> Bool -> String -> Test
validationCase name shouldPass source =
  let imports = Map.fromList [(path, "") | path <- snapshotImportPaths (sourceSnapshot source)]
      result = checkSource False source (Map.difference imports libraryPaths)
   in pure $ case (shouldPass, result) of
        (True, "type ok") -> Nothing
        (True, message) -> Just (name ++ ": unexpected rejection: " ++ message)
        (False, "type ok") -> Just (name ++ ": unexpected acceptance")
        _ -> Nothing
  where
    libraryPaths = Map.fromList [(path, ()) | path <- ["ilk/list.tung", "ground.tung"]]
