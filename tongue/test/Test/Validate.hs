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
  [ ("distinct declarations", "type _pair: * { pair: _pair } class hath_≍:[a:*, *] { let same:[a, a] }"),
    ("explicit aliases override colliding defaults", "bring type/list.tung data_list bring syntax/list.tung syntax_list"),
    ("explicit aliases distinguish extension-sharing paths", "bring a.tung one bring a.extra.tung two"),
    ("explicit aliases distinguish dotted directories", "bring pkg.one/query.tung one bring pkg.two/query.tung two"),
    ("field names may repeat in separate types", "type first: * { first_of: [x: ℤ, first] } type second: * { second_of: [x: ℤ, second] }")
  ]

rejected :: [(String, String)]
rejected =
  [ ("colliding default use aliases", "bring type/list.tung bring syntax/list.tung"),
    ("duplicate class declarations", "show class hath_≍:[a:*, *] {} class hath_≍:[a:*, *] {}"),
    ("type alias and data declarations share a namespace", "type hath_≍: * {} let hath_≍:* ≔ ℤ"),
    ("a class and its member share a namespace", "class hath_≍:[a:*, *] { let hath_≍:[a, a] }"),
    ("a type and its constructor share a namespace", "type hath_≍: * { hath_≍: hath_≍ }"),
    ("a class and a let share a namespace", "class hath_≍:[a:*, *] {} let hath_≍ ≔ +1"),
    ("extension-sharing paths retain colliding default aliases", "bring a.tung bring a.extra.tung"),
    ("extensionless bring path", "bring often"),
    ("qualified type alias name", "let left~right:* ≔ ℤ"),
    ("qualified data name", "type left~right: * { value: left~right }"),
    ("qualified constructor name", "type value: * { left~right: value }"),
    ("duplicate data parameter", "type bad: [a:*, a:*, *] { bad: a bad a }"),
    ("duplicate type alias parameter", "let bad:[a:*, a:*, *] ≔ a"),
    ("duplicate constructor", "type bad: * { hath_≍: bad, hath_≍: bad }"),
    ("qualified class name", "class left~right:[a:*, *] { let op:[a, a] }"),
    ("qualified class member name", "class left:[a:*, *] { let right~op:[a, a] }"),
    ("duplicate class parameter", "class bad:[a:*, a:*, *] { let op:[a, a] }"),
    ("duplicate class member", "class bad:[a:*, *] { let op:[a, a] let op:[a, a] }"),
    ("duplicate class law parameter", "bring is.tung class bad:[a:*, *] { let rule:[x: a, x: a, x = x] }"),
    ("a law and a member share one namespace", "bring is.tung class bad:[a:*, *] { let hath_≍:[a, a] let hath_≍:[x: a, (x hath_≍) = x] }"),
    ("duplicate bizen member", "bizen:ℤ bad { let op: [x:] ≔ x let op: [y:] ≔ y }"),
    ("duplicate field", "type bad: * { bad_of: [x: ℤ, x: string, bad] }")
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
    libraryPaths = Map.fromList [(path, ()) | path <- ["type/list.tung", "often.tung", "is.tung"]]
