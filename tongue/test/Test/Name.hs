-- bare and qualified lookup, ambiguity, exports, shadowing, and record access.
module Test.Name (group) where

import Data.Map.Strict qualified as Map
import Test.Compile (compileProject)
import Test.Harness (Group, Test, expectEq, integerSource, typeErrWith, typeOkWith)
import Test.Harness qualified as Harness
import Tung (ModuleId (..))
import Tung.Dependent.Source (typeOfName)

group :: IO Group
group = Harness.group "name" (resolutionCases ++ [lookupCase])

resolutionCases :: [Test]
resolutionCases =
  [ typeOkWith "unique imported worth may be bare" "use left.tung let ok:ℤ ≔ foo" leftOnly,
    typeErrWith "two imported values are ambiguous" "use left.tung use right.tung let bad:ℤ ≔ foo" both,
    typeOkWith "qualification resolveth worth ambiguity" "use left.tung use right.tung let ok:r{left:ℤ, right:ℤ} ≔ r{left ≔ left~foo, right ≔ right~foo}" both,
    typeErrWith "unknown qualified namespace" "use left.tung let bad ≔ right~foo" leftOnly,
    typeOkWith "local worth shadows imported values" "use left.tung use right.tung let foo ≔ +3 let ok:ℤ ≔ foo" both,
    typeOkWith "unique imported constructor may be bare" "use left.tung let ok:left~_box ≔ box" leftOnly,
    typeErrWith "constructors are ambiguous too" "use left.tung use right.tung let bad ≔ box" both,
    typeOkWith "qualified constructor resolveth ambiguity" "use left.tung use right.tung let ok:left~_box ≔ left~box" both,
    typeErrWith "bare imported types are ambiguous" "use left.tung use right.tung let bad:_box ≔ left~box" both,
    typeOkWith "qualified type resolveth ambiguity" "use left.tung use right.tung let ok:left~_box ≔ left~box" both,
    typeErrWith "exports hide unshown values" "use public.tung let bad ≔ hidden" publicOnly,
    typeErrWith "private values stay hidden when qualified" "use public.tung let bad ≔ public~hidden" publicOnly,
    typeErrWith "private types stay hidden when qualified" "use private_type.tung let bad:private_type~secret ≔ +1" privateType,
    typeOkWith "shown values stay bare" "use public.tung let ok:ℤ ≔ visible" publicOnly,
    typeOkWith "qualified lookup remaineth distinct from record access" "use public.tung let public ≔ r{visible ≔ 'record'} let qualified:ℤ ≔ public~visible let field:text ≔ public.visible" publicOnly,
    typeOkWith "record access is explicit" "let worth ≔ r{field ≔ +1} let ok:ℤ ≔ worth.field" Map.empty,
    typeOkWith "a qualified name can be re-exported" "use middle.tung let ok:r{bare:ℤ, qualified:ℤ} ≔ r{bare ≔ worth, qualified ≔ middle~worth}" reexported,
    typeErrWith "an ordinary use doth not re-export" "use closed.tung let bad ≔ worth" notReexported,
    typeErrWith "an unknown re-export is rejected" "show missing" Map.empty,
    typeErrWith "an ambiguous bare re-export is rejected" "use left.tung use right.tung show foo" both,
    typeErrWith "bare imported type aliases are ambiguous" "use integer_type.tung use text_type.tung let id:[x: token, token] ≔ x" aliasImports,
    typeOkWith "qualification resolveth type alias ambiguity" "use integer_type.tung use text_type.tung let integer_id:[x: integer_type~token, integer_type~token] ≔ x let text_id:[x: text_type~token, text_type~token] ≔ x" aliasImports,
    typeErrWith "an ambiguous type re-export is rejected" "use integer_type.tung use text_type.tung show token" aliasImports,
    typeOkWith "one show publisheth a type and its constructor" "use data_middle.tung let ok:ℤ _box ≔ +1 box" dataReexport,
    typeOkWith "a flock export carrieth methods and bizen evidence" "use sameness.tung let ok:ℤ ≔ +1 sameness" identityExport,
    typeOkWith "show re-exporteth a flock" "use sameness_middle.tung let ok:ℤ ≔ +1 sameness" classReexport,
    typeOkWith "constructor pattern is exhaustive after re-export" "use data_middle.tung let unbox:[ℤ _box, ℤ] ≔ { x box ^ x }" dataWholeReexport,
    typeOkWith "dotted filename preserveth its short default alias" "use a.extra.tung let ok:ℤ ≔ a~foo" dottedFileImport,
    typeOkWith "a dotted directory doth not alter the default basename alias" "use pkg.one/query.tung let ok:ℤ ≔ query~foo" dottedDirectoryImport
  ]
  where
    leftOnly = Map.fromList [("left.tung", moduleSource 1)]
    both = Map.fromList [("left.tung", moduleSource 1), ("right.tung", moduleSource 2)]
    publicOnly = Map.fromList [("public.tung", "let hidden ≔ +0 show let visible ≔ +1")]
    privateType = Map.fromList [("private_type.tung", "let secret:* ≔ ℤ")]
    reexported =
      Map.fromList
        [ ("base.tung", "show let worth ≔ +1"),
          ("middle.tung", "use base.tung show base~worth")
        ]
    notReexported =
      Map.fromList
        [ ("base.tung", "show let worth ≔ +1"),
          ("closed.tung", "use base.tung")
        ]
    dataReexport =
      Map.fromList
        [ ("data_base.tung", "show ilk _box: [a:*, *] { box: [a, a _box] }"),
          ("data_middle.tung", "use data_base.tung show data_base~_box, data_base~box")
        ]
    dataWholeReexport =
      Map.fromList
        [ ("data_base.tung", "show ilk _box: [a:*, *] { box: [a, a _box] }"),
          ("data_middle.tung", "use data_base.tung show data_base~_box, data_base~box")
        ]
    identityExport =
      Map.fromList
        [ ("sameness.tung", "show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x }")
        ]
    classReexport =
      Map.fromList
        [ ("sameness_base.tung", "show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x }"),
          ("sameness_middle.tung", "use sameness_base.tung show sameness_base~hath_sameness, sameness_base~sameness")
        ]
    aliasImports =
      Map.fromList
        [ ("integer_type.tung", "show let token:* ≔ ℤ"),
          ("text_type.tung", "show let token:* ≔ text")
        ]
    dottedFileImport = Map.singleton "a.extra.tung" (moduleSource 1)
    dottedDirectoryImport = Map.singleton "pkg.one/query.tung" (moduleSource 1)

moduleSource :: Int -> String
moduleSource value = "show ilk _box: * { box: _box } show let foo:ℤ ≔ " ++ integerSource value

lookupCase :: Test
lookupCase = expectEq "lookup imported worth" (Right "ℤ") (compileProject (SourceModule "main.tung") "use left.tung" imports >>= (`typeOfName` "foo"))
  where
    imports = Map.fromList [("left.tung", moduleSource 1)]
