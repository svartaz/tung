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
  [ typeOkWith "unique imported worth may be bare" "bring left.tung let ok:ℤ ≔ foo" leftOnly,
    typeErrWith "unknown qualified namespace" "bring left.tung let bad ≔ right~foo" leftOnly,
    typeOkWith "unique imported constructor may be bare" "bring left.tung let ok:left~_box ≔ box" leftOnly,
    typeErrWith "constructors are ambiguous too" "bring left.tung bring right.tung let bad ≔ box" both,
    typeOkWith "qualified constructor resolveth ambiguity" "bring left.tung bring right.tung let ok:left~_box ≔ left~box" both,
    typeErrWith "bare imported types are ambiguous" "bring left.tung bring right.tung let bad:_box ≔ left~box" both,
    typeErrWith "private values stay hidden when qualified" "bring public.tung let bad ≔ public~hidden" publicOnly,
    typeErrWith "private types stay hidden when qualified" "bring private_type.tung let bad:private_type~secret ≔ +1" privateType,
    typeOkWith "qualified lookup remaineth distinct from field access" "bring public.tung ilk holder: * { holder_of: [visible: string, holder] } let public ≔ 'field' holder_of let qualified:ℤ ≔ public~visible let field:string ≔ public.visible" publicOnly,
    typeOkWith "a qualified name can be re-exported" "bring middle.tung let bare:ℤ ≔ worth let qualified:ℤ ≔ middle~worth" reexported,
    typeErrWith "an ordinary use doth not re-export" "bring closed.tung let bad ≔ worth" notReexported,
    typeErrWith "an unknown re-export is rejected" "show missing" Map.empty,
    typeErrWith "an ambiguous bare re-export is rejected" "bring left.tung bring right.tung show foo" both,
    typeErrWith "bare imported type aliases are ambiguous" "bring wholetale_type.tung bring string_type.tung let id:[x: token, token] ≔ x" aliasImports,
    typeOkWith "qualification resolveth type alias ambiguity" "bring wholetale_type.tung bring string_type.tung let wholetale_id:[x: wholetale_type~token, wholetale_type~token] ≔ x let string_id:[x: string_type~token, string_type~token] ≔ x" aliasImports,
    typeErrWith "an ambiguous type re-export is rejected" "bring wholetale_type.tung bring string_type.tung show token" aliasImports,
    typeOkWith "one show publisheth a type and its constructor" "bring data_middle.tung let ok:ℤ _box ≔ +1 box" dataReexport,
    typeOkWith "a flock export carrieth methods and bizen evidence" "bring sameness.tung let ok:ℤ ≔ +1 sameness" identityExport,
    typeOkWith "show re-exporteth a flock" "bring sameness_middle.tung let ok:ℤ ≔ +1 sameness" classReexport,
    typeOkWith "constructor pattern is exhaustive after re-export" "bring data_middle.tung let unbox:[ℤ _box, ℤ] ≔ { x box ^ x }" dataReexport,
    typeOkWith "dotted filename preserveth its short default alias" "bring a.extra.tung let ok:ℤ ≔ a~foo" dottedFileImport,
    typeOkWith "a dotted directory doth not alter the default basename alias" "bring pkg.one/query.tung let ok:ℤ ≔ query~foo" dottedDirectoryImport
  ]
  where
    leftOnly = Map.fromList [("left.tung", moduleSource 1)]
    both = Map.fromList [("left.tung", moduleSource 1), ("right.tung", moduleSource 2)]
    publicOnly = Map.fromList [("public.tung", "let hidden ≔ +0 show let visible ≔ +1")]
    privateType = Map.fromList [("private_type.tung", "let secret:* ≔ ℤ")]
    reexported =
      Map.fromList
        [ ("base.tung", "show let worth ≔ +1"),
          ("middle.tung", "bring base.tung show base~worth")
        ]
    notReexported =
      Map.fromList
        [ ("base.tung", "show let worth ≔ +1"),
          ("closed.tung", "bring base.tung")
        ]
    dataReexport =
      Map.fromList
        [ ("data_base.tung", "show ilk _box: [a:*, *] { box: [a, a _box] }"),
          ("data_middle.tung", "bring data_base.tung show data_base~_box, data_base~box")
        ]
    identityExport =
      Map.fromList
        [ ("sameness.tung", "show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x }")
        ]
    classReexport =
      Map.fromList
        [ ("sameness_base.tung", "show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x }"),
          ("sameness_middle.tung", "bring sameness_base.tung show sameness_base~hath_sameness, sameness_base~sameness")
        ]
    aliasImports =
      Map.fromList
        [ ("wholetale_type.tung", "show let token:* ≔ ℤ"),
          ("string_type.tung", "show let token:* ≔ string")
        ]
    dottedFileImport = Map.singleton "a.extra.tung" (moduleSource 1)
    dottedDirectoryImport = Map.singleton "pkg.one/query.tung" (moduleSource 1)

moduleSource :: Int -> String
moduleSource value = "show ilk _box: * { box: _box } show let foo:ℤ ≔ " ++ integerSource value

lookupCase :: Test
lookupCase = expectEq "lookup imported worth" (Right "ℤ") (compileProject (SourceModule "main.tung") "bring left.tung" imports >>= (`typeOfName` "foo"))
  where
    imports = Map.fromList [("left.tung", moduleSource 1)]
