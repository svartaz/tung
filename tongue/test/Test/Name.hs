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
  [ typeOkWith "unique imported value may be bare" "bring left.tung let ok:ℤ ≔ foo" leftOnly,
    typeErrWith "unknown qualified namespace" "bring left.tung let bad ≔ right~foo" leftOnly,
    typeOkWith "unique imported constructor may be bare" "bring left.tung let ok:left~_box ≔ box" leftOnly,
    typeErrWith "constructors are ambiguous too" "bring left.tung bring right.tung let bad ≔ box" both,
    typeOkWith "qualified constructor resolveth ambiguity" "bring left.tung bring right.tung let ok:left~_box ≔ left~box" both,
    typeErrWith "bare imported types are ambiguous" "bring left.tung bring right.tung let bad:_box ≔ left~box" both,
    typeErrWith "private values stay hidden when qualified" "bring public.tung let bad ≔ public~hidden" publicOnly,
    typeErrWith "private types stay hidden when qualified" "bring private_type.tung let bad:private_type~secret ≔ +1" privateType,
    typeOkWith "qualified lookup remaineth distinct from field access" "bring public.tung type holder: * { holder_of: [visible: string, holder] } let public ≔ 'field' holder_of let qualified:ℤ ≔ public~visible let field:string ≔ public.visible" publicOnly,
    typeOkWith "a qualified name can be re-exported" "bring middle.tung let bare:ℤ ≔ value let qualified:ℤ ≔ middle~value" reexported,
    typeErrWith "an ordinary use doth not re-export" "bring closed.tung let bad ≔ value" notReexported,
    typeErrWith "an unknown re-export is rejected" "show missing" Map.empty,
    typeErrWith "an ambiguous bare re-export is rejected" "bring left.tung bring right.tung show foo" both,
    typeErrWith "bare imported type aliases are ambiguous" "bring integer_type.tung bring string_type.tung let id:[x: token, token] ≔ x" aliasImports,
    typeOkWith "qualification resolveth type alias ambiguity" "bring integer_type.tung bring string_type.tung let integer_id:[x: integer_type~token, integer_type~token] ≔ x let string_id:[x: string_type~token, string_type~token] ≔ x" aliasImports,
    typeErrWith "an ambiguous type re-export is rejected" "bring integer_type.tung bring string_type.tung show token" aliasImports,
    typeOkWith "one show publisheth a type and its constructor" "bring data_middle.tung let ok:ℤ _box ≔ +1 box" dataReexport,
    typeOkWith "a class export carrieth methods and bizen evidence" "bring identity.tung let ok:ℤ ≔ +1 identity" identityExport,
    typeOkWith "show re-exporteth a class" "bring identity_middle.tung let ok:ℤ ≔ +1 identity" classReexport,
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
        [ ("base.tung", "show let value ≔ +1"),
          ("middle.tung", "bring base.tung show base~value")
        ]
    notReexported =
      Map.fromList
        [ ("base.tung", "show let value ≔ +1"),
          ("closed.tung", "bring base.tung")
        ]
    dataReexport =
      Map.fromList
        [ ("data_base.tung", "show type _box: [a:*, *] { box: [a, a _box] }"),
          ("data_middle.tung", "bring data_base.tung show data_base~_box, data_base~box")
        ]
    identityExport =
      Map.fromList
        [ ("identity.tung", "show class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x }")
        ]
    classReexport =
      Map.fromList
        [ ("identity_base.tung", "show class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x }"),
          ("identity_middle.tung", "bring identity_base.tung show identity_base~hath_identity, identity_base~identity")
        ]
    aliasImports =
      Map.fromList
        [ ("integer_type.tung", "show let token:* ≔ ℤ"),
          ("string_type.tung", "show let token:* ≔ string")
        ]
    dottedFileImport = Map.singleton "a.extra.tung" (moduleSource 1)
    dottedDirectoryImport = Map.singleton "pkg.one/query.tung" (moduleSource 1)

moduleSource :: Int -> String
moduleSource value = "show type _box: * { box: _box } show let foo:ℤ ≔ " ++ integerSource value

lookupCase :: Test
lookupCase = expectEq "lookup imported value" (Right "ℤ") (compileProject (SourceModule "main.tung") "bring left.tung" imports >>= (`typeOfName` "foo"))
  where
    imports = Map.fromList [("left.tung", moduleSource 1)]
