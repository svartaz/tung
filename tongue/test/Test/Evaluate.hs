-- checked interactive evaluation, dictionaries, and deeds.
module Test.Evaluate (group) where

import Control.Exception (bracket)
import Data.List (stripPrefix)
import Data.Map.Strict qualified as Map
import Data.Time.Clock.POSIX (getPOSIXTime)
import System.Environment qualified as Environment
import Test.Harness (Group, Test, evalOkWith, evalTypeErrWith, integerSource)
import Test.Harness qualified as Harness
import Text.Read (readMaybe)

group :: IO Group
group =
  Harness.group "evaluate" (map (evalCase Map.empty) deterministic ++ map (typeErrorCase Map.empty) typeErrors ++ importedCases Map.empty)

deterministic :: [(String, String, String)]
deterministic =
  [ ("explicit type inputs are erased beside worth inputs", "let f:[@a:*, @b:*, x:a, _:b, a] ≔ x yield +1 f @ℤ @string 'x'", "eval ok: +1"),
    ("instance method type inputs are erased", "let id:[@a:*, x:a, a] ≔ x flock owner:[a:*, *] { let copy:[@b:*, a, b, b] } bizen:ℤ owner { let copy:[@c:*, _:ℤ, x:c, c] ≔ x id @c } yield +1 copy 'x'", "eval ok: 'x'"),
    ("unused type inputs requireth no runtime argument", "let worth:[@a:*, ℤ] ≔ +7 yield worth @string", "eval ok: +7"),
    ("higher-rank argument is erased and instantiated twice", "ilk pair: * { pair_of: [tale: ℤ, word: string, pair] } let both:[f:[@a:*, a, a], pair] ≔ (+1 f) pair_of ('x' f) let id: [@a:*, x: a, a] ≔ x yield (id both).tale", "eval ok: +1"),
    ("polymorphic return needs no runtime type arguments", "let make:[_:ℤ, [@a:*, a, a]] ≔ {x ^ x} yield 'yes' (+1 make)", "eval ok: 'yes'"),
    ("left-associated sequence", "bring often.tung yield <{-+, +10, +3, +2}", "eval ok: +9"),
    ("right-associated sequence", "bring often.tung yield >{-+, +10, +3, +2}", "eval ok: -11"),
    ("nested brace forms share type and expression boundaries", "bring often.tung ilk inner: * { inner_of: [worth: ℤ, inner] } ilk outer: * { outer_of: [callback: [ℤ, ℤ], nested: inner, outer] } let record:outer ≔ {x ^ <{+, x, +1}} outer_of (+2 inner_of) yield record.nested.worth record.callback", "eval ok: +3"),
    ("term type ascription is erased before evaluation", "bring often.tung yield (+1 + +2: ℤ)", "eval ok: +3"),
    ("ascribed anonymous function remaineth recursive", "bring often.tung let factorial ≔ ({ 0 ^ 1, n heir ^ (n heir) · (n factorial) }: [ℕ, ℕ]) yield 5 factorial", "eval ok: 120"),
    ("ℤ arithmetic is arbitrary precision", "bring often.tung yield +999999999999999999999999999999 + +1", "eval ok: +1000000000000000000000000000000"),
    ("fremmed key selecteth a host function independently of the let name", "let plus:[ℤ, ℤ, ℤ] ≔ 'eke_wholetale' fremmed yield +1 plus +2", "eval ok: +3"),
    ("unicode string", "yield 'λ字'", "eval ok: 'λ字'"),
    ("unicode control rendering useth decimal terminator", "yield `\\1;", "eval ok: `\\1;"),
    ("float arithmetic", "bring often.tung yield 0.5 + 0.25", "eval ok: 0.75"),
    ("string becometh a float", "bring often.tung bring ilk/maybe.tung let parsed:float maybe ≔ '0.5' from_string yield parsed", "eval ok: (0.5 some)"),
    ("unparsable string yieldeth none", "bring often.tung bring ilk/maybe.tung let parsed:float maybe ≔ 'not a float' from_string yield parsed", "eval ok: none"),
    ("float division useth the division sign", "bring often.tung yield 6.0 ÷ 4.0", "eval ok: 1.5"),
    ("float division by naught followeth ieee", "bring often.tung yield 1.0 ÷ 0.0", "eval ok: Infinity"),
    ("an infinite float floor yieldeth none", "bring _fremmed.tung yield (1.0 deal_float 0.0) ⌊", "eval ok: none"),
    ("a nan float floor yieldeth none", "bring _fremmed.tung yield (0.0 deal_float 0.0) ⌊", "eval ok: none"),
    ("float is ignoreth literal spelling", "bring often.tung ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } yield 1.0 ≍ 1.00", "eval ok: yea"),
    ("bracketed natural constructors construct and match", "ilk nat: * { naught: nat, suc: [nat, nat] } yield match naught suc { x suc ^ +1, naught ^ +0 }", "eval ok: +1"),
    ("bracketed list constructors preserve native ABI", "ilk list: [a:*, *] { empty: a list, ‥: [a, a list, a list] } yield match (+1 ‥ empty) { first ‥ _ ^ first, empty ^ +0 }", "eval ok: +1"),
    ("indexed constructor match useth its refined payload", indexedUnpackSource ++ "yield (+3 integer) unpack", "eval ok: +3"),
    ("indexed constructor match useth its other branch", indexedUnpackSource ++ "yield ('hi' textual) unpack", "eval ok: 'hi'"),
    ("float ordering is numeric", "bring often.tung ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } yield 2.0 ≤ 10.0", "eval ok: yea"),
    ("curried half application", "bring often.tung let hath_+: [a: ℤ, b: ℤ, ℤ] ≔ a + b let eke_one ≔ +1 hath_+ yield +2 eke_one", "eval ok: +3"),
    ("local recursive function", "bring often.tung ilk nat: * { naught: nat, suc: [nat, nat] } let rime ≔ (let loop: [nat, ℤ] ≔ { naught ^ +0, n suc ^ +1 + (n loop) } yield loop) yield ((naught suc) suc) rime", "eval ok: +2"),
    ("recursive calls retain inferred evidence", "bring often.tung flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +1 } let loop: [ℕ, ℤ, ℤ] ≔ { 0, x ^ x sameness, n heir, x ^ n loop x } yield 2 loop +3", "eval ok: +4"),
    ("recursive evidence surviveth a nested polymorphic binding", "bring often.tung flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +1 } let loop: [ℕ, ℤ, ℤ] ≔ { 0, x ^ x sameness, n heir, x ^ (let echo: [y:] ≔ y sameness yield (n loop x) echo) } yield 2 loop +3", "eval ok: +6"),
    ("dollar function segment", "bring often.tung let f: [x: ℤ, ℤ] ≔ x + +1 let h: [x: ℤ, y: ℤ, z: ℤ, ℤ] ≔ (x + y) · z yield +1 f $h +2 +3", "eval ok: +12"),
    ("lexical closure", "let x ≔ +1 let f: [_: ℤ, ℤ] ≔ x yield (let x ≔ +2 yield +0 f)", "eval ok: +1"),
    ("sequential shadowing preserveth each preceding local", "bring often.tung yield (let worth ≔ +1 let worth ≔ worth + +1 let worth ≔ worth + +1 yield worth)", "eval ok: +3"),
    ("nested same-string pattern binders remain distinct", "bring often.tung yield match +1 { worth ^ (match +2 { worth ^ worth }) + worth }", "eval ok: +3"),
    ("multi-scrutinee match", boolData ++ "yield match yea, nay { yea, yea ^ +1, yea, nay ^ +2, nay, yea ^ +3, nay, nay ^ +4 }", "eval ok: +2"),
    ("nested constructor match", boolData ++ optionData ++ "yield match nay some { yea some ^ +1, nay some ^ +2, none ^ +0 }", "eval ok: +2"),
    ("ℤ match patterns", "yield match -1 { +0 ^ +10, -1 ^ +20, _ ^ +30 }", "eval ok: +20"),
    ("ℤ patterns fall through", "yield match +2 { +0 ^ +10, +1 ^ +20, _ ^ +30 }", "eval ok: +30"),
    ("alternative constructor patterns share bindings", "ilk choice: [a:*, *] { left: [a, a choice], right: [a, a choice] } yield match +2 right { x left; x right ^ x }", "eval ok: +2"),
    ("string match patterns", "yield match 'yes' { 'yes' ^ +1, _ ^ +0 }", "eval ok: +1"),
    ("unchosen arm is not evaluated", boolData ++ "yield match yea { yea ^ +1, nay ^ +0 (sorry:[ℤ, ℤ]) }", "eval ok: +1"),
    ("fremmed arity followeth a transparent alias", "let twostead:* ≔ [ℤ, ℤ, ℤ] let plus:twostead ≔ 'eke_wholetale' fremmed yield +1 plus +2", "eval ok: +3"),
    ("an unused top-level definition is not computed", "let missing:ℤ ≔ sorry yield +1", "eval ok: +1"),
    ("a demanded top-level definition is computed", "let missing:ℤ ≔ sorry yield missing", "eval error: reached sorry"),
    ("an unused argument is not computed", "let ignore:[_:ℤ, ℤ] ≔ +7 yield (+1 (sorry:[ℤ, ℤ])) ignore", "eval ok: +7"),
    ("an unused local definition is not computed", "yield (let unused:ℤ ≔ +1 (sorry:[ℤ, ℤ]) yield +7)", "eval ok: +7"),
    ("a field projection computeth only the selected field", "ilk keep: * { keep_of: [kept: ℤ, unused: ℤ, keep] } yield (+7 keep_of (+1 (sorry:[ℤ, ℤ]))).kept", "eval ok: +7"),
    ("selfcalling under a match computeth only the chosen branch", rowData ++ "let flips: [r: row, inside: 𝟚, ℕ] ≔ match r { stop ^ 0, _ more leftover ^ match inside { yea ^ (leftover flips nay) heir, nay ^ leftover flips yea } } yield (64 ones) flips yea", "eval ok: 32"),
    ("a user function computeth only its selected recursive input", recursiveChoiceSource, "eval ok: +8"),
    ("an unused constructor field and recursive hypothesis are not computed", rowData ++ "let first: [r: row, 𝟚] ≔ match r { stop ^ nay, c more _ ^ c } yield (yea more (0 (sorry:[ℕ, row]))) first", "eval ok: yea"),
    ("reaching an orsetting is a runtime error", boolData ++ "orsetting missing: 𝟚 yield missing", "eval error: reached orsetting 'missing'"),
    ("a yielded worth is computed in full", "ilk keep: * { keep_of: [kept: ℤ, missing: ℤ, keep] } yield +1 keep_of (sorry: ℤ)", "eval error: reached sorry"),
    ("a yielded deed is performed", "bring ilk/one.tung " ++ sleepBinding ++ "yield 0 sleep", "eval ok: only"),
    ("deed_bind passeth a result on", deedPrelude ++ "let plus:[ℤ, ℤ, ℤ] ≔ 'eke_wholetale' fremmed yield (+2 sheer) bind { x ^ (x plus +1) sheer }", "eval ok: +3"),
    ("a deed is a worth until performed", deedPrelude ++ "let action:ℤ deed ≔ +1 sheer yield (let unused ≔ action yield +2)", "eval ok: +2"),
    ("flock laws are erased", "bring is.tung flock hath_sameness:[a:*, *] { let sameness:[a, a] let rule:[x: a, (x sameness) = x] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x let rule ≔ sorry } yield +2 sameness", "eval ok: +2"),
    ("result-only member useth expected type", "flock hath_origin:[a:*, *] { let origin:a } bizen:ℤ hath_origin { let origin ≔ +7 } let worth:ℤ ≔ origin yield worth", "eval ok: +7"),
    ("different instances dispatch by inferred type", "flock hath_label:[a:*, *] { let label:[a, string] } bizen:ℤ hath_label { let label: [_:] ≔ 'ℤ' } bizen:string hath_label { let label: [_:] ≔ 'string' } yield 'x' label", "eval ok: 'string'"),
    ("constraint function receiveth its caller dictionary", "flock hath_label:[a:*, *] { let label:[a, string] } bizen:ℤ hath_label { let label: [_:] ≔ 'ℤ' } bizen:string hath_label { let label: [_:] ≔ 'string' } let labelled:[@a:*, @:a hath_label, x: a, string] ≔ x label yield +1 labelled", "eval ok: 'ℤ'"),
    ("child dictionary useth a direct parent instance", "flock hath_parent:[a:*, *] { let parent:[a, a] } flock hath_child:[a:*, @:a hath_parent, *] { let child:[a, a] } bizen:ℤ hath_parent { let parent: [x:] ≔ x } bizen:ℤ hath_child { let child: [x:] ≔ x parent } yield +4 child", "eval ok: +4"),
    ("repeated bizen calls retain a preceding private worth", "bring often.tung flock hath_bump:[a:*, *] { let bump:[a, a] } let offset ≔ +2 bizen:ℤ hath_bump { let bump: [x:] ≔ x + offset } yield (+1 bump) + (+2 bump)", "eval ok: +7"),
    ("bizen may precede its resolved flock declaration", "bizen:ℤ hath_sameness { let sameness: [x:] ≔ x } flock hath_sameness:[a:*, *] { let sameness:[a, a] } yield +3 sameness", "eval ok: +3"),
    ("bizen constraint remaineth an external dictionary", "bring often.tung flock hath_combine:[a:*, *] { let combine:[a, a, a] } bizen:ℤ hath_combine { let combine: [x:, y:] ≔ x + y } ilk _box: [a:*, *] { box: [a, a _box] } bizen:[@a:*, @:a hath_combine, (a _box) hath_combine] { let combine: [x box:, y box:] ≔ (x combine y) box } yield (+1 box) combine (+2 box)", "eval ok: (+3 box)")
  ]

indexedUnpackSource :: String
indexedUnpackSource =
  "ilk tag: [a:*, *] { integer: [ℤ, ℤ tag], textual: [string, string tag] } "
    ++ "let unpack:[@a:*, x:a tag, a] ≔ match x { n integer ^ n, t textual ^ t } "

-- both inputs recurse; the discarded path faileth at its base.
recursiveChoiceSource :: String
recursiveChoiceSource =
  rowData
    ++ """
       let hath_+:[ℤ, ℤ, ℤ] ≔ 'eke_wholetale' fremmed
       let choose:[flag:𝟚, yes:ℤ, no:ℤ, ℤ] ≔ match flag { yea ^ yes, nay ^ no }
       let rime:[r:row, flag:𝟚, ℤ] ≔ match r {
         stop ^ match flag { yea ^ +0, nay ^ +0 (sorry:[ℤ, ℤ]) },
         _ more leftover ^ flag choose (+1 hath_+ (leftover rime yea)) (leftover rime nay)
       }
       yield (8 ones) rime yea

       """

typeErrors :: [(String, String)]
typeErrors =
  [ ("captured alias mismatch is rejected before evaluation", "let bad: [x:] ≔ (let y ≔ x let tale:ℤ ≔ y yield tale + +1) yield 'oops' bad"),
    ("non-function application", "yield +1 +2"),
    ("constructor overapplication", "ilk _box: [a:*, *] { box: [a, a _box] } yield +1 box +2")
  ]

importedCases :: Map.Map String String -> [Test]
importedCases imports =
  [ evalOkWith
      "a local term and an imported constructor retain distinct runtime identities"
      "bring token.tung ilk pair: * { pair_of: [constructor: token, local: ℤ, pair] } let box ≔ +7 yield token~box pair_of box"
      (Map.singleton "token.tung" "show ilk token: * { box: token }")
      "eval ok: (box +7 pair_of)",
    evalOkWith "imported call" "bring often.tung bring file.tung yield +2 inc" (Map.insert "file.tung" "bring often.tung show let inc: [x:] ≔ x + +1" imports) "eval ok: +3",
    evalOkWith "a use declaration is initialised before a preceding let" "let answer ≔ dep~worth bring dep.tung yield answer" (Map.insert "dep.tung" "show let worth ≔ +7" imports) "eval ok: +7",
    evalOkWith "a local and its imported predecessor retain distinct identities" "bring often.tung bring source.tung let worth ≔ source~worth + +1 yield worth + source~worth" (Map.insert "source.tung" "show let worth ≔ +2" imports) "eval ok: +5",
    evalTypeErrWith "a local worth shadoweth an imported constructor in patterns" "bring ilk/two.tung let yea:𝟚 ≔ two~yea yield match yea { yea ^ +1, nay ^ +0 }" imports,
    evalOkWith "a qualified pattern still reacheth a shadowed constructor" "bring ilk/two.tung let yea ≔ +0 yield match two~yea { two~yea ^ +1, nay ^ +0 }" imports "eval ok: +1",
    evalOkWith "default use alias worketh for values, classes, and constructor patterns" "bring ilk/item.tung let worth:item~_item ≔ item~empty yield match (worth item~sameness) { item~item ^ +1 }" (Map.insert "ilk/item.tung" "show ilk _item: * { item: _item } show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:_item hath_sameness { let sameness: [x:] ≔ x } show let empty:_item ≔ item" imports) "eval ok: +1",
    evalOkWith "derived flock operations" "bring often.tung yield (+1 < +2) ∧ (+1 ≭ +2)" imports "eval ok: yea",
    evalOkWith "false implieth false" "bring often.tung yield nay ≤ nay" imports "eval ok: yea",
    evalOkWith "true doth not imply false" "bring often.tung yield yea ≤ nay" imports "eval ok: nay",
    evalOkWith "heir patterns recurse on a natural" "bring often.tung let double: [n: ℕ, ℕ] ≔ match n { 0 ^ 0, m heir ^ (m double) + 2 } yield 3 double" imports "eval ok: 6",
    evalOkWith "heir addeth one to a natural" "yield (2 heir) heir" imports "eval ok: 4",
    evalOkWith "euclidean division returneth quotient and remainder for a undernaught divisor" "bring often.tung bring ilk/product.tung yield +5 % -3" imports "eval ok: ((-1 +2 both) some)",
    evalOkWith "euclidean division returneth quotient and remainder for a undernaught dividend" "bring often.tung bring ilk/product.tung yield -5 % +3" imports "eval ok: ((-2 +1 both) some)",
    evalOkWith "euclidean quotient and remainder reconstruct the dividend" "bring often.tung bring ilk/maybe.tung bring ilk/product.tung let dividend ≔ -5 let divisor ≔ -3 yield match dividend % divisor { (quotient both leftover) some ^ (quotient · divisor) + leftover, none ^ +0 }" imports "eval ok: -5",
    evalOkWith "euclidean division faileth at naught" "bring often.tung yield +1 % +0" imports "eval ok: none",
    evalOkWith "three-way comparison distinguishes each result" "bring often.tung bring ilk/product.tung yield (+0 compare +1) both (+1 compare +1) $both (+2 compare +1)" imports "eval ok: ((fore mid both) aft both)",
    evalOkWith "clamp keepeth a worth inside its bounds" "bring often.tung yield +0 clamp +10 +12" imports "eval ok: +10",
    evalOkWith "qualified duplicate values" "bring often.tung bring left.tung bring right.tung yield left~foo + right~foo" (duplicateImports <> imports) "eval ok: +3",
    evalOkWith "shared diamond import" "bring often.tung bring left.tung bring right.tung yield left~left + right~right" (diamondImports <> imports) "eval ok: +5",
    evalOkWith "diamond import keepeth one bizen sameness" "bring left.tung bring right.tung yield +3 left~sameness" (instanceDiamondImports <> imports) "eval ok: +3",
    evalOkWith "qualified classes from different modules stay distinct" "bring often.tung bring left.tung bring right.tung yield +3 left~sameness" (distinctClassImports <> imports) "eval ok: +4",
    evalOkWith "inherited same-named members select the requested class" (collidingMemberPrelude ++ "bizen:ℤ first { let tag: [_:] ≔ +1 } bizen:ℤ second { let tag: [_:] ≔ +2 } bizen:ℤ both { let own: [_:] ≔ +3 } let outcome:[@a:*, @:a both, x: a, ℤ] ≔ x right~tag yield +1 outcome") (collidingMemberImports <> imports) "eval ok: +2",
    evalOkWith "a child member override doth not replace a sibling flock member" ("bring often.tung " ++ collidingMemberPrelude ++ "bizen:ℤ second { let tag: [_:] ≔ +2 } bizen:ℤ both { let tag: [_:] ≔ +10 let own: [_:] ≔ +3 } let outcome:[@a:*, @:a both, x: a, ℤ] ≔ (x left~tag) + (x right~tag) yield +1 outcome") (collidingMemberImports <> imports) "eval ok: +12",
    evalOkWith "instances in extension-sharing paths stay distinct" "bring often.tung bring a.tung one bring a.extra.tung two yield (+1 one~sameness) + (+1 two~sameness)" (samePrefixInstanceImports <> imports) "eval ok: +13",
    evalOkWith "instances beneath dotted directories stay distinct" "bring often.tung bring pkg.one/sameness.tung one bring pkg.two/sameness.tung two yield (+1 one~sameness) + (+1 two~sameness)" (dottedDirectoryInstanceImports <> imports) "eval ok: +13",
    evalOkWith "same-spelled imported data types dispatch through distinct instances" "bring often.tung bring common.tung bring left.tung bring right.tung yield (left~worth common~label) + (right~worth common~label)" (nominalTypeInstanceImports <> imports) "eval ok: +11",
    evalOkWith "an imported transparent alias useth its underlying instance" "bring base.tung bring alias.tung yield alias~worth base~label" (transparentAliasInstanceImports <> imports) "eval ok: +7",
    evalOkWith "an exported alias retaineth its private nominal instance" "bring opaque.tung opaque yield opaque~worth opaque~label" (privateAliasInstanceImports <> imports) "eval ok: +7",
    evalOkWith "a local flock and bizen shadow an imported namesake" "bring often.tung bring left.tung flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +2 } yield (+1 sameness) + (+1 left~sameness)" (distinctClassImports <> imports) "eval ok: +5",
    evalTypeErrWith "local evidence cannot satisfy an imported namesake class" "bring left.tung flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x } let imported_use:[@a:*, @:a left~hath_sameness, x: a, a] ≔ x left~sameness let local_use:[@a:*, @:a hath_sameness, x: a, a] ≔ x imported_use yield +1 local_use" (distinctClassImports <> imports),
    evalOkWith "worth survives a named re-export" "bring middle.tung yield worth" (reexportImports <> imports) "eval ok: +7",
    evalOkWith "qualified re-export outranketh a shadowing local" "bring often.tung bring middle.tung let worth ≔ +3 yield middle~worth + worth" (reexportImports <> imports) "eval ok: +10",
    evalOkWith "flock bizen survives an import" "bring sameness.tung yield +3 sameness" (identityImports <> imports) "eval ok: +3",
    evalOkWith "specific bizen outranketh a blanket instance" "bring often.tung flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:[@a:*, a hath_sameness] { let sameness: [x:] ≔ x } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +1 } yield +1 sameness" imports "eval ok: +2",
    evalOkWith "data constructor survives a named re-export" "bring data_middle.tung yield +4 box" (dataReexportImports <> imports) "eval ok: (+4 box)",
    evalOkWith "constructor sameness survives a different re-export path" "bring data_base.tung bring data_middle.tung yield match +4 data_middle~box { x data_base~box ^ x }" (dataReexportImports <> imports) "eval ok: +4",
    evalOkWith "constructor pattern surviveth a middle-module re-export" "bring middle.tung yield match middle~off { middle~off ^ +1 }" (constructorReexportImports <> imports) "eval ok: +1",
    evalOkWith "qualified constructor pattern useth import alias" "bring alias.tung yield match +4 alias~box { x alias~box ^ x }" (Map.insert "alias.tung" "show ilk _box: [a:*, *] { box: [a, a _box] }" imports) "eval ok: +4",
    evalTypeErrWith "private qualified worth is rejected before runtime" "bring private.tung yield private~hidden" (Map.fromList [("private.tung", "let hidden ≔ +1")]),
    evalOkWith "string converteth to a unicode list" "bring often.tung yield 'λ😀' string_to_list" imports "eval ok: (`λ (`😀 empty ‥) ‥)",
    evalOkWith "unicode converteth to its scalar ℕ" "bring often.tung yield `😀 unicode_to_kindful" imports "eval ok: 128512",
    evalOkWith "scalar ℕ converteth to unicode" "bring often.tung yield 128512 kindful_to_unicode" imports "eval ok: (`😀 some)",
    evalOkWith "surrogate ℕ cannot become unicode" "bring often.tung yield 55296 kindful_to_unicode" imports "eval ok: none",
    evalOkWith "out-of-range ℕ cannot become unicode" "bring often.tung yield 1114112 kindful_to_unicode" imports "eval ok: none",
    evalOkWith "string behead exposeth one code point" "bring often.tung bring ilk/list.tung bring ilk/maybe.tung bring ilk/product.tung bring flock/algebra/whole/hath_fold.tung yield match 'λ字' behead_string { (c both leftover) maybe~some ^ ((c ‥ empty) list_to_string) · leftover, maybe~none ^ '' }" imports "eval ok: 'λ字'",
    evalOkWith "empty string hath no head" "bring often.tung bring ilk/maybe.tung yield match '' behead_string { none ^ +1, _ some ^ +0 }" imports "eval ok: +1",
    evalOkWith "generic string fold" "bring often.tung bring ilk/list.tung bring flock/functor/downshaper.tung yield ('north' ‥ ('南' ‥ empty)) …·" imports "eval ok: 'north南'",
    evalOkWith "string classes dispatch" "bring often.tung bring flock/algebra/whole/hath_fold.tung yield (('a' · 'β') ≍ 'aβ') ∧ ('a' ≤ 'b')" imports "eval ok: yea",
    evalOkWith "unicode classes dispatch" "bring often.tung yield (`a ≍ `a) ∧ (`a ≤ `b)" imports "eval ok: yea",
    evalOkWith "imported bizen doth not shadow native ℤ order" "bring ilk/list.tung yield +0 till +3" imports "eval ok: (+0 (+1 (+2 empty ‥) ‥) ‥)",
    evalOkWith "list warp pipeline keepeth the list functor" "bring often.tung bring ilk/list.tung yield +0 till +3 $ warp { x ^ x + +1 } $ warp to_string" imports "eval ok: ('1' ('2' ('3' empty ‥) ‥) ‥)",
    evalOkWith "list atfold calleth its separate warp instance" "bring often.tung bring ilk/list.tung let values ≔ +1 ‥ (+2 ‥ empty) let functions ≔ { x ^ x + +10 } ‥ ({ x ^ x · +2 } ‥ empty) yield values atfold functions" imports "eval ok: (+11 (+12 (+2 (+4 empty ‥) ‥) ‥) ‥)",
    evalOkWith "list traversal sequences maybe values" "bring often.tung bring ilk/list.tung bring ilk/maybe.tung bring flock/functor/hath_throughwend.tung yield (+1 ‥ (+2 ‥ empty)) throughwend { x ^ x maybe~some }" imports "eval ok: ((+1 (+2 empty ‥) ‥) some)",
    evalOkWith "fold_warp combineth mapped list values" "bring often.tung bring ilk/list.tung bring flock/functor/downshaper.tung yield (+0 till +3) gather_warp to_string" imports "eval ok: '012'",
    evalOkWith "bounded conjunction folds values" "bring often.tung bring ilk/list.tung bring flock/functor/downshaper.tung yield yea ‥ (nay ‥ empty) $ …∧" imports "eval ok: nay",
    evalOkWith "empty bounded disjunction useth the lower endpoint" "bring often.tung bring ilk/list.tung bring flock/functor/downshaper.tung let values:𝟚 list ≔ empty yield values …∨" imports "eval ok: nay",
    evalOkWith "boolean complement negateth" "bring often.tung yield yea ¬" imports "eval ok: nay",
    evalTypeErrWith "bounded lattice need not have a complement" "bring often.tung yield mid ¬" imports,
    evalOkWith "ℤ lattice chooseth the lesser worth" "bring often.tung yield +3 ∧ +2" imports "eval ok: +2",
    evalOkWith "whole order supplieth a distributive lattice" "bring often.tung let distribute:[@a:*, @:a lattice_spreadsome, x: a, y: a, z: a, a] ≔ x ∧ (y ∨ z) yield +3 distribute +2 +4" imports "eval ok: +3",
    evalOkWith "non-total powerset lattice yoketh predicates" "bring often.tung bring ilk/list.tung bring ilk/powerset.tung bring flock/functor/downshaper.tung let one:ℤ powerset ≔ { x ^ x ≍ +1 } let two:ℤ powerset ≔ { x ^ x ≍ +2 } let yoked ≔ one ‥ (two ‥ list~empty) $ …∨ yield yoked ∋ +2" imports "eval ok: yea",
    evalOkWith "empty powerset meet yieldeth the universal set" "bring often.tung bring ilk/list.tung bring ilk/powerset.tung bring flock/functor/downshaper.tung let values:(ℤ powerset) list ≔ list~empty let all ≔ values …∧ yield all ∋ +42" imports "eval ok: yea",
    evalOkWith "pattern binders do not become constructor patterns" "bring often.tung bring ilk/list.tung ilk bit: * { off: bit } yield +0 till +3 $ warp { _ ^ off } $ warp { _ ^ +1 }" imports "eval ok: (+1 (+1 (+1 empty ‥) ‥) ‥)",
    evalOkWith "control branch suspends actions" "bring often.tung yield nay branch { _ ^ +1 } { _ ^ +2 }" imports "eval ok: +2",
    evalOkWith "maybe maybe mapeth present worth" "bring often.tung bring ilk/maybe.tung yield (+3 some) handle +0 { x ^ x + +1 }" imports "eval ok: +4",
    evalOkWith "sum either consumeth selected side" "bring often.tung bring ilk/sum.tung yield (+2 incast₁) either { x ^ x + +1 } { y ^ y · +3 }" imports "eval ok: +6",
    evalOkWith "sum biwarp mapeth the selected side" "bring often.tung bring ilk/sum.tung let worth:ℤ ∑ string ≔ +2 incast₀ yield match (worth biwarp { x ^ x + +1 } { string ^ string }) { x incast₀ ^ x, _ incast₁ ^ +0 }" imports "eval ok: +3",
    evalOkWith "sum functor mapeth the right side" "bring often.tung bring ilk/sum.tung let worth:string ∑ ℤ ≔ +2 incast₁ yield match (worth warp { x ^ x + +1 }) { _ incast₀ ^ +0, x incast₁ ^ x }" imports "eval ok: +3",
    evalOkWith "sum atfoldsome applieth the right side" "bring often.tung bring ilk/sum.tung let worth:string ∑ ℤ ≔ +2 incast₁ let f:string ∑ [ℤ, ℤ] ≔ { x ^ x + +3 } incast₁ yield match worth atfold f { _ incast₀ ^ +0, x incast₁ ^ x }" imports "eval ok: +5",
    evalOkWith "sum monad preserveth a left worth" "bring often.tung bring ilk/sum.tung let worth:string ∑ ℤ ≔ 'left' incast₀ yield match (worth bind { x ^ (x + +1) incast₁ }) { message incast₀ ^ message, x incast₁ ^ x to_string }" imports "eval ok: 'left'",
    evalOkWith "sum downshaper foldeth the right side" "bring often.tung bring ilk/sum.tung bring flock/functor/downshaper.tung let worth:string ∑ ℤ ≔ +3 incast₁ yield worth gather₁ +1 +" imports "eval ok: +4",
    evalOkWith "sum traversal preserveth its side" "bring often.tung bring ilk/sum.tung bring ilk/maybe.tung bring flock/functor/hath_throughwend.tung let worth:string ∑ ℤ ≔ +3 incast₁ yield worth throughwend { x ^ (x + +1) some }" imports "eval ok: ((+4 incast₁) some)",
    evalOkWith "product biwarp mapeth both fields" "bring often.tung bring ilk/product.tung yield (+1 both +2) biwarp { x ^ x + +1 } { y ^ y · +3 }" imports "eval ok: (+2 +6 both)",
    evalOkWith "product atfoldsome accumulateth worth context first" "bring often.tung bring ilk/product.tung let worth ≔ 'worth:' both +2 let f ≔ 'function:' both { x ^ x + +1 } yield worth atfold f" imports "eval ok: ('worth:function:' +3 both)",
    evalOkWith "product monad accumulateth outer context first" "bring often.tung bring ilk/product.tung yield ('outer:' both +2) bind { x ^ 'inner:' both (x + +1) }" imports "eval ok: ('outer:inner:' +3 both)",
    evalOkWith "product downshaper foldeth the second field" "bring often.tung bring ilk/product.tung bring flock/functor/downshaper.tung yield ('ignored' both +3) gather₁ +1 +" imports "eval ok: +4",
    evalOkWith "product traversal preserveth the first field" "bring often.tung bring ilk/product.tung bring ilk/maybe.tung bring flock/functor/hath_throughwend.tung yield ('context' both +3) throughwend { x ^ (x + +1) some }" imports "eval ok: (('context' +4 both) some)",
    evalOkWith "atfoldsome lift2 for maybe" "bring often.tung bring ilk/maybe.tung yield (+1 some) lift₂ (+2 some) +" imports "eval ok: (+3 some)",
    evalOkWith "atfoldsome keep_other preserveth context order" "bring often.tung bring ilk/product.tung yield ('left:' both +1) keep_other ('right:' both +2)" imports "eval ok: ('right:left:' +2 both)",
    evalOkWith "functor void for maybe" "bring ilk/maybe.tung bring flock/functor.tung yield (+1 some) void" imports "eval ok: (only some)",
    evalOkWith "freer bind transformeth a completed worth" (freerPrelude ++ "yield ((+3 done) freer~bind { worth ^ (worth + +1) done }) run") imports "eval ok: +4",
    evalOkWith "freer lift and fold may repeat a continuation" (freerPrelude ++ "yield ask_freer run") imports "eval ok: +3",
    evalOkWith "freer bind may discard a continuation" (freerPrelude ++ "yield (ask_freer freer~bind { _ ^ +0 done }) run") imports "eval ok: +0",
    evalOkWith "freer mapping and flattening preserve suspended requests" (freerPrelude ++ "yield (ask_freer often~warp { worth ^ worth + +10 } $ freer~warp { worth ^ worth done } $ freer~flat) run") imports "eval ok: +23",
    evalOkWith "list behead exposeth the head and tail" "bring ilk/list.tung bring ilk/maybe.tung bring ilk/product.tung yield match (+1 ‥ empty) behead { (head product~both _) maybe~some ^ head, maybe~none ^ +0 }" imports "eval ok: +1",
    evalOkWith "till excludeth its stop" "bring ilk/list.tung yield >{‥, +2 till +2, +3 till +1, -1 till +1, empty}" imports "eval ok: (empty (empty ((-1 (+0 empty ‥) ‥) empty ‥) ‥) ‥)",
    evalOkWith "list take after drop" "bring ilk/list.tung yield ((+0 till +5) drop 2) take 2" imports "eval ok: (+2 (+3 empty ‥) ‥)",
    evalOkWith "list find returneth first match" "bring often.tung bring ilk/list.tung yield (+0 till +5) find { x ^ +3 ≤ x }" imports "eval ok: (+3 some)",
    evalOkWith "list indexing is naught based" "bring ilk/list.tung yield (+10 ‥ (+20 ‥ empty)) at 1" imports "eval ok: (+20 some)",
    evalOkWith "list index past the end faileth" "bring often.tung bring ilk/list.tung yield (+10 ‥ (+20 ‥ empty)) at 2" imports "eval ok: none",
    evalOkWith "natural subtraction stoppeth at naught" "bring often.tung yield (2 ∸ 3) + (5 ∸ 2)" imports "eval ok: 3",
    evalOkWith "list last returneth the final worth" "bring ilk/list.tung yield (+1 ‥ (+2 ‥ empty)) last" imports "eval ok: (+2 some)",
    evalOkWith "empty list hath no last worth" "bring ilk/list.tung let values:ℤ list ≔ empty yield values last" imports "eval ok: none",
    evalOkWith "list membership findeth a worth" "bring often.tung bring ilk/list.tung yield (+1 ‥ (+2 ‥ empty)) ∋ +2" imports "eval ok: yea",
    evalOkWith "list membership rejecteth a missing worth" "bring often.tung bring ilk/list.tung yield (+1 ‥ (+2 ‥ empty)) ∋ +3" imports "eval ok: nay",
    evalOkWith "list replicate useth a nonnegative count" "bring ilk/list.tung yield 'x' eftfold 3" imports "eval ok: ('x' ('x' ('x' empty ‥) ‥) ‥)",
    evalOkWith "list partition preserveth order" "bring often.tung bring ilk/list.tung yield (+0 till +5) partition { x ^ +2 ≤ x }" imports "eval ok: ((+2 (+3 (+4 empty ‥) ‥) ‥) (+0 (+1 empty ‥) ‥) both)",
    evalOkWith "list unzip preserveth both sides" "bring ilk/list.tung bring ilk/product.tung yield ((+1 both 'a') ‥ ((+2 both 'b') ‥ empty)) unzip" imports "eval ok: ((+1 (+2 empty ‥) ‥) ('a' ('b' empty ‥) ‥) both)",
    evalOkWith "n-ary sum addeth a foldable collection" "bring often.tung bring ilk/list.tung bring flock/functor/downshaper.tung yield (+1 ‥ (+2 ‥ (+3 ‥ empty))) …+" imports "eval ok: +6",
    evalOkWith "n-ary sum of an empty collection is naught" "bring often.tung bring ilk/list.tung bring flock/functor/downshaper.tung let values:ℤ list ≔ empty yield values …+" imports "eval ok: +0",
    evalTypeErrWith "n-ary sum needeth a downshaper" "bring often.tung bring flock/functor/downshaper.tung ilk _box: [a:*, *] { box: [a, a _box] } let worth:ℤ _box ≔ +1 box yield worth …+" imports,
    evalOkWith "n-ary product multiplies a foldable collection" "bring often.tung bring ilk/list.tung bring flock/functor/downshaper.tung yield (+2 ‥ (+3 ‥ (+4 ‥ empty))) …·" imports "eval ok: +24",
    evalOkWith "n-ary product of an empty collection is one" "bring often.tung bring ilk/list.tung bring flock/functor/downshaper.tung let values:ℤ list ≔ empty yield values …·" imports "eval ok: +1",
    evalTypeErrWith "n-ary product needeth a fold monoid" "bring often.tung bring ilk/list.tung bring flock/functor/downshaper.tung yield (`a ‥ empty) …·" imports,
    evalOkWith "boolean upper wrapper useth disjunction" "bring often.tung bring ilk/list.tung bring flock/algebra/whole/semigroup_fold.tung bring flock/functor/downshaper.tung let values ≔ (nay upper) ‥ ((yea upper) ‥ list~empty) yield match values …· { outcome upper ^ outcome }" imports "eval ok: yea",
    evalOkWith "empty boolean upper fold yieldeth nay" "bring often.tung bring ilk/list.tung bring flock/algebra/whole/semigroup_fold.tung bring flock/functor/downshaper.tung let values:(𝟚 _upper) list ≔ list~empty yield match values …· { outcome upper ^ outcome }" imports "eval ok: nay",
    evalOkWith "boolean lower wrapper useth conjunction" "bring often.tung bring ilk/list.tung bring flock/algebra/whole/semigroup_fold.tung bring flock/functor/downshaper.tung let values ≔ (yea lower) ‥ ((nay lower) ‥ list~empty) yield match values …· { outcome lower ^ outcome }" imports "eval ok: nay",
    evalOkWith "empty boolean lower fold yieldeth yea" "bring often.tung bring ilk/list.tung bring flock/algebra/whole/semigroup_fold.tung bring flock/functor/downshaper.tung let values:(𝟚 _lower) list ≔ list~empty yield match values …· { outcome lower ^ outcome }" imports "eval ok: yea",
    evalOkWith "natural semiring computeth with both identities" "bring often.tung bring ilk/kindful.tung let two:ℕ ≔ 2 let three ≔ two + 1 yield ((two · three) + one) to_ℤ" imports "eval ok: +7",
    evalOkWith "natural semiring supplieth fold monoid evidence" "bring often.tung bring ilk/list.tung bring ilk/kindful.tung bring flock/functor/downshaper.tung let two:ℕ ≔ 2 let three ≔ two + 1 yield ((two ‥ (three ‥ list~empty)) …·) to_ℤ" imports "eval ok: +6",
    evalOkWith "nonnegative ℤ converteth to natural" "bring often.tung bring ilk/kindful.tung yield +3 to_ℕ" imports "eval ok: (3 some)",
    evalOkWith "unsigned digits are a natural" "bring often.tung yield (2 + 3) · 4" imports "eval ok: 20",
    evalOkWith "undernaught ℤ cannot become natural" "bring often.tung yield -1 to_ℕ" imports "eval ok: none",
    evalOkWith "complex exponentiation scaleth by the real exponent" "bring often.tung bring ilk/midbraid.tung yield ((1.0 +i 0.0) exponent) real" imports "eval ok: 2.718281828459045",
    evalOkWith "complex sine of unit imaginary yieldeth hyperbolic sine" "bring often.tung bring ilk/midbraid.tung yield ((0.0 +i 1.0) sine) imaginary" imports "eval ok: 1.1752011936438014",
    evalOkWith "complex cosine of unit imaginary yieldeth hyperbolic cosine" "bring often.tung bring ilk/midbraid.tung yield ((0.0 +i 1.0) cosine) real" imports "eval ok: 1.5430806348152437",
    evalOkWith "unempty warp preserveth the first element" "bring often.tung bring ilk/list.tung bring ilk/unempty.tung yield ((+1 ‥′ (+2 ‥ empty)) warp { x ^ x + +1 }) to_list" imports "eval ok: (+2 (+3 empty ‥) ‥)",
    evalOkWith "unempty semigroup athangeth without losing the head" "bring often.tung bring ilk/list.tung bring ilk/unempty.tung bring flock/algebra/whole/hath_fold.tung yield ((+1 ‥′ (+2 ‥ empty)) · (+3 ‥′ empty)) to_list" imports "eval ok: (+1 (+2 (+3 empty ‥) ‥) ‥)",
    evalOkWith "unempty atfoldsome applieth every function" "bring often.tung bring ilk/list.tung bring ilk/unempty.tung let values ≔ +1 ‥′ (+2 ‥ empty) let fs ≔ { x ^ x + +1 } ‥′ ({ x ^ x · +2 } ‥ empty) yield (values atfold fs) to_list" imports "eval ok: (+2 (+3 (+2 (+4 empty ‥) ‥) ‥) ‥)",
    evalOkWith "unempty monad concatenateth every result" "bring often.tung bring ilk/list.tung bring ilk/unempty.tung let values ≔ +1 ‥′ (+2 ‥ empty) yield (values bind { x ^ x ‥′ ((x + +10) ‥ empty) }) to_list" imports "eval ok: (+1 (+11 (+2 (+12 empty ‥) ‥) ‥) ‥)",
    evalOkWith "unempty downshaper visiteth the head first" "bring often.tung bring ilk/list.tung bring ilk/unempty.tung bring flock/functor/downshaper.tung yield (+1 ‥′ (+2 ‥ empty)) gather₁ +0 +" imports "eval ok: +3",
    evalOkWith "unempty traversal keepeth a unempty result" "bring often.tung bring ilk/list.tung bring ilk/unempty.tung bring ilk/maybe.tung bring flock/functor/hath_throughwend.tung yield ((+1 ‥′ (+2 ‥ empty)) throughwend { x ^ (x + +1) some }) warp to_list" imports "eval ok: ((+2 (+3 empty ‥) ‥) some)",
    evalOkWith "unempty membership delegateth to list" "bring often.tung bring ilk/list.tung bring ilk/unempty.tung yield (+1 ‥′ (+2 ‥ empty)) ∋ +2" imports "eval ok: yea",
    evalOkWith "wordbook put replaceth a key" "bring often.tung bring ilk/wordbook.tung let wordbook ≔ (empty put 'a' +1) put 'a' +2 yield wordbook lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "wordbook membership dispatcheth through inhold" "bring often.tung bring ilk/wordbook.tung let wordbook ≔ empty put 'a' +1 yield wordbook ∋ 'a'" imports "eval ok: yea",
    evalOkWith "wordbook constructor may be qualified" "bring often.tung bring ilk/list.tung bring ilk/product.tung bring ilk/wordbook.tung yield (('a' both +2) ‥ list~empty) wordbook~from_list $ lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "tree keepeth its keys in order" "bring often.tung bring ilk/tree.tung let t ≔ ((empty put 'c' +3) put 'a' +1) put 'b' +2 yield t keys" imports "eval ok: ('a' ('b' ('c' empty ‥) ‥) ‥)",
    evalOkWith "tree put replaceth a key" "bring often.tung bring ilk/tree.tung let t ≔ (empty put 'a' +1) put 'a' +2 yield t lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "tree rid droppeth a key and keepeth the rest" "bring often.tung bring ilk/tree.tung let t ≔ ((empty put 2 'b') put 1 'a') put 3 'c' yield (t rid 2) keys" imports "eval ok: (1 (3 empty ‥) ‥)",
    evalOkWith "tree stayeth shallow under sorted puts" "bring often.tung bring flock/functor/downshaper.tung bring flock/hath_greatness.tung bring ilk/list.tung bring ilk/product.tung bring ilk/tree.tung let depth: [@α: *, @β: *, α tree β, ℕ] ≔ { leaf ^ 0, _ node _ _ l r ^ ((l depth) ∨ (r depth)) + 1 } let t: ℕ tree ℕ ≔ (0 eftfold 64) gather₁ (tree~empty both 0) {pair, _ ^ match pair { t both n ^ (t put n n) both (n + 1) }} $ forthcast₀ yield (t depth) both (t greatness)" imports "eval ok: (7 64 both)",
    evalOkWith "wordbook rid droppeth a key" "bring often.tung bring ilk/wordbook.tung let wordbook ≔ empty put 'a' +1 yield (wordbook rid 'a') lookup 'a'" imports "eval ok: none",
    evalOkWith "set put keepeth values unique" "bring often.tung bring ilk/set.tung yield ((empty put +1) put +1) to_list" imports "eval ok: (+1 empty ‥)",
    evalOkWith "set from_list sorteth and removeth duplicates" "bring often.tung bring ilk/list.tung bring ilk/set.tung yield (+2 ‥ (+1 ‥ (+2 ‥ list~empty))) set~from_list $ to_list" imports "eval ok: (+1 (+2 empty ‥) ‥)",
    evalOkWith "set rid droppeth a worth" "bring often.tung bring ilk/set.tung let values ≔ (empty put +1) put +2 yield (values rid +1) ∋ +1" imports "eval ok: nay",
    evalOkWith "set supremum keepeth unique values in order" "bring often.tung bring ilk/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +3 yield (left ∨ right) to_list" imports "eval ok: (+1 (+2 (+3 empty ‥) ‥) ‥)",
    evalOkWith "set infimum keepeth shared values" "bring often.tung bring ilk/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +3 yield (left ∧ right) to_list" imports "eval ok: (+2 empty ‥)",
    evalOkWith "set is ignoreth putting order" "bring often.tung bring ilk/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +1 yield left ≍ right" imports "eval ok: yea",
    evalOkWith "set half order compareth enclosure" "bring often.tung bring ilk/set.tung let smaller ≔ empty put +1 let larger ≔ smaller put +2 yield (smaller ≤ larger) ∧ (smaller < larger)" imports "eval ok: yea",
    evalOkWith "set enclosure rejecteth a proper superset" "bring often.tung bring ilk/set.tung let smaller ≔ empty put +1 let larger ≔ smaller put +2 yield larger ≤ smaller" imports "eval ok: nay",
    evalOkWith "powerset addition is evenmete difference" "bring often.tung bring ilk/powerset.tung let left:ℤ powerset ≔ { worth ^ (worth ≍ +1) ∨ (worth ≍ +2) } let right:ℤ powerset ≔ { worth ^ (worth ≍ +2) ∨ (worth ≍ +3) } yield ((left + right) ∋ +2)" imports "eval ok: nay",
    evalOkWith "powerset addition keepeth an unshared member" "bring often.tung bring ilk/powerset.tung let left:ℤ powerset ≔ { worth ^ worth ≍ +1 } let right:ℤ powerset ≔ { worth ^ worth ≍ +2 } yield ((left + right) ∋ +1)" imports "eval ok: yea",
    evalOkWith "powerset multiplication is intersection" "bring often.tung bring ilk/powerset.tung let left:ℤ powerset ≔ { worth ^ (worth ≍ +1) ∨ (worth ≍ +2) } let right:ℤ powerset ≔ { worth ^ worth ≍ +2 } yield ((left · right) ∋ +2)" imports "eval ok: yea",
    evalOkWith "powerset supremum is yoke" "bring often.tung bring ilk/powerset.tung let left:ℤ powerset ≔ { worth ^ worth ≍ +1 } let right:ℤ powerset ≔ { worth ^ worth ≍ +2 } yield (left ∨ right) ∋ +2" imports "eval ok: yea",
    evalOkWith "powerset infimum is intersection" "bring often.tung bring ilk/powerset.tung let left:ℤ powerset ≔ { worth ^ (worth ≍ +1) ∨ (worth ≍ +2) } let right:ℤ powerset ≔ { worth ^ worth ≍ +2 } yield (left ∧ right) ∋ +1" imports "eval ok: nay",
    evalOkWith "powerset complement excludeth a former member" "bring often.tung bring ilk/powerset.tung let one:ℤ powerset ≔ { worth ^ worth ≍ +1 } let outside:ℤ powerset ≔ one ¬ yield outside ∋ +1" imports "eval ok: nay",
    evalOkWith "powerset complement encloseth a former nonmember" "bring often.tung bring ilk/powerset.tung let one:ℤ powerset ≔ { worth ^ worth ≍ +1 } let outside:ℤ powerset ≔ one ¬ yield outside ∋ +2" imports "eval ok: yea",
    evalOkWith "powerset updates compose pointwise" "bring often.tung bring ilk/powerset.tung let left:ℤ powerset ≔ (powerset~empty put +1) put +2 let right:ℤ powerset ≔ powerset~empty put +2 yield >{∧, left ∋ +1, ((left rid +1) ∋ +1) ¬, (left ∖ right) ∋ +1, ((left ∖ right) ∋ +2) ¬}" imports "eval ok: yea",
    evalOkWith "powerset negation leaveth a set whose sum with it is empty" "bring often.tung bring ilk/powerset.tung let values:ℤ powerset ≔ { worth ^ worth ≍ +1 } yield ((values + (values -)) ∋ +1)" imports "eval ok: nay",
    evalOkWith "powerset naught is empty" "bring often.tung bring ilk/powerset.tung let values:ℤ powerset ≔ naught yield values ∋ +7" imports "eval ok: nay",
    evalOkWith "powerset one is universal" "bring often.tung bring ilk/powerset.tung let values:ℤ powerset ≔ one yield values ∋ +7" imports "eval ok: yea",
    evalOkWith "set becometh a powerset" "bring often.tung bring ilk/set.tung bring ilk/powerset.tung let finite ≔ set~empty set~put +7 yield (finite to_powerset) ∋ +7" imports "eval ok: yea",
    evalOkWith "powerset lower wrapper useth intersection" "bring often.tung bring ilk/list.tung bring ilk/powerset.tung bring flock/algebra/whole/semigroup_fold.tung bring flock/functor/downshaper.tung let one:ℤ powerset ≔ { worth ^ worth ≍ +1 } let both:ℤ powerset ≔ { worth ^ (worth ≍ +1) ∨ (worth ≍ +2) } let wrapped ≔ (one lower) ‥ ((both lower) ‥ list~empty) yield match wrapped …· { outcome lower ^ outcome ∋ +2 }" imports "eval ok: nay",
    evalOkWith "powerset upper wrapper useth yoke" "bring often.tung bring ilk/list.tung bring ilk/powerset.tung bring flock/algebra/whole/semigroup_fold.tung bring flock/functor/downshaper.tung let one:ℤ powerset ≔ { worth ^ worth ≍ +1 } let two:ℤ powerset ≔ { worth ^ worth ≍ +2 } let wrapped ≔ (one upper) ‥ ((two upper) ‥ list~empty) yield match wrapped …· { outcome upper ^ outcome ∋ +2 }" imports "eval ok: yea",
    evalOkWith "empty powerset wrapper monoids select their bounds" "bring often.tung bring ilk/list.tung bring ilk/powerset.tung bring flock/algebra/whole/semigroup_fold.tung bring flock/functor/downshaper.tung let meets:((ℤ powerset) _lower) list ≔ list~empty let yokes:((ℤ powerset) _upper) list ≔ list~empty yield >{∧, match meets …· { outcome lower ^ outcome ∋ +42 }, match yokes …· { outcome upper ^ (outcome ∋ +42) ¬ }}" imports "eval ok: yea",
    evalOkWith "wordbook functor mapeth values" "bring often.tung bring ilk/wordbook.tung let wordbook ≔ (empty put 'a' +1) put 'b' +2 yield (wordbook warp { x ^ x + +10 }) lookup 'a'" imports "eval ok: (+11 some)",
    evalOkWith "wordbook sift keepeth matching values" "bring often.tung bring ilk/wordbook.tung bring flock/functor/hath_sift.tung let wordbook ≔ (empty put 'a' +1) put 'b' +2 yield (wordbook sift { x ^ +2 ≤ x }) lookup 'a'" imports "eval ok: none",
    evalOkWith "wordbook merge preferreth right values" "bring often.tung bring ilk/wordbook.tung let left ≔ empty put 'a' +1 let right ≔ empty put 'a' +2 yield (left merge right) lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "wordbook adjust changeth an existing worth" "bring often.tung bring ilk/wordbook.tung let wordbook ≔ empty put 'a' +1 yield (wordbook adjust 'a' { x ^ x + +1 }) lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "string operations use unicode code points" "bring often.tung bring ilk/string/operation.tung yield ('aβ字' eftwend_string) take_string 2" imports "eval ok: '字β'",
    evalOkWith "string greatness counteth unicode code points" "bring often.tung bring ilk/string/operation.tung bring flock/hath_greatness.tung bring ilk/kindful.tung yield ('aβ字' greatness) to_ℤ" imports "eval ok: +3",
    evalOkWith "string split and yoke preserve empty fields" "bring often.tung bring ilk/string/operation.tung yield ('a,b,,c' split_string `,) yoke_with_string '.'" imports "eval ok: 'a.b..c'",
    evalOkWith "string words collapse whitespace runs" "bring often.tung bring ilk/string/operation.tung yield ' red\\tblue\\nred ' words_string $ yoke_with_string '.'" imports "eval ok: 'red.blue.red'",
    evalOkWith "typed paths yoke components" "bring often.tung bring ilk/path.tung yield (('root' path) path~yoke ('leaf' path)) to_string" imports "eval ok: 'root/leaf'",
    evalOkWith "time spans drive async sleep" "bring often.tung bring ilk/milliseconds.tung yield (0 milliseconds) sleep_for" imports "eval ok: only",
    evalOkWith "process captureth standard output" "bring often.tung bring deed/process.tung bring process/outcome.tung bring ilk/list.tung bring ilk/sum.tung yield 'printf' process~run ('hello' ‥ empty) $ warp { outcome ^ outcome warp process_output }" imports "eval ok: ('hello' incast₁)",
    evalOkWith "arctan range is nonnegative" "bring _fremmed.tung yield 0.0 arctan_float -1.0" imports "eval ok: 4.71238898038469",
    evalOkWith "fork and wait" "bring often.tung let work:ℤ deed ≔ +42 sheer yield work fork $ bind wait" imports "eval ok: (+42 some)",
    evalOkWith "task result may be awaited repeatedly" "bring often.tung let work:ℤ deed ≔ +21 sheer yield work fork $ bind { task ^ (task wait) lift₂ (task wait) { a, b ^ a lift₂ b + } }" imports "eval ok: (+42 some)",
    evalOkWith "task wait may time out" "bring often.tung let work:ℤ deed ≔ (200 sleep) then (+42 sheer) yield work fork $ bind { task ^ task wait_for 0 }" imports "eval ok: none",
    evalOkWith "task wait_for returneth a finished worth" "bring often.tung let work:ℤ deed ≔ +42 sheer yield work fork $ bind { task ^ task wait_for 1000 }" imports "eval ok: (+42 some)",
    evalOkWith "a cancelled task yieldeth none" "bring often.tung let work:ℤ deed ≔ (1000 sleep) then (+42 sheer) yield work fork $ bind { task ^ (task outstrike) then (task wait) }" imports "eval ok: none",
    evalOkWith "cpu-bound task remaineth cancellable" "bring often.tung let spin:ℤ deed ≔ { again ^ (only sheer) bind { _ ^ again } } deed_steadfast yield spin fork $ bind { task ^ (task outstrike) then (task wait) }" imports "eval ok: none",
    evalTypeErrWith "an opaque task cannot be eliminated as an empty family" "bring often.tung let unwrap:[worth:ℤ task, ℤ] ≔ match worth {} yield +0" imports,
    concurrentForks imports,
    randomRange imports,
    systemArguments imports,
    systemEnvironment imports,
    unixTime imports
  ]
  where
    duplicateImports = Map.fromList [("left.tung", "show let foo ≔ +1"), ("right.tung", "show let foo ≔ +2")]
    diamondImports =
      Map.fromList
        [ ("left.tung", "bring often.tung bring shared.tung show let left ≔ shared~base + +1"),
          ("right.tung", "bring often.tung bring shared.tung show let right ≔ shared~base + +2"),
          ("shared.tung", "show let base ≔ +1")
        ]
    instanceDiamondImports =
      Map.fromList
        [ ("left.tung", "bring shared.tung show shared~sameness"),
          ("right.tung", "bring shared.tung"),
          ("shared.tung", "show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x }")
        ]
    distinctClassImports =
      Map.fromList
        [ ("left.tung", "bring often.tung show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +1 }"),
          ("right.tung", "bring often.tung show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +2 }")
        ]
    collidingMemberPrelude = "bring left.tung bring right.tung flock both:[a:*, @:a first, @:a second, *] { let own:[a, ℤ] } "
    collidingMemberImports =
      Map.fromList
        [ ("left.tung", "show flock first:[a:*, *] { let tag:[a, ℤ] }"),
          ("right.tung", "show flock second:[a:*, *] { let tag:[a, ℤ] }")
        ]
    samePrefixInstanceImports = Map.fromList [("a.tung", identityInstance 1), ("a.extra.tung", identityInstance 10)]
    dottedDirectoryInstanceImports = Map.fromList [("pkg.one/sameness.tung", identityInstance 1), ("pkg.two/sameness.tung", identityInstance 10)]
    identityInstance :: Int -> String
    identityInstance increment = "bring often.tung show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + " ++ integerSource increment ++ " }"
    nominalTypeInstanceImports =
      Map.fromList
        [ ("common.tung", "show flock hath_label:[a:*, *] { let label:[a, ℤ] }"),
          ("left.tung", "bring common.tung show ilk _token: * { token: _token } bizen:_token common~hath_label { let label: [_:] ≔ +1 } show let worth:_token ≔ token"),
          ("right.tung", "bring common.tung show ilk _token: * { token: _token } bizen:_token common~hath_label { let label: [_:] ≔ +10 } show let worth:_token ≔ token")
        ]
    transparentAliasInstanceImports =
      Map.fromList
        [ ("base.tung", "show ilk _token: * { token: _token } show flock hath_label:[a:*, *] { let label:[a, ℤ] } bizen:_token hath_label { let label: [_:] ≔ +7 }"),
          ("alias.tung", "bring base.tung show let alias:* ≔ base~_token show let worth:alias ≔ base~token")
        ]
    privateAliasInstanceImports =
      Map.singleton
        "opaque.tung"
        "ilk _secret: * { secret: _secret } show let public:* ≔ _secret show flock hath_label:[a:*, *] { let label:[a, ℤ] } bizen:_secret hath_label { let label: [_:] ≔ +7 } show let worth:public ≔ secret"
    reexportImports = Map.fromList [("base.tung", "show let worth ≔ +7"), ("middle.tung", "bring base.tung show base~worth")]
    identityImports = Map.fromList [("sameness.tung", "show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x }")]
    dataReexportImports =
      Map.fromList
        [ ("data_base.tung", "show ilk _box: [a:*, *] { box: [a, a _box] }"),
          ("data_middle.tung", "bring data_base.tung show data_base~box")
        ]
    constructorReexportImports =
      Map.fromList
        [ ("base.tung", "show ilk bit: * { off: bit }"),
          ("middle.tung", "bring base.tung show base~bit show base~off")
        ]
    -- a request names its answer type; the handler answereth each `ask` twice.
    freerPrelude =
      "bring often.tung bring ilk/freer.tung "
        ++ "ilk question: [a:*, *] { ask: ℤ question } "
        ++ "let ask_freer: question freer ℤ ≔ ask lift "
        ++ "let answer: [@ξ:*, request: ξ question, throughwone: [ξ, ℤ], ℤ] ≔ match request { ask ^ (+1 throughwone) + (+2 throughwone) } "
        ++ "let run: [forewrit: question freer ℤ, ℤ] ≔ { worth ^ worth } gather answer forewrit "

randomRange :: Map.Map String String -> Test
randomRange imports = do
  actual <- Harness.evaluateSource "bring often.tung yield random" imports
  pure $ case stripPrefix "eval ok: " actual >>= readMaybe of
    Just value | value >= (0 :: Double) && value < 1 -> Nothing
    _ -> Just ("random result is in [0, 1): got " ++ actual)

concurrentForks :: Map.Map String String -> Test
concurrentForks imports =
  evalOkWith "concurrent forks overlap while one is awaited" source imports "eval ok: (+21 some)"
  where
    -- awaiting one equal-duration task giveth the other time to finish. its
    -- already-available result testeth overlap without timing the whole compiler.
    source =
      "bring often.tung "
        ++ "let work:ℤ deed ≔ (600 sleep) then (+21 sheer) "
        ++ "yield work fork $ bind { left ^ work fork $ bind { right ^ (left wait) then (right wait_for 100) } }"

systemArguments :: Map.Map String String -> Test
systemArguments imports = do
  actual <- Harness.evaluateSourceWithArgs ["north", "two words"] "bring often.tung bring deed/system.tung yield arguments" imports
  pure $ if actual == "eval ok: ('north' ('two words' empty ‥) ‥)" then Nothing else Just ("system arguments: " ++ actual)

systemEnvironment :: Map.Map String String -> Test
systemEnvironment imports = bracket (Environment.lookupEnv name) restore $ \_ -> do
  Environment.setEnv name "seen"
  actual <- Harness.evaluateSource ("bring often.tung bring deed/system.tung yield '" ++ name ++ "' environment") imports
  pure $ if actual == "eval ok: ('seen' some)" then Nothing else Just ("system environment: " ++ actual)
  where
    name = "TUNG_TEST_ENVIRONMENT"
    restore Nothing = Environment.unsetEnv name
    restore (Just value) = Environment.setEnv name value

unixTime :: Map.Map String String -> Test
unixTime imports = do
  before <- floor <$> getPOSIXTime
  actual <- Harness.evaluateSource "bring often.tung bring deed/clock.tung yield unix_time" imports
  after <- floor <$> getPOSIXTime
  pure $ case stripPrefix "eval ok: +" actual >>= readMaybe of
    Just value | value >= (before :: Int) && value <= after -> Nothing
    _ -> Just ("unix time is in the host clock range: got " ++ actual)

evalCase :: Map.Map String String -> (String, String, String) -> Test
evalCase imports (name, source, expected) = evalOkWith name source imports expected

typeErrorCase :: Map.Map String String -> (String, String) -> Test
typeErrorCase imports (name, source) = evalTypeErrWith name source imports

boolData, optionData, rowData, deedPrelude, sleepBinding :: String
boolData = "ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } "
optionData = "ilk maybe: [a:*, *] { none: a maybe, some: [a, a maybe] } "
rowData = boolData ++ "ilk row: * { stop: row, more: [𝟚, row, row] } let ones: [n: ℕ, row] ≔ match n { 0 ^ stop, k heir ^ yea more (k ones) } "
deedPrelude = "let sheer:[@a:*, a, a deed] ≔ 'deed_sheer' fremmed let bind:[@a:*, @b:*, a deed, [a, b deed], b deed] ≔ 'deed_bind' fremmed "
sleepBinding = "let sleep:[ℕ, 𝟙 deed] ≔ 'sleep' fremmed "
