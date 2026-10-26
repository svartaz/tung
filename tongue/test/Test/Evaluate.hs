-- checked interactive evaluation, dictionaries, and effects.
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
  [ ("explicit type inputs are erased beside value inputs", "let f:[@a:*, @b:*, x:a, _:b, a] ≔ x yield +1 f @ℤ @string 'x'", "eval ok: +1"),
    ("instance method type inputs are erased", "let id:[@a:*, x:a, a] ≔ x class owner:[a:*, *] { let copy:[@b:*, a, b, b] } bizen:ℤ owner { let copy:[@c:*, _:ℤ, x:c, c] ≔ x id @c } yield +1 copy 'x'", "eval ok: 'x'"),
    ("unused type inputs requireth no runtime argument", "let value:[@a:*, ℤ] ≔ +7 yield value @string", "eval ok: +7"),
    ("higher-rank argument is erased and instantiated twice", "type pair: * { pair_of: [tale: ℤ, word: string, pair] } let both:[f:[@a:*, a, a], pair] ≔ (+1 f) pair_of ('x' f) let id: [@a:*, x: a, a] ≔ x yield (id both).tale", "eval ok: +1"),
    ("polymorphic return needs no runtime type arguments", "let make:[_:ℤ, [@a:*, a, a]] ≔ {x ^ x} yield 'yes' (+1 make)", "eval ok: 'yes'"),
    ("left-associated sequence", "bring often.tung yield <{-+, +10, +3, +2}", "eval ok: +9"),
    ("right-associated sequence", "bring often.tung yield >{-+, +10, +3, +2}", "eval ok: -11"),
    ("nested brace forms share type and expression boundaries", "bring often.tung type inner: * { inner_of: [value: ℤ, inner] } type outer: * { outer_of: [callback: [ℤ, ℤ], nested: inner, outer] } let record:outer ≔ {x ^ <{+, x, +1}} outer_of (+2 inner_of) yield record.nested.value record.callback", "eval ok: +3"),
    ("term type ascription is erased before evaluation", "bring often.tung yield (+1 + +2: ℤ)", "eval ok: +3"),
    ("ascribed anonymous function remaineth recursive", "bring often.tung let factorial ≔ ({ 0 ^ 1, n next ^ (n next) · (n factorial) }: [ℕ, ℕ]) yield 5 factorial", "eval ok: 120"),
    ("ℤ arithmetic is arbitrary precision", "bring often.tung yield +999999999999999999999999999999 + +1", "eval ok: +1000000000000000000000000000000"),
    ("foreign key selecteth a host function independently of the let name", "let plus:[ℤ, ℤ, ℤ] ≔ 'add_integer' foreign yield +1 plus +2", "eval ok: +3"),
    ("unicode string", "yield 'λ字'", "eval ok: 'λ字'"),
    ("unicode control rendering useth decimal terminator", "yield `\\1;", "eval ok: `\\1;"),
    ("float arithmetic", "bring often.tung yield 0.5 + 0.25", "eval ok: 0.75"),
    ("string becometh a float", "bring often.tung bring type/optional.tung let parsed:float optional ≔ '0.5' from_string yield parsed", "eval ok: (0.5 some)"),
    ("unparsable string yieldeth none", "bring often.tung bring type/optional.tung let parsed:float optional ≔ 'not a float' from_string yield parsed", "eval ok: none"),
    ("float division useth the division sign", "bring often.tung yield 6.0 ÷ 4.0", "eval ok: 1.5"),
    ("float division by zero followeth ieee", "bring often.tung yield 1.0 ÷ 0.0", "eval ok: Infinity"),
    ("an infinite float floor yieldeth none", "bring _foreign.tung yield (1.0 divide_float 0.0) ⌊", "eval ok: none"),
    ("a nan float floor yieldeth none", "bring _foreign.tung yield (0.0 divide_float 0.0) ⌊", "eval ok: none"),
    ("float is ignoreth literal spelling", "bring often.tung type 𝟚: * { yea: 𝟚, nay: 𝟚 } yield 1.0 ≍ 1.00", "eval ok: yea"),
    ("bracketed natural constructors construct and match", "type nat: * { zero: nat, suc: [nat, nat] } yield match zero suc { x suc ^ +1, zero ^ +0 }", "eval ok: +1"),
    ("bracketed list constructors preserve native ABI", "type list: [a:*, *] { empty: a list, ‥: [a, a list, a list] } yield match (+1 ‥ empty) { first ‥ _ ^ first, empty ^ +0 }", "eval ok: +1"),
    ("indexed constructor match useth its refined payload", indexedUnpackSource ++ "yield (+3 integer) unpack", "eval ok: +3"),
    ("indexed constructor match useth its other branch", indexedUnpackSource ++ "yield ('hi' textual) unpack", "eval ok: 'hi'"),
    ("float ordering is numeric", "bring often.tung type 𝟚: * { yea: 𝟚, nay: 𝟚 } yield 2.0 ≤ 10.0", "eval ok: yea"),
    ("curried partial application", "bring often.tung let hath_+: [a: ℤ, b: ℤ, ℤ] ≔ a + b let add_one ≔ +1 hath_+ yield +2 add_one", "eval ok: +3"),
    ("local recursive function", "bring often.tung type nat: * { zero: nat, suc: [nat, nat] } let count ≔ (let loop: [nat, ℤ] ≔ { zero ^ +0, n suc ^ +1 + (n loop) } yield loop) yield ((zero suc) suc) count", "eval ok: +2"),
    ("recursive calls retain inferred evidence", "bring often.tung class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x + +1 } let loop: [ℕ, ℤ, ℤ] ≔ { 0, x ^ x identity, n next, x ^ n loop x } yield 2 loop +3", "eval ok: +4"),
    ("recursive evidence surviveth a nested polymorphic binding", "bring often.tung class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x + +1 } let loop: [ℕ, ℤ, ℤ] ≔ { 0, x ^ x identity, n next, x ^ (let echo: [y:] ≔ y identity yield (n loop x) echo) } yield 2 loop +3", "eval ok: +6"),
    ("dollar function segment", "bring often.tung let f: [x: ℤ, ℤ] ≔ x + +1 let h: [x: ℤ, y: ℤ, z: ℤ, ℤ] ≔ (x + y) · z yield +1 f $h +2 +3", "eval ok: +12"),
    ("lexical closure", "let x ≔ +1 let f: [_: ℤ, ℤ] ≔ x yield (let x ≔ +2 yield +0 f)", "eval ok: +1"),
    ("sequential shadowing preserveth each preceding local", "bring often.tung yield (let value ≔ +1 let value ≔ value + +1 let value ≔ value + +1 yield value)", "eval ok: +3"),
    ("nested same-string pattern binders remain distinct", "bring often.tung yield match +1 { value ^ (match +2 { value ^ value }) + value }", "eval ok: +3"),
    ("multi-scrutinee match", boolData ++ "yield match yea, nay { yea, yea ^ +1, yea, nay ^ +2, nay, yea ^ +3, nay, nay ^ +4 }", "eval ok: +2"),
    ("nested constructor match", boolData ++ optionData ++ "yield match nay some { yea some ^ +1, nay some ^ +2, none ^ +0 }", "eval ok: +2"),
    ("ℤ match patterns", "yield match -1 { +0 ^ +10, -1 ^ +20, _ ^ +30 }", "eval ok: +20"),
    ("ℤ patterns fall through", "yield match +2 { +0 ^ +10, +1 ^ +20, _ ^ +30 }", "eval ok: +30"),
    ("alternative constructor patterns share bindings", "type choice: [a:*, *] { left: [a, a choice], right: [a, a choice] } yield match +2 right { x left; x right ^ x }", "eval ok: +2"),
    ("string match patterns", "yield match 'yes' { 'yes' ^ +1, _ ^ +0 }", "eval ok: +1"),
    ("unchosen arm is not evaluated", boolData ++ "yield match yea { yea ^ +1, nay ^ +0 (sorry:[ℤ, ℤ]) }", "eval ok: +1"),
    ("foreign arity followeth a transparent alias", "let binary:* ≔ [ℤ, ℤ, ℤ] let plus:binary ≔ 'add_integer' foreign yield +1 plus +2", "eval ok: +3"),
    ("an unused top-level definition is not computed", "let missing:ℤ ≔ sorry yield +1", "eval ok: +1"),
    ("a demanded top-level definition is computed", "let missing:ℤ ≔ sorry yield missing", "eval error: reached sorry"),
    ("an unused argument is not computed", "let ignore:[_:ℤ, ℤ] ≔ +7 yield (+1 (sorry:[ℤ, ℤ])) ignore", "eval ok: +7"),
    ("an unused local definition is not computed", "yield (let unused:ℤ ≔ +1 (sorry:[ℤ, ℤ]) yield +7)", "eval ok: +7"),
    ("a field projection computeth only the selected field", "type keep: * { keep_of: [kept: ℤ, unused: ℤ, keep] } yield (+7 keep_of (+1 (sorry:[ℤ, ℤ]))).kept", "eval ok: +7"),
    ("recursion under a match computeth only the chosen branch", rowData ++ "let flips: [r: row, inside: 𝟚, ℕ] ≔ match r { stop ^ 0, _ more leftover ^ match inside { yea ^ (leftover flips nay) next, nay ^ leftover flips yea } } yield (64 ones) flips yea", "eval ok: 32"),
    ("a user function computeth only its selected recursive input", recursiveChoiceSource, "eval ok: +8"),
    ("an unused constructor field and recursive hypothesis are not computed", rowData ++ "let first: [r: row, 𝟚] ≔ match r { stop ^ nay, c more _ ^ c } yield (yea more (0 (sorry:[ℕ, row]))) first", "eval ok: yea"),
    ("reaching an axiom is a runtime error", boolData ++ "axiom missing: 𝟚 yield missing", "eval error: reached axiom 'missing'"),
    ("a yielded value is computed in full", "type keep: * { keep_of: [kept: ℤ, missing: ℤ, keep] } yield +1 keep_of (sorry: ℤ)", "eval error: reached sorry"),
    ("a yielded effect is performed", "bring type/one.tung " ++ sleepBinding ++ "yield 0 sleep", "eval ok: only"),
    ("effect_bind passeth a result on", effectPrelude ++ "let plus:[ℤ, ℤ, ℤ] ≔ 'add_integer' foreign yield (+2 pure) bind { x ^ (x plus +1) pure }", "eval ok: +3"),
    ("an effect is a value until performed", effectPrelude ++ "let action:ℤ effect ≔ +1 pure yield (let unused ≔ action yield +2)", "eval ok: +2"),
    ("class laws are erased", "bring is.tung class hath_identity:[a:*, *] { let identity:[a, a] let rule:[x: a, (x identity) = x] } bizen:ℤ hath_identity { let identity: [x:] ≔ x let rule ≔ sorry } yield +2 identity", "eval ok: +2"),
    ("result-only member useth expected type", "class hath_origin:[a:*, *] { let origin:a } bizen:ℤ hath_origin { let origin ≔ +7 } let value:ℤ ≔ origin yield value", "eval ok: +7"),
    ("different instances dispatch by inferred type", "class hath_label:[a:*, *] { let label:[a, string] } bizen:ℤ hath_label { let label: [_:] ≔ 'ℤ' } bizen:string hath_label { let label: [_:] ≔ 'string' } yield 'x' label", "eval ok: 'string'"),
    ("constraint function receiveth its caller dictionary", "class hath_label:[a:*, *] { let label:[a, string] } bizen:ℤ hath_label { let label: [_:] ≔ 'ℤ' } bizen:string hath_label { let label: [_:] ≔ 'string' } let labelled:[@a:*, @:a hath_label, x: a, string] ≔ x label yield +1 labelled", "eval ok: 'ℤ'"),
    ("child dictionary useth a direct parent instance", "class hath_parent:[a:*, *] { let parent:[a, a] } class hath_child:[a:*, @:a hath_parent, *] { let child:[a, a] } bizen:ℤ hath_parent { let parent: [x:] ≔ x } bizen:ℤ hath_child { let child: [x:] ≔ x parent } yield +4 child", "eval ok: +4"),
    ("repeated bizen calls retain a preceding private value", "bring often.tung class hath_bump:[a:*, *] { let bump:[a, a] } let offset ≔ +2 bizen:ℤ hath_bump { let bump: [x:] ≔ x + offset } yield (+1 bump) + (+2 bump)", "eval ok: +7"),
    ("bizen may precede its resolved class declaration", "bizen:ℤ hath_identity { let identity: [x:] ≔ x } class hath_identity:[a:*, *] { let identity:[a, a] } yield +3 identity", "eval ok: +3"),
    ("bizen constraint remaineth an external dictionary", "bring often.tung class hath_combine:[a:*, *] { let combine:[a, a, a] } bizen:ℤ hath_combine { let combine: [x:, y:] ≔ x + y } type _box: [a:*, *] { box: [a, a _box] } bizen:[@a:*, @:a hath_combine, (a _box) hath_combine] { let combine: [x box:, y box:] ≔ (x combine y) box } yield (+1 box) combine (+2 box)", "eval ok: (+3 box)")
  ]

indexedUnpackSource :: String
indexedUnpackSource =
  "type tag: [a:*, *] { integer: [ℤ, ℤ tag], textual: [string, string tag] } "
    ++ "let unpack:[@a:*, x:a tag, a] ≔ match x { n integer ^ n, t textual ^ t } "

-- both inputs recurse; the discarded path faileth at its base.
recursiveChoiceSource :: String
recursiveChoiceSource =
  rowData
    ++ """
       let hath_+:[ℤ, ℤ, ℤ] ≔ 'add_integer' foreign
       let choose:[flag:𝟚, yes:ℤ, no:ℤ, ℤ] ≔ match flag { yea ^ yes, nay ^ no }
       let count:[r:row, flag:𝟚, ℤ] ≔ match r {
         stop ^ match flag { yea ^ +0, nay ^ +0 (sorry:[ℤ, ℤ]) },
         _ more leftover ^ flag choose (+1 hath_+ (leftover count yea)) (leftover count nay)
       }
       yield (8 ones) count yea

       """

typeErrors :: [(String, String)]
typeErrors =
  [ ("captured alias mismatch is rejected before evaluation", "let bad: [x:] ≔ (let y ≔ x let tale:ℤ ≔ y yield tale + +1) yield 'oops' bad"),
    ("non-function application", "yield +1 +2"),
    ("constructor overapplication", "type _box: [a:*, *] { box: [a, a _box] } yield +1 box +2")
  ]

importedCases :: Map.Map String String -> [Test]
importedCases imports =
  [ evalOkWith
      "a local term and an imported constructor retain distinct runtime identities"
      "bring token.tung type pair: * { pair_of: [constructor: token, local: ℤ, pair] } let box ≔ +7 yield token~box pair_of box"
      (Map.singleton "token.tung" "show type token: * { box: token }")
      "eval ok: (box +7 pair_of)",
    evalOkWith "imported call" "bring often.tung bring file.tung yield +2 inc" (Map.insert "file.tung" "bring often.tung show let inc: [x:] ≔ x + +1" imports) "eval ok: +3",
    evalOkWith "a use declaration is initialised before a preceding let" "let answer ≔ dep~value bring dep.tung yield answer" (Map.insert "dep.tung" "show let value ≔ +7" imports) "eval ok: +7",
    evalOkWith "a local and its imported predecessor retain distinct identities" "bring often.tung bring source.tung let value ≔ source~value + +1 yield value + source~value" (Map.insert "source.tung" "show let value ≔ +2" imports) "eval ok: +5",
    evalTypeErrWith "a local value shadoweth an imported constructor in patterns" "bring type/two.tung let yea:𝟚 ≔ two~yea yield match yea { yea ^ +1, nay ^ +0 }" imports,
    evalOkWith "a qualified pattern still reacheth a shadowed constructor" "bring type/two.tung let yea ≔ +0 yield match two~yea { two~yea ^ +1, nay ^ +0 }" imports "eval ok: +1",
    evalOkWith "default use alias worketh for values, classes, and constructor patterns" "bring type/item.tung let value:item~_item ≔ item~empty yield match (value item~identity) { item~item ^ +1 }" (Map.insert "type/item.tung" "show type _item: * { item: _item } show class hath_identity:[a:*, *] { let identity:[a, a] } bizen:_item hath_identity { let identity: [x:] ≔ x } show let empty:_item ≔ item" imports) "eval ok: +1",
    evalOkWith "derived class operations" "bring often.tung yield (+1 < +2) ⋏ (+1 ≭ +2)" imports "eval ok: yea",
    evalOkWith "false implieth false" "bring often.tung yield nay ≤ nay" imports "eval ok: yea",
    evalOkWith "true doth not imply false" "bring often.tung yield yea ≤ nay" imports "eval ok: nay",
    evalOkWith "next patterns recurse on a natural" "bring often.tung let double: [n: ℕ, ℕ] ≔ match n { 0 ^ 0, m next ^ (m double) + 2 } yield 3 double" imports "eval ok: 6",
    evalOkWith "next addeth one to a natural" "yield (2 next) next" imports "eval ok: 4",
    evalOkWith "euclidean division returneth quotient and remainder for a negative divisor" "bring often.tung bring type/and.tung yield +5 % -3" imports "eval ok: ((-1 +2 ⸴) some)",
    evalOkWith "euclidean division returneth quotient and remainder for a negative dividend" "bring often.tung bring type/and.tung yield -5 % +3" imports "eval ok: ((-2 +1 ⸴) some)",
    evalOkWith "euclidean quotient and remainder reconstruct the dividend" "bring often.tung bring type/optional.tung bring type/and.tung let dividend ≔ -5 let divisor ≔ -3 yield match dividend % divisor { (quotient ⸴ leftover) some ^ (quotient · divisor) + leftover, none ^ +0 }" imports "eval ok: -5",
    evalOkWith "euclidean division faileth at zero" "bring often.tung yield +1 % +0" imports "eval ok: none",
    evalOkWith "three-way comparison distinguishes each result" "bring often.tung bring type/and.tung yield (+0 compare +1) ⸴ (+1 compare +1) $⸴ (+2 compare +1)" imports "eval ok: ((fore mid ⸴) aft ⸴)",
    evalOkWith "clamp keepeth a value inside its bounds" "bring often.tung yield +0 clamp +10 +12" imports "eval ok: +10",
    evalOkWith "qualified duplicate values" "bring often.tung bring left.tung bring right.tung yield left~foo + right~foo" (duplicateImports <> imports) "eval ok: +3",
    evalOkWith "shared diamond import" "bring often.tung bring left.tung bring right.tung yield left~left + right~right" (diamondImports <> imports) "eval ok: +5",
    evalOkWith "diamond import keepeth one bizen identity" "bring left.tung bring right.tung yield +3 left~identity" (instanceDiamondImports <> imports) "eval ok: +3",
    evalOkWith "qualified classes from different modules stay distinct" "bring often.tung bring left.tung bring right.tung yield +3 left~identity" (distinctClassImports <> imports) "eval ok: +4",
    evalOkWith "inherited same-named members select the requested class" (collidingMemberPrelude ++ "bizen:ℤ first { let tag: [_:] ≔ +1 } bizen:ℤ second { let tag: [_:] ≔ +2 } bizen:ℤ both { let own: [_:] ≔ +3 } let outcome:[@a:*, @:a both, x: a, ℤ] ≔ x right~tag yield +1 outcome") (collidingMemberImports <> imports) "eval ok: +2",
    evalOkWith "a child member override doth not replace a sibling class member" ("bring often.tung " ++ collidingMemberPrelude ++ "bizen:ℤ second { let tag: [_:] ≔ +2 } bizen:ℤ both { let tag: [_:] ≔ +10 let own: [_:] ≔ +3 } let outcome:[@a:*, @:a both, x: a, ℤ] ≔ (x left~tag) + (x right~tag) yield +1 outcome") (collidingMemberImports <> imports) "eval ok: +12",
    evalOkWith "instances in extension-sharing paths stay distinct" "bring often.tung bring a.tung one bring a.extra.tung two yield (+1 one~identity) + (+1 two~identity)" (samePrefixInstanceImports <> imports) "eval ok: +13",
    evalOkWith "instances beneath dotted directories stay distinct" "bring often.tung bring pkg.one/identity.tung one bring pkg.two/identity.tung two yield (+1 one~identity) + (+1 two~identity)" (dottedDirectoryInstanceImports <> imports) "eval ok: +13",
    evalOkWith "same-spelled imported data types dispatch through distinct instances" "bring often.tung bring common.tung bring left.tung bring right.tung yield (left~value common~label) + (right~value common~label)" (nominalTypeInstanceImports <> imports) "eval ok: +11",
    evalOkWith "an imported transparent alias useth its underlying instance" "bring base.tung bring alias.tung yield alias~value base~label" (transparentAliasInstanceImports <> imports) "eval ok: +7",
    evalOkWith "an exported alias retaineth its private nominal instance" "bring opaque.tung opaque yield opaque~value opaque~label" (privateAliasInstanceImports <> imports) "eval ok: +7",
    evalOkWith "a local class and bizen shadow an imported namesake" "bring often.tung bring left.tung class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x + +2 } yield (+1 identity) + (+1 left~identity)" (distinctClassImports <> imports) "eval ok: +5",
    evalTypeErrWith "local evidence cannot satisfy an imported namesake class" "bring left.tung class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x } let imported_use:[@a:*, @:a left~hath_identity, x: a, a] ≔ x left~identity let local_use:[@a:*, @:a hath_identity, x: a, a] ≔ x imported_use yield +1 local_use" (distinctClassImports <> imports),
    evalOkWith "value survives a named re-export" "bring middle.tung yield value" (reexportImports <> imports) "eval ok: +7",
    evalOkWith "qualified re-export outranketh a shadowing local" "bring often.tung bring middle.tung let value ≔ +3 yield middle~value + value" (reexportImports <> imports) "eval ok: +10",
    evalOkWith "class bizen survives an import" "bring identity.tung yield +3 identity" (identityImports <> imports) "eval ok: +3",
    evalOkWith "specific bizen outranketh a blanket instance" "bring often.tung class hath_identity:[a:*, *] { let identity:[a, a] } bizen:[@a:*, a hath_identity] { let identity: [x:] ≔ x } bizen:ℤ hath_identity { let identity: [x:] ≔ x + +1 } yield +1 identity" imports "eval ok: +2",
    evalOkWith "data constructor survives a named re-export" "bring data_middle.tung yield +4 box" (dataReexportImports <> imports) "eval ok: (+4 box)",
    evalOkWith "constructor identity survives a different re-export path" "bring data_base.tung bring data_middle.tung yield match +4 data_middle~box { x data_base~box ^ x }" (dataReexportImports <> imports) "eval ok: +4",
    evalOkWith "constructor pattern surviveth a middle-module re-export" "bring middle.tung yield match middle~off { middle~off ^ +1 }" (constructorReexportImports <> imports) "eval ok: +1",
    evalOkWith "qualified constructor pattern useth import alias" "bring alias.tung yield match +4 alias~box { x alias~box ^ x }" (Map.insert "alias.tung" "show type _box: [a:*, *] { box: [a, a _box] }" imports) "eval ok: +4",
    evalTypeErrWith "private qualified value is rejected before runtime" "bring private.tung yield private~hidden" (Map.fromList [("private.tung", "let hidden ≔ +1")]),
    evalOkWith "string converteth to a unicode list" "bring often.tung yield 'λ😀' string_to_list" imports "eval ok: (`λ (`😀 empty ‥) ‥)",
    evalOkWith "unicode converteth to its scalar ℕ" "bring often.tung yield `😀 unicode_to_natural" imports "eval ok: 128512",
    evalOkWith "scalar ℕ converteth to unicode" "bring often.tung yield 128512 natural_to_unicode" imports "eval ok: (`😀 some)",
    evalOkWith "surrogate ℕ cannot become unicode" "bring often.tung yield 55296 natural_to_unicode" imports "eval ok: none",
    evalOkWith "out-of-range ℕ cannot become unicode" "bring often.tung yield 1114112 natural_to_unicode" imports "eval ok: none",
    evalOkWith "string behead exposeth one code point" "bring often.tung bring type/list.tung bring type/optional.tung bring type/and.tung bring class/algebra/total/hath_multiply.tung yield match 'λ字' behead_string { (c ⸴ leftover) optional~some ^ ((c ‥ empty) list_to_string) · leftover, optional~none ^ '' }" imports "eval ok: 'λ字'",
    evalOkWith "empty string hath no head" "bring often.tung bring type/optional.tung yield match '' behead_string { none ^ +1, _ some ^ +0 }" imports "eval ok: +1",
    evalOkWith "generic string fold" "bring often.tung bring type/list.tung bring class/functor/catamorphism.tung yield ('north' ‥ ('南' ‥ empty)) …·" imports "eval ok: 'north南'",
    evalOkWith "string classes dispatch" "bring often.tung bring class/algebra/total/hath_multiply.tung yield (('a' · 'β') ≍ 'aβ') ⋏ ('a' ≤ 'b')" imports "eval ok: yea",
    evalOkWith "unicode classes dispatch" "bring often.tung yield (`a ≍ `a) ⋏ (`a ≤ `b)" imports "eval ok: yea",
    evalOkWith "imported bizen doth not shadow native ℤ order" "bring type/list.tung yield +0 till +3" imports "eval ok: (+0 (+1 (+2 empty ‥) ‥) ‥)",
    evalOkWith "list map pipeline keepeth the list functor" "bring often.tung bring type/list.tung yield +0 till +3 $ map { x ^ x + +1 } $ map to_string" imports "eval ok: ('1' ('2' ('3' empty ‥) ‥) ‥)",
    evalOkWith "list apply calleth its separate map instance" "bring often.tung bring type/list.tung let values ≔ +1 ‥ (+2 ‥ empty) let functions ≔ { x ^ x + +10 } ‥ ({ x ^ x · +2 } ‥ empty) yield values apply functions" imports "eval ok: (+11 (+12 (+2 (+4 empty ‥) ‥) ‥) ‥)",
    evalOkWith "list traversal sequences optional values" "bring often.tung bring type/list.tung bring type/optional.tung bring class/functor/hath_traverse.tung yield (+1 ‥ (+2 ‥ empty)) traverse { x ^ x optional~some }" imports "eval ok: ((+1 (+2 empty ‥) ‥) some)",
    evalOkWith "fold_map combineth mapped list values" "bring often.tung bring type/list.tung bring class/functor/catamorphism.tung yield (+0 till +3) gather_map to_string" imports "eval ok: '012'",
    evalOkWith "bounded conjunction folds values" "bring often.tung bring type/list.tung bring class/functor/catamorphism.tung yield yea ‥ (nay ‥ empty) $ …⋏" imports "eval ok: nay",
    evalOkWith "empty bounded disjunction useth the lower endpoint" "bring often.tung bring type/list.tung bring class/functor/catamorphism.tung let values:𝟚 list ≔ empty yield values …⋎" imports "eval ok: nay",
    evalOkWith "boolean complement negateth" "bring often.tung yield yea ∁" imports "eval ok: nay",
    evalTypeErrWith "bounded lattice need not have a complement" "bring often.tung yield mid ∁" imports,
    evalOkWith "ℤ lattice chooseth the lesser value" "bring often.tung yield +3 ⋏ +2" imports "eval ok: +2",
    evalOkWith "total order supplieth a distributive lattice" "bring often.tung let distribute:[@a:*, @:a lattice_distributive, x: a, y: a, z: a, a] ≔ x ⋏ (y ⋎ z) yield +3 distribute +2 +4" imports "eval ok: +3",
    evalOkWith "non-total powerset lattice joineth predicates" "bring often.tung bring type/list.tung bring type/powerset.tung bring class/functor/catamorphism.tung let one:ℤ powerset ≔ { x ^ x ≍ +1 } let two:ℤ powerset ≔ { x ^ x ≍ +2 } let joined ≔ one ‥ (two ‥ list~empty) $ …⋎ yield joined ∋ +2" imports "eval ok: yea",
    evalOkWith "empty powerset meet yieldeth the universal set" "bring often.tung bring type/list.tung bring type/powerset.tung bring class/functor/catamorphism.tung let values:(ℤ powerset) list ≔ list~empty let all ≔ values …⋏ yield all ∋ +42" imports "eval ok: yea",
    evalOkWith "pattern binders do not become constructor patterns" "bring often.tung bring type/list.tung type bit: * { off: bit } yield +0 till +3 $ map { _ ^ off } $ map { _ ^ +1 }" imports "eval ok: (+1 (+1 (+1 empty ‥) ‥) ‥)",
    evalOkWith "control branch suspends actions" "bring often.tung yield nay branch { _ ^ +1 } { _ ^ +2 }" imports "eval ok: +2",
    evalOkWith "optional optional mapeth present value" "bring often.tung bring type/optional.tung yield (+3 some) handle +0 { x ^ x + +1 }" imports "eval ok: +4",
    evalOkWith "sum either consumeth selected side" "bring often.tung bring type/or.tung yield (+2 inject₁) either { x ^ x + +1 } { y ^ y · +3 }" imports "eval ok: +6",
    evalOkWith "sum bimap mapeth the selected side" "bring often.tung bring type/or.tung let value:ℤ ∨ string ≔ +2 inject₀ yield match (value bimap { x ^ x + +1 } { string ^ string }) { x inject₀ ^ x, _ inject₁ ^ +0 }" imports "eval ok: +3",
    evalOkWith "sum functor mapeth the right side" "bring often.tung bring type/or.tung let value:string ∨ ℤ ≔ +2 inject₁ yield match (value map { x ^ x + +1 }) { _ inject₀ ^ +0, x inject₁ ^ x }" imports "eval ok: +3",
    evalOkWith "sum applicative applieth the right side" "bring often.tung bring type/or.tung let value:string ∨ ℤ ≔ +2 inject₁ let f:string ∨ [ℤ, ℤ] ≔ { x ^ x + +3 } inject₁ yield match value apply f { _ inject₀ ^ +0, x inject₁ ^ x }" imports "eval ok: +5",
    evalOkWith "sum monad preserveth a left value" "bring often.tung bring type/or.tung let value:string ∨ ℤ ≔ 'left' inject₀ yield match (value bind { x ^ (x + +1) inject₁ }) { message inject₀ ^ message, x inject₁ ^ x to_string }" imports "eval ok: 'left'",
    evalOkWith "sum catamorphism foldeth the right side" "bring often.tung bring type/or.tung bring class/functor/catamorphism.tung let value:string ∨ ℤ ≔ +3 inject₁ yield value gather₁ +1 +" imports "eval ok: +4",
    evalOkWith "sum traversal preserveth its side" "bring often.tung bring type/or.tung bring type/optional.tung bring class/functor/hath_traverse.tung let value:string ∨ ℤ ≔ +3 inject₁ yield value traverse { x ^ (x + +1) some }" imports "eval ok: ((+4 inject₁) some)",
    evalOkWith "product bimap mapeth both fields" "bring often.tung bring type/and.tung yield (+1 ⸴ +2) bimap { x ^ x + +1 } { y ^ y · +3 }" imports "eval ok: (+2 +6 ⸴)",
    evalOkWith "product applicative accumulateth value context first" "bring often.tung bring type/and.tung let value ≔ 'value:' ⸴ +2 let f ≔ 'function:' ⸴ { x ^ x + +1 } yield value apply f" imports "eval ok: ('value:function:' +3 ⸴)",
    evalOkWith "product monad accumulateth outer context first" "bring often.tung bring type/and.tung yield ('outer:' ⸴ +2) bind { x ^ 'inner:' ⸴ (x + +1) }" imports "eval ok: ('outer:inner:' +3 ⸴)",
    evalOkWith "product catamorphism foldeth the second field" "bring often.tung bring type/and.tung bring class/functor/catamorphism.tung yield ('ignored' ⸴ +3) gather₁ +1 +" imports "eval ok: +4",
    evalOkWith "product traversal preserveth the first field" "bring often.tung bring type/and.tung bring type/optional.tung bring class/functor/hath_traverse.tung yield ('context' ⸴ +3) traverse { x ^ (x + +1) some }" imports "eval ok: (('context' +4 ⸴) some)",
    evalOkWith "reader functor mappeth the outcome" "bring often.tung yield 3 (map @(ℕ →) { n ^ n + n } { n ^ n + 1 })" imports "eval ok: 7",
    evalOkWith "reader monad readeth one input twice" "bring often.tung bring class/functor/monad.tung yield 3 (bind @(ℕ →) { n ^ n + n } { d ^ { n ^ d + n } })" imports "eval ok: 9",
    evalOkWith "contravariant contramap feedeth the input first" "bring often.tung bring combinator.tung bring class/functor/contravariant.tung yield 2 (contramap @(𝟚 ←) { n ^ 3 < n } { n ^ n + n })" imports "eval ok: yea",
    evalOkWith "▶ and ◀ apply from either side, and ◁ runneth its right arrow first" "bring often.tung bring combinator.tung bring class/algebra/partial/semigroupoid.tung bring type/list.tung yield >{‥, 2 ▶ { n ^ n + 1 }, { n ^ n + n } ◀ 3, 3 ▶ ({ n ^ n + 1 } ◁ { n ^ n + n }), empty}" imports "eval ok: (3 (6 (7 empty ‥) ‥) ‥)",
    evalOkWith "kleisli arrows compose by binding" "bring often.tung bring class/algebra/partial/category.tung bring class/algebra/partial/semigroupoid.tung bring type/list.tung bring type/optional.tung bring type/kleisli.tung let less: [ℕ, ℕ optional] ≔ { 0 ^ none, n next ^ n some } yield >{‥, 2 ((less wrap) ▷ (less wrap) $ unwrap), 1 ((less wrap) ▷ (less wrap) $ unwrap), 2 ((less wrap) ▷ identity $ unwrap), empty}" imports "eval ok: ((0 some) (none ((1 some) empty ‥) ‥) ‥)",
    evalOkWith "applicative lift2 for optional" "bring often.tung bring type/optional.tung yield (+1 some) lift₂ (+2 some) +" imports "eval ok: (+3 some)",
    evalOkWith "applicative keep_other preserveth context order" "bring often.tung bring type/and.tung yield ('left:' ⸴ +1) keep_other ('right:' ⸴ +2)" imports "eval ok: ('right:left:' +2 ⸴)",
    evalOkWith "functor void for optional" "bring type/optional.tung bring class/functor.tung yield (+1 some) void" imports "eval ok: (only some)",
    evalOkWith "freer bind transformeth a completed value" (freerPrelude ++ "yield ((+3 done) freer~bind { value ^ (value + +1) done }) run") imports "eval ok: +4",
    evalOkWith "freer lift and fold may repeat a continuation" (freerPrelude ++ "yield ask_freer run") imports "eval ok: +3",
    evalOkWith "freer bind may discard a continuation" (freerPrelude ++ "yield (ask_freer freer~bind { _ ^ +0 done }) run") imports "eval ok: +0",
    evalOkWith "freer mapping and flattening preserve suspended requests" (freerPrelude ++ "yield (ask_freer often~map { value ^ value + +10 } $ freer~map { value ^ value done } $ freer~flat) run") imports "eval ok: +23",
    evalOkWith "list behead exposeth the head and tail" "bring type/list.tung bring type/optional.tung bring type/and.tung yield match (+1 ‥ empty) behead { (head and~⸴ _) optional~some ^ head, optional~none ^ +0 }" imports "eval ok: +1",
    evalOkWith "till excludeth its stop" "bring type/list.tung yield >{‥, +2 till +2, +3 till +1, -1 till +1, empty}" imports "eval ok: (empty (empty ((-1 (+0 empty ‥) ‥) empty ‥) ‥) ‥)",
    evalOkWith "list take after drop" "bring type/list.tung yield ((+0 till +5) drop 2) take 2" imports "eval ok: (+2 (+3 empty ‥) ‥)",
    evalOkWith "list find returneth first match" "bring often.tung bring type/list.tung yield (+0 till +5) find { x ^ +3 ≤ x }" imports "eval ok: (+3 some)",
    evalOkWith "list indexing is zero based" "bring type/list.tung yield (+10 ‥ (+20 ‥ empty)) at 1" imports "eval ok: (+20 some)",
    evalOkWith "list index past the end faileth" "bring often.tung bring type/list.tung yield (+10 ‥ (+20 ‥ empty)) at 2" imports "eval ok: none",
    evalOkWith "natural subtraction stoppeth at zero" "bring often.tung yield (2 ∸ 3) + (5 ∸ 2)" imports "eval ok: 3",
    evalOkWith "list last returneth the final value" "bring type/list.tung yield (+1 ‥ (+2 ‥ empty)) last" imports "eval ok: (+2 some)",
    evalOkWith "empty list hath no last value" "bring type/list.tung let values:ℤ list ≔ empty yield values last" imports "eval ok: none",
    evalOkWith "list membership findeth a value" "bring often.tung bring type/list.tung yield (+1 ‥ (+2 ‥ empty)) ∋ +2" imports "eval ok: yea",
    evalOkWith "list membership rejecteth a missing value" "bring often.tung bring type/list.tung yield (+1 ‥ (+2 ‥ empty)) ∋ +3" imports "eval ok: nay",
    evalOkWith "list replicate useth a nonnegative count" "bring type/list.tung yield 'x' replicate 3" imports "eval ok: ('x' ('x' ('x' empty ‥) ‥) ‥)",
    evalOkWith "a vector head needeth no optional" "bring often.tung bring type/vector.tung m yield (+1 m~‥ (+2 m~‥ m~empty)) m~head" imports "eval ok: +1",
    evalOkWith "a zip at a place pairs the values there" "bring often.tung bring type/and.tung bring type/natural_below.tung bring type/vector.tung m yield ((+1 m~‥ (+2 m~‥ m~empty)) m~zip ('a' m~‥ ('b' m~‥ m~empty))) m~at (least after)" imports "eval ok: (+2 'b' ⸴)",
    evalOkWith "the greatest common divisor of two tales" "bring often.tung bring type/natural_division.tung yield 12 greatest_common_divisor 18" imports "eval ok: 6",
    evalOkWith "a hade over bare is pure state" "bring often.tung bring type/and.tung bring type/bare.tung bring type/hade.tung bring class/functor/monad.tung yield ((((_ + 1) tweak) then get) hade~unwrap 1) bare~unwrap" imports "eval ok: (2 2 ⸴)",
    evalOkWith "holes make functions of their inputs" "bring often.tung bring type/and.tung bring type/list.tung yield ((+0 till +3) map (_ + +10)) ⸴ (+2 (_ · _) +3)" imports "eval ok: ((+10 (+11 (+12 empty ‥) ‥) ‥) +6 ⸴)",
    evalOkWith "list shedding preserveth order" "bring often.tung bring type/list.tung yield (+0 till +5) shed { x ^ +2 ≤ x }" imports "eval ok: ((+2 (+3 (+4 empty ‥) ‥) ‥) (+0 (+1 empty ‥) ‥) ⸴)",
    evalOkWith "list unzip preserveth both sides" "bring type/list.tung bring type/and.tung yield ((+1 ⸴ 'a') ‥ ((+2 ⸴ 'b') ‥ empty)) unzip" imports "eval ok: ((+1 (+2 empty ‥) ‥) ('a' ('b' empty ‥) ‥) ⸴)",
    evalOkWith "n-ary sum addeth a foldable collection" "bring often.tung bring type/list.tung bring class/functor/catamorphism.tung yield (+1 ‥ (+2 ‥ (+3 ‥ empty))) …+" imports "eval ok: +6",
    evalOkWith "n-ary sum of an empty collection is zero" "bring often.tung bring type/list.tung bring class/functor/catamorphism.tung let values:ℤ list ≔ empty yield values …+" imports "eval ok: +0",
    evalTypeErrWith "n-ary sum needeth a catamorphism" "bring often.tung bring class/functor/catamorphism.tung type _box: [a:*, *] { box: [a, a _box] } let value:ℤ _box ≔ +1 box yield value …+" imports,
    evalOkWith "n-ary product multiplies a foldable collection" "bring often.tung bring type/list.tung bring class/functor/catamorphism.tung yield (+2 ‥ (+3 ‥ (+4 ‥ empty))) …·" imports "eval ok: +24",
    evalOkWith "n-ary product of an empty collection is one" "bring often.tung bring type/list.tung bring class/functor/catamorphism.tung let values:ℤ list ≔ empty yield values …·" imports "eval ok: +1",
    evalTypeErrWith "n-ary product needeth a multiply monoid" "bring often.tung bring type/list.tung bring class/functor/catamorphism.tung yield (`a ‥ empty) …·" imports,
    evalOkWith "boolean upper wrapper useth disjunction" "bring often.tung bring type/list.tung bring class/algebra/total/semigroup_multiply.tung bring class/functor/catamorphism.tung let values ≔ (nay upper) ‥ ((yea upper) ‥ list~empty) yield match values …· { outcome upper ^ outcome }" imports "eval ok: yea",
    evalOkWith "empty boolean upper fold yieldeth nay" "bring often.tung bring type/list.tung bring class/algebra/total/semigroup_multiply.tung bring class/functor/catamorphism.tung let values:(𝟚 _upper) list ≔ list~empty yield match values …· { outcome upper ^ outcome }" imports "eval ok: nay",
    evalOkWith "boolean lower wrapper useth conjunction" "bring often.tung bring type/list.tung bring class/algebra/total/semigroup_multiply.tung bring class/functor/catamorphism.tung let values ≔ (yea lower) ‥ ((nay lower) ‥ list~empty) yield match values …· { outcome lower ^ outcome }" imports "eval ok: nay",
    evalOkWith "empty boolean lower fold yieldeth yea" "bring often.tung bring type/list.tung bring class/algebra/total/semigroup_multiply.tung bring class/functor/catamorphism.tung let values:(𝟚 _lower) list ≔ list~empty yield match values …· { outcome lower ^ outcome }" imports "eval ok: yea",
    evalOkWith "natural semiring computeth with both identities" "bring often.tung bring type/natural.tung let two:ℕ ≔ 2 let three ≔ two + 1 yield ((two · three) + one) to_ℤ" imports "eval ok: +7",
    evalOkWith "natural semiring supplieth multiply monoid evidence" "bring often.tung bring type/list.tung bring type/natural.tung bring class/functor/catamorphism.tung let two:ℕ ≔ 2 let three ≔ two + 1 yield ((two ‥ (three ‥ list~empty)) …·) to_ℤ" imports "eval ok: +6",
    evalOkWith "nonnegative ℤ converteth to natural" "bring often.tung bring type/natural.tung yield +3 to_ℕ" imports "eval ok: (3 some)",
    evalOkWith "unsigned digits are a natural" "bring often.tung yield (2 + 3) · 4" imports "eval ok: 20",
    evalOkWith "negative ℤ cannot become natural" "bring often.tung yield -1 to_ℕ" imports "eval ok: none",
    evalOkWith "complex exponentiation scaleth by the real exponent" "bring often.tung bring type/complex.tung yield ((1.0 +i 0.0) exponent) real" imports "eval ok: 2.718281828459045",
    evalOkWith "complex sine of unit imaginary yieldeth hyperbolic sine" "bring often.tung bring type/complex.tung yield ((0.0 +i 1.0) sine) imaginary" imports "eval ok: 1.1752011936438014",
    evalOkWith "complex cosine of unit imaginary yieldeth hyperbolic cosine" "bring often.tung bring type/complex.tung yield ((0.0 +i 1.0) cosine) real" imports "eval ok: 1.5430806348152437",
    evalOkWith "unempty map preserveth the first element" "bring often.tung bring type/list.tung bring type/unempty.tung yield ((+1 ‥′ (+2 ‥ empty)) map { x ^ x + +1 }) to_list" imports "eval ok: (+2 (+3 empty ‥) ‥)",
    evalOkWith "unempty semigroup appendeth without losing the head" "bring often.tung bring type/list.tung bring type/unempty.tung bring class/algebra/total/hath_multiply.tung yield ((+1 ‥′ (+2 ‥ empty)) · (+3 ‥′ empty)) to_list" imports "eval ok: (+1 (+2 (+3 empty ‥) ‥) ‥)",
    evalOkWith "unempty applicative applieth every function" "bring often.tung bring type/list.tung bring type/unempty.tung let values ≔ +1 ‥′ (+2 ‥ empty) let fs ≔ { x ^ x + +1 } ‥′ ({ x ^ x · +2 } ‥ empty) yield (values apply fs) to_list" imports "eval ok: (+2 (+3 (+2 (+4 empty ‥) ‥) ‥) ‥)",
    evalOkWith "unempty monad concatenateth every result" "bring often.tung bring type/list.tung bring type/unempty.tung let values ≔ +1 ‥′ (+2 ‥ empty) yield (values bind { x ^ x ‥′ ((x + +10) ‥ empty) }) to_list" imports "eval ok: (+1 (+11 (+2 (+12 empty ‥) ‥) ‥) ‥)",
    evalOkWith "unempty catamorphism visiteth the head first" "bring often.tung bring type/list.tung bring type/unempty.tung bring class/functor/catamorphism.tung yield (+1 ‥′ (+2 ‥ empty)) gather₁ +0 +" imports "eval ok: +3",
    evalOkWith "unempty traversal keepeth a unempty result" "bring often.tung bring type/list.tung bring type/unempty.tung bring type/optional.tung bring class/functor/hath_traverse.tung yield ((+1 ‥′ (+2 ‥ empty)) traverse { x ^ (x + +1) some }) map to_list" imports "eval ok: ((+2 (+3 empty ‥) ‥) some)",
    evalOkWith "unempty membership delegateth to list" "bring often.tung bring type/list.tung bring type/unempty.tung yield (+1 ‥′ (+2 ‥ empty)) ∋ +2" imports "eval ok: yea",
    evalOkWith "table put replaceth a key" "bring often.tung bring type/table.tung let table ≔ (empty put 'a' +1) put 'a' +2 yield table lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "table membership dispatcheth through inhold" "bring often.tung bring type/table.tung let table ≔ empty put 'a' +1 yield table ∋ 'a'" imports "eval ok: yea",
    evalOkWith "table constructor may be qualified" "bring often.tung bring type/list.tung bring type/and.tung bring type/table.tung yield (('a' ⸴ +2) ‥ list~empty) table~from_list $ lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "tree keepeth its keys in order" "bring often.tung bring type/tree.tung let t ≔ ((empty put 'c' +3) put 'a' +1) put 'b' +2 yield t keys" imports "eval ok: ('a' ('b' ('c' empty ‥) ‥) ‥)",
    evalOkWith "tree put replaceth a key" "bring often.tung bring type/tree.tung let t ≔ (empty put 'a' +1) put 'a' +2 yield t lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "tree rid droppeth a key and keepeth the rest" "bring often.tung bring type/tree.tung let t ≔ ((empty put 2 'b') put 1 'a') put 3 'c' yield (t rid 2) keys" imports "eval ok: (1 (3 empty ‥) ‥)",
    evalOkWith "tree stayeth shallow under sorted puts" "bring often.tung bring class/functor/catamorphism.tung bring class/hath_manyhood.tung bring type/list.tung bring type/and.tung bring type/tree.tung let depth: [@α: *, @β: *, α tree β, ℕ] ≔ { leaf ^ 0, _ node _ _ l r ^ ((l depth) ⋎ (r depth)) + 1 } let t: ℕ tree ℕ ≔ (0 replicate 64) gather₁ (tree~empty ⸴ 0) {pair, _ ^ match pair { t ⸴ n ^ (t put n n) ⸴ (n + 1) }} $ project₀ yield (t depth) ⸴ (t manyhood)" imports "eval ok: (7 64 ⸴)",
    evalOkWith "table rid droppeth a key" "bring often.tung bring type/table.tung let table ≔ empty put 'a' +1 yield (table rid 'a') lookup 'a'" imports "eval ok: none",
    evalOkWith "set put keepeth values unique" "bring often.tung bring type/set.tung yield ((empty put +1) put +1) to_list" imports "eval ok: (+1 empty ‥)",
    evalOkWith "set from_list sorteth and removeth duplicates" "bring often.tung bring type/list.tung bring type/set.tung yield (+2 ‥ (+1 ‥ (+2 ‥ list~empty))) set~from_list $ to_list" imports "eval ok: (+1 (+2 empty ‥) ‥)",
    evalOkWith "set rid droppeth a value" "bring often.tung bring type/set.tung let values ≔ (empty put +1) put +2 yield (values rid +1) ∋ +1" imports "eval ok: nay",
    evalOkWith "set supremum keepeth unique values in order" "bring often.tung bring type/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +3 yield (left ⋎ right) to_list" imports "eval ok: (+1 (+2 (+3 empty ‥) ‥) ‥)",
    evalOkWith "set infimum keepeth shared values" "bring often.tung bring type/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +3 yield (left ⋏ right) to_list" imports "eval ok: (+2 empty ‥)",
    evalOkWith "set is ignoreth putting order" "bring often.tung bring type/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +1 yield left ≍ right" imports "eval ok: yea",
    evalOkWith "set partial order compareth enclosure" "bring often.tung bring type/set.tung let smaller ≔ empty put +1 let larger ≔ smaller put +2 yield (smaller ≤ larger) ⋏ (smaller < larger)" imports "eval ok: yea",
    evalOkWith "set enclosure rejecteth a proper superset" "bring often.tung bring type/set.tung let smaller ≔ empty put +1 let larger ≔ smaller put +2 yield larger ≤ smaller" imports "eval ok: nay",
    evalOkWith "powerset addition is symmetry difference" "bring often.tung bring type/powerset.tung let left:ℤ powerset ≔ { value ^ (value ≍ +1) ⋎ (value ≍ +2) } let right:ℤ powerset ≔ { value ^ (value ≍ +2) ⋎ (value ≍ +3) } yield ((left + right) ∋ +2)" imports "eval ok: nay",
    evalOkWith "powerset addition keepeth an unshared member" "bring often.tung bring type/powerset.tung let left:ℤ powerset ≔ { value ^ value ≍ +1 } let right:ℤ powerset ≔ { value ^ value ≍ +2 } yield ((left + right) ∋ +1)" imports "eval ok: yea",
    evalOkWith "powerset multiplication is intersection" "bring often.tung bring type/powerset.tung let left:ℤ powerset ≔ { value ^ (value ≍ +1) ⋎ (value ≍ +2) } let right:ℤ powerset ≔ { value ^ value ≍ +2 } yield ((left · right) ∋ +2)" imports "eval ok: yea",
    evalOkWith "powerset supremum is join" "bring often.tung bring type/powerset.tung let left:ℤ powerset ≔ { value ^ value ≍ +1 } let right:ℤ powerset ≔ { value ^ value ≍ +2 } yield (left ⋎ right) ∋ +2" imports "eval ok: yea",
    evalOkWith "powerset infimum is intersection" "bring often.tung bring type/powerset.tung let left:ℤ powerset ≔ { value ^ (value ≍ +1) ⋎ (value ≍ +2) } let right:ℤ powerset ≔ { value ^ value ≍ +2 } yield (left ⋏ right) ∋ +1" imports "eval ok: nay",
    evalOkWith "powerset complement excludeth a former member" "bring often.tung bring type/powerset.tung let one:ℤ powerset ≔ { value ^ value ≍ +1 } let outside:ℤ powerset ≔ one ∁ yield outside ∋ +1" imports "eval ok: nay",
    evalOkWith "powerset complement encloseth a former nonmember" "bring often.tung bring type/powerset.tung let one:ℤ powerset ≔ { value ^ value ≍ +1 } let outside:ℤ powerset ≔ one ∁ yield outside ∋ +2" imports "eval ok: yea",
    evalOkWith "powerset updates compose pointwise" "bring often.tung bring type/powerset.tung let left:ℤ powerset ≔ (powerset~empty put +1) put +2 let right:ℤ powerset ≔ powerset~empty put +2 yield >{⋏, left ∋ +1, ((left rid +1) ∋ +1) ∁, (left ∖ right) ∋ +1, ((left ∖ right) ∋ +2) ∁}" imports "eval ok: yea",
    evalOkWith "powerset negation leaveth a set whose sum with it is empty" "bring often.tung bring type/powerset.tung let values:ℤ powerset ≔ { value ^ value ≍ +1 } yield ((values + (values -)) ∋ +1)" imports "eval ok: nay",
    evalOkWith "powerset zero is empty" "bring often.tung bring type/powerset.tung let values:ℤ powerset ≔ zero yield values ∋ +7" imports "eval ok: nay",
    evalOkWith "powerset one is universal" "bring often.tung bring type/powerset.tung let values:ℤ powerset ≔ one yield values ∋ +7" imports "eval ok: yea",
    evalOkWith "set becometh a powerset" "bring often.tung bring type/set.tung bring type/powerset.tung let finite ≔ set~empty set~put +7 yield (finite to_powerset) ∋ +7" imports "eval ok: yea",
    evalOkWith "powerset lower wrapper useth intersection" "bring often.tung bring type/list.tung bring type/powerset.tung bring class/algebra/total/semigroup_multiply.tung bring class/functor/catamorphism.tung let one:ℤ powerset ≔ { value ^ value ≍ +1 } let both:ℤ powerset ≔ { value ^ (value ≍ +1) ⋎ (value ≍ +2) } let wrapped ≔ (one lower) ‥ ((both lower) ‥ list~empty) yield match wrapped …· { outcome lower ^ outcome ∋ +2 }" imports "eval ok: nay",
    evalOkWith "powerset upper wrapper useth join" "bring often.tung bring type/list.tung bring type/powerset.tung bring class/algebra/total/semigroup_multiply.tung bring class/functor/catamorphism.tung let one:ℤ powerset ≔ { value ^ value ≍ +1 } let two:ℤ powerset ≔ { value ^ value ≍ +2 } let wrapped ≔ (one upper) ‥ ((two upper) ‥ list~empty) yield match wrapped …· { outcome upper ^ outcome ∋ +2 }" imports "eval ok: yea",
    evalOkWith "empty powerset wrapper monoids select their bounds" "bring often.tung bring type/list.tung bring type/powerset.tung bring class/algebra/total/semigroup_multiply.tung bring class/functor/catamorphism.tung let meets:((ℤ powerset) _lower) list ≔ list~empty let joins:((ℤ powerset) _upper) list ≔ list~empty yield >{⋏, match meets …· { outcome lower ^ outcome ∋ +42 }, match joins …· { outcome upper ^ (outcome ∋ +42) ∁ }}" imports "eval ok: yea",
    evalOkWith "table functor mapeth values" "bring often.tung bring type/table.tung let table ≔ (empty put 'a' +1) put 'b' +2 yield (table map { x ^ x + +10 }) lookup 'a'" imports "eval ok: (+11 some)",
    evalOkWith "table sift keepeth matching values" "bring often.tung bring type/table.tung bring class/functor/hath_sift.tung let table ≔ (empty put 'a' +1) put 'b' +2 yield (table sift { x ^ +2 ≤ x }) lookup 'a'" imports "eval ok: none",
    evalOkWith "table joining preferreth right values" "bring often.tung bring type/table.tung let left ≔ empty put 'a' +1 let right ≔ empty put 'a' +2 yield (left join right) lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "table tweaking changeth an existing value" "bring often.tung bring type/table.tung let table ≔ empty put 'a' +1 yield (table tweak 'a' { x ^ x + +1 }) lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "string operations use unicode code points" "bring often.tung bring type/string/operation.tung yield ('aβ字' reverse_string) take_string 2" imports "eval ok: '字β'",
    evalOkWith "string manyhood counteth unicode code points" "bring often.tung bring type/string/operation.tung bring class/hath_manyhood.tung bring type/natural.tung yield ('aβ字' manyhood) to_ℤ" imports "eval ok: +3",
    evalOkWith "string split and join preserve empty fields" "bring often.tung bring type/string/operation.tung yield ('a,b,,c' split_string `,) join_with_string '.'" imports "eval ok: 'a.b..c'",
    evalOkWith "string words collapse whitespace runs" "bring often.tung bring type/string/operation.tung yield ' red\\tblue\\nred ' words_string $ join_with_string '.'" imports "eval ok: 'red.blue.red'",
    evalOkWith "typed paths join components" "bring often.tung bring type/path.tung yield (('root' path) path~join ('leaf' path)) to_string" imports "eval ok: 'root/leaf'",
    evalOkWith "time spans drive async sleep" "bring often.tung bring type/milliseconds.tung yield (0 milliseconds) sleep_for" imports "eval ok: only",
    evalOkWith "process captureth standard output" "bring often.tung bring effect/process.tung bring process/outcome.tung bring type/list.tung bring type/or.tung yield 'printf' process~run ('hello' ‥ empty) $ map { outcome ^ outcome map output }" imports "eval ok: ('hello' inject₁)",
    evalOkWith "arctan range is nonnegative" "bring _foreign.tung yield 0.0 arctan_float -1.0" imports "eval ok: 4.71238898038469",
    evalOkWith "fork and wait" "bring often.tung let work:ℤ effect ≔ +42 pure yield work fork $ bind wait" imports "eval ok: (+42 some)",
    evalOkWith "task result may be awaited repeatedly" "bring often.tung let work:ℤ effect ≔ +21 pure yield work fork $ bind { task ^ (task wait) lift₂ (task wait) { a, b ^ a lift₂ b + } }" imports "eval ok: (+42 some)",
    evalOkWith "task wait may time out" "bring often.tung let work:ℤ effect ≔ (200 sleep) then (+42 pure) yield work fork $ bind { task ^ task wait_for 0 }" imports "eval ok: none",
    evalOkWith "task wait_for returneth a finished value" "bring often.tung let work:ℤ effect ≔ +42 pure yield work fork $ bind { task ^ task wait_for 1000 }" imports "eval ok: (+42 some)",
    evalOkWith "a cancelled task yieldeth none" "bring often.tung let work:ℤ effect ≔ (1000 sleep) then (+42 pure) yield work fork $ bind { task ^ (task strike) then (task wait) }" imports "eval ok: none",
    evalOkWith "cpu-bound task remaineth cancellable" "bring often.tung fast turn:ℤ effect ≔ (only pure) bind { _ ^ turn } yield turn fork $ bind { task ^ (task strike) then (task wait) }" imports "eval ok: none",
    evalTypeErrWith "an opaque task cannot be eliminated as an empty family" "bring often.tung let unwrap:[value:ℤ task, ℤ] ≔ match value {} yield +0" imports,
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
        [ ("left.tung", "bring shared.tung show shared~identity"),
          ("right.tung", "bring shared.tung"),
          ("shared.tung", "show class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x }")
        ]
    distinctClassImports =
      Map.fromList
        [ ("left.tung", "bring often.tung show class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x + +1 }"),
          ("right.tung", "bring often.tung show class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x + +2 }")
        ]
    collidingMemberPrelude = "bring left.tung bring right.tung class both:[a:*, @:a first, @:a second, *] { let own:[a, ℤ] } "
    collidingMemberImports =
      Map.fromList
        [ ("left.tung", "show class first:[a:*, *] { let tag:[a, ℤ] }"),
          ("right.tung", "show class second:[a:*, *] { let tag:[a, ℤ] }")
        ]
    samePrefixInstanceImports = Map.fromList [("a.tung", identityInstance 1), ("a.extra.tung", identityInstance 10)]
    dottedDirectoryInstanceImports = Map.fromList [("pkg.one/identity.tung", identityInstance 1), ("pkg.two/identity.tung", identityInstance 10)]
    identityInstance :: Int -> String
    identityInstance increment = "bring often.tung show class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x + " ++ integerSource increment ++ " }"
    nominalTypeInstanceImports =
      Map.fromList
        [ ("common.tung", "show class hath_label:[a:*, *] { let label:[a, ℤ] }"),
          ("left.tung", "bring common.tung show type _token: * { token: _token } bizen:_token common~hath_label { let label: [_:] ≔ +1 } show let value:_token ≔ token"),
          ("right.tung", "bring common.tung show type _token: * { token: _token } bizen:_token common~hath_label { let label: [_:] ≔ +10 } show let value:_token ≔ token")
        ]
    transparentAliasInstanceImports =
      Map.fromList
        [ ("base.tung", "show type _token: * { token: _token } show class hath_label:[a:*, *] { let label:[a, ℤ] } bizen:_token hath_label { let label: [_:] ≔ +7 }"),
          ("alias.tung", "bring base.tung show let alias:* ≔ base~_token show let value:alias ≔ base~token")
        ]
    privateAliasInstanceImports =
      Map.singleton
        "opaque.tung"
        "type _secret: * { secret: _secret } show let public:* ≔ _secret show class hath_label:[a:*, *] { let label:[a, ℤ] } bizen:_secret hath_label { let label: [_:] ≔ +7 } show let value:public ≔ secret"
    reexportImports = Map.fromList [("base.tung", "show let value ≔ +7"), ("middle.tung", "bring base.tung show base~value")]
    identityImports = Map.fromList [("identity.tung", "show class hath_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ hath_identity { let identity: [x:] ≔ x }")]
    dataReexportImports =
      Map.fromList
        [ ("data_base.tung", "show type _box: [a:*, *] { box: [a, a _box] }"),
          ("data_middle.tung", "bring data_base.tung show data_base~box")
        ]
    constructorReexportImports =
      Map.fromList
        [ ("base.tung", "show type bit: * { off: bit }"),
          ("middle.tung", "bring base.tung show base~bit show base~off")
        ]
    -- a request names its answer type; the handler answereth each `ask` twice.
    freerPrelude =
      "bring often.tung bring type/freer.tung "
        ++ "type question: [a:*, *] { ask: ℤ question } "
        ++ "let ask_freer: question freer ℤ ≔ ask lift "
        ++ "let answer: [@ξ:*, request: ξ question, continue: [ξ, ℤ], ℤ] ≔ match request { ask ^ (+1 continue) + (+2 continue) } "
        ++ "let run: [program: question freer ℤ, ℤ] ≔ { value ^ value } gather answer program "

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
        ++ "let work:ℤ effect ≔ (600 sleep) then (+21 pure) "
        ++ "yield work fork $ bind { left ^ work fork $ bind { right ^ (left wait) then (right wait_for 100) } }"

systemArguments :: Map.Map String String -> Test
systemArguments imports = do
  actual <- Harness.evaluateSourceWithArgs ["north", "two words"] "bring often.tung bring effect/system.tung yield arguments" imports
  pure $ if actual == "eval ok: ('north' ('two words' empty ‥) ‥)" then Nothing else Just ("system arguments: " ++ actual)

systemEnvironment :: Map.Map String String -> Test
systemEnvironment imports = bracket (Environment.lookupEnv name) restore $ \_ -> do
  Environment.setEnv name "seen"
  actual <- Harness.evaluateSource ("bring often.tung bring effect/system.tung yield '" ++ name ++ "' environment") imports
  pure $ if actual == "eval ok: ('seen' some)" then Nothing else Just ("system environment: " ++ actual)
  where
    name = "TUNG_TEST_ENVIRONMENT"
    restore Nothing = Environment.unsetEnv name
    restore (Just value) = Environment.setEnv name value

unixTime :: Map.Map String String -> Test
unixTime imports = do
  before <- floor <$> getPOSIXTime
  actual <- Harness.evaluateSource "bring often.tung bring effect/clock.tung yield unix_time" imports
  after <- floor <$> getPOSIXTime
  pure $ case stripPrefix "eval ok: +" actual >>= readMaybe of
    Just value | value >= (before :: Int) && value <= after -> Nothing
    _ -> Just ("unix time is in the host clock range: got " ++ actual)

evalCase :: Map.Map String String -> (String, String, String) -> Test
evalCase imports (name, source, expected) = evalOkWith name source imports expected

typeErrorCase :: Map.Map String String -> (String, String) -> Test
typeErrorCase imports (name, source) = evalTypeErrWith name source imports

boolData, optionData, rowData, effectPrelude, sleepBinding :: String
boolData = "type 𝟚: * { yea: 𝟚, nay: 𝟚 } "
optionData = "type optional: [a:*, *] { none: a optional, some: [a, a optional] } "
rowData = boolData ++ "type row: * { stop: row, more: [𝟚, row, row] } let ones: [n: ℕ, row] ≔ match n { 0 ^ stop, k next ^ yea more (k ones) } "
effectPrelude = "let pure:[@a:*, a, a effect] ≔ 'effect_pure' foreign let bind:[@a:*, @b:*, a effect, [a, b effect], b effect] ≔ 'effect_bind' foreign "
sleepBinding = "let sleep:[ℕ, 𝟙 effect] ≔ 'sleep' foreign "
