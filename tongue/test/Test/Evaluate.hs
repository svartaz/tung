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
import Tung

group :: IO Group
group = do
  imports <- readLibraryImports "." >>= either fail pure
  Harness.group "evaluate" (map (evalCase imports) deterministic ++ map (typeErrorCase imports) typeErrors ++ importedCases imports)

deterministic :: [(String, String, String)]
deterministic =
  [ ("ℤ arithmetic", "use ground.tung yield (+1 + +2) × +3", "eval ok: +9"),
    ("declared type parameters eke no runtime arguments", "let constant:[@a:*, @b:*, x:a, _:b, a] ≔ x yield +1 constant 'x'", "eval ok: +1"),
    ("explicit type inputs are erased beside worth inputs", "let f:[@a:*, @b:*, x:a, _:b, a] ≔ x yield +1 f @ℤ @text 'x'", "eval ok: +1"),
    ("instance method type inputs are erased", "let id:[@a:*, x:a, a] ≔ x flock owner:[a:*, *] { let copy:[@b:*, a, b, b] } bizen:ℤ owner { let copy:[@c:*, _:ℤ, x:c, c] ≔ x id @c } yield +1 copy 'x'", "eval ok: 'x'"),
    ("unused type inputs requireth no runtime argument", "let worth:[@a:*, ℤ] ≔ +7 yield worth @text", "eval ok: +7"),
    ("higher-rank argument is erased and instantiated twice", "let both:[f:[@a:*, a, a], r{tale:ℤ, word:text}] ≔ r{tale≔+1 f, word≔'x' f} let id: [@a:*, x: a, a] ≔ x yield (id both).tale", "eval ok: +1"),
    ("polymorphic return needs no runtime type arguments", "let make:[_:ℤ, [@a:*, a, a]] ≔ {x ^ x} yield 'yes' (+1 make)", "eval ok: 'yes'"),
    ("left-associated sequence", "use ground.tung yield <{-, +10, +3, +2}", "eval ok: +5"),
    ("right-associated sequence", "use ground.tung yield >{-, +10, +3, +2}", "eval ok: +9"),
    ("nested brace forms share type and expression boundaries", "use ground.tung let record:r{callback:[ℤ, ℤ], nested:r{worth:ℤ}} ≔ r{callback≔{x ^ <{+, x, +1}}, nested≔r{worth≔+2}} yield record.nested.worth record.callback", "eval ok: +3"),
    ("term type ascription is erased before evaluation", "use ground.tung yield (+1 + +2: ℤ)", "eval ok: +3"),
    ("ascribed anonymous function remaineth recursive", "use ground.tung let factorial ≔ ({ 0 ^ 1, n heir ^ (n heir) × (n factorial) }: [ℕ, ℕ]) yield 5 factorial", "eval ok: 120"),
    ("ℤ arithmetic is arbitrary precision", "use ground.tung yield +999999999999999999999999999999 + +1", "eval ok: +1000000000000000000000000000000"),
    ("fremmed key selecteth a host function independently of the let name", "let plus:[ℤ, ℤ, ℤ] ≔ 'eke_integer' fremmed yield +1 plus +2", "eval ok: +3"),
    ("unicode text", "yield 'λ字'", "eval ok: 'λ字'"),
    ("unicode control rendering useth decimal terminator", "yield `\\1;", "eval ok: `\\1;"),
    ("float arithmetic", "use ground.tung yield 0.5 + 0.25", "eval ok: 0.75"),
    ("text becometh a float", "use ground.tung use ilk/maybe.tung let parsed:float maybe ≔ '0.5' from_text yield parsed", "eval ok: (0.5 some)"),
    ("unparsable text yieldeth none", "use ground.tung use ilk/maybe.tung let parsed:float maybe ≔ 'not a float' from_text yield parsed", "eval ok: none"),
    ("division by zero yieldeth none", "use ground.tung " ++ optionData ++ "yield +1 % +0", "eval ok: none"),
    ("float division useth the division sign", "use ground.tung yield 6.0 ÷ 4.0", "eval ok: 1.5"),
    ("float division by zero followeth ieee", "use ground.tung yield 1.0 ÷ 0.0", "eval ok: Infinity"),
    ("non-finite float floors yield none", "use _foreign.tung yield r{infinite ≔ (1.0 deal_float 0.0) ⌊, nan ≔ (0.0 deal_float 0.0) ⌊}", "eval ok: r{infinite ≔ none, nan ≔ none}"),
    ("float is ignoreth literal spelling", "use ground.tung ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } yield 1.0 ≍ 1.00", "eval ok: yea"),
    ("bracketed natural constructors construct and match", "ilk nat: * { zero: nat, suc: [nat, nat] } yield match zero suc { x suc ^ +1, zero ^ +0 }", "eval ok: +1"),
    ("bracketed list constructors preserve native ABI", "ilk list: [a:*, *] { empty: a list, ‥: [a, a list, a list] } yield match (+1 ‥ empty) { first ‥ _ ^ first, empty ^ +0 }", "eval ok: +1"),
    ("indexed constructor match useth its refined payload", indexedUnpackSource ++ "yield (+3 integer) unpack", "eval ok: +3"),
    ("indexed constructor match useth its other branch", indexedUnpackSource ++ "yield ('hi' textual) unpack", "eval ok: 'hi'"),
    ("float ordering is numeric", "use ground.tung ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } yield 2.0 ≤ 10.0", "eval ok: yea"),
    ("curried half application", "use ground.tung let hath_+: [a: ℤ, b: ℤ, ℤ] ≔ a + b let eke_one ≔ +1 hath_+ yield +2 eke_one", "eval ok: +3"),
    ("three curried arguments", "use ground.tung let hath_+: [a: ℤ, b: ℤ, c: ℤ, ℤ] ≔ (a + b) + c yield +1 hath_+ +2 +3", "eval ok: +6"),
    ("local recursive function", "use ground.tung ilk nat: * { zero: nat, suc: [nat, nat] } let count ≔ (let loop: [nat, ℤ] ≔ { zero ^ +0, n suc ^ +1 + (n loop) } yield loop) yield ((zero suc) suc) count", "eval ok: +2"),
    ("recursive calls retain inferred evidence", "use ground.tung flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +1 } let loop: [ℕ, ℤ, ℤ] ≔ { 0, x ^ x sameness, n heir, x ^ n loop x } yield 2 loop +3", "eval ok: +4"),
    ("recursive evidence surviveth a nested polymorphic binding", "use ground.tung flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +1 } let loop: [ℕ, ℤ, ℤ] ≔ { 0, x ^ x sameness, n heir, x ^ (let echo: [y:] ≔ y sameness yield (n loop x) echo) } yield 2 loop +3", "eval ok: +6"),
    ("second-position function header", "use ground.tung let hath_+: [a: ℤ, b: ℤ, ℤ] ≔ a + b yield +1 hath_+ +2", "eval ok: +3"),
    ("dollar function segment", "use ground.tung let f: [x: ℤ, ℤ] ≔ x + +1 let h: [x: ℤ, y: ℤ, z: ℤ, ℤ] ≔ (x + y) × z yield +1 f $h +2 +3", "eval ok: +12"),
    ("lexical closure", "let x ≔ +1 let f: [_: ℤ, ℤ] ≔ x yield (let x ≔ +2 yield +0 f)", "eval ok: +1"),
    ("sequential shadowing preserveth each preceding local", "use ground.tung yield (let worth ≔ +1 let worth ≔ worth + +1 let worth ≔ worth + +1 yield worth)", "eval ok: +3"),
    ("nested same-text pattern binders remain distinct", "use ground.tung yield match +1 { worth ^ (match +2 { worth ^ worth }) + worth }", "eval ok: +3"),
    ("multi-scrutinee match", boolData ++ "yield match yea, nay { yea, yea ^ +1, yea, nay ^ +2, nay, yea ^ +3, nay, nay ^ +4 }", "eval ok: +2"),
    ("nested constructor match", boolData ++ optionData ++ "yield match nay some { yea some ^ +1, nay some ^ +2, none ^ +0 }", "eval ok: +2"),
    ("first matching arm winneth", boolData ++ "yield match yea { yea ^ +1, _ ^ +2 }", "eval ok: +1"),
    ("ℤ match patterns", "yield match -1 { +0 ^ +10, -1 ^ +20, _ ^ +30 }", "eval ok: +20"),
    ("ℤ patterns fall through", "yield match +2 { +0 ^ +10, +1 ^ +20, _ ^ +30 }", "eval ok: +30"),
    ("alternative patterns share one result", "yield match +2 { +0; +1; +2 ^ +7, _ ^ +0 }", "eval ok: +7"),
    ("alternative constructor patterns share bindings", "ilk choice: [a:*, *] { left: [a, a choice], right: [a, a choice] } yield match +2 right { x left; x right ^ x }", "eval ok: +2"),
    ("ℤ function patterns", "let classify:[ℤ, ℤ] ≔ { +0 ^ +10, +1 ^ +20, _ ^ +30 } yield +1 classify", "eval ok: +20"),
    ("text match patterns", "yield match 'yes' { 'yes' ^ +1, _ ^ +0 }", "eval ok: +1"),
    ("text patterns fall through", "yield match 'no' { 'yes' ^ +1, _ ^ +0 }", "eval ok: +0"),
    ("text function patterns", "let classify:[text, ℤ] ≔ { 'yes' ^ +1, _ ^ +0 } yield 'yes' classify", "eval ok: +1"),
    ("unchosen arm is not evaluated", boolData ++ "yield match yea { yea ^ +1, nay ^ +0 (sorry:[ℤ, ℤ]) }", "eval ok: +1"),
    ("record update", "let person ≔ r{name ≔ 'n', age ≔ +1} yield r{≔ person, age ≔ +2}", "eval ok: r{age ≔ +2, name ≔ 'n'}"),
    ("record access", "let person ≔ r{name ≔ 'n', age ≔ +1} yield person.age", "eval ok: +1"),
    ("chained record access", "let person ≔ r{address ≔ r{city ≔ 'kyoto'}} yield person.address.city", "eval ok: 'kyoto'"),
    ("record removal", "let person ≔ r{name ≔ 'n', age ≔ +1} yield r{≔ person, - age}", "eval ok: r{name ≔ 'n'}"),
    ("fremmed arity followeth a transparent alias", "let binary:* ≔ [ℤ, ℤ, ℤ] let plus:binary ≔ 'eke_integer' fremmed yield +1 plus +2", "eval ok: +3"),
    ("an unused top-level definition is not computed", "let missing:ℤ ≔ sorry yield +1", "eval ok: +1"),
    ("a demanded top-level definition is computed", "let missing:ℤ ≔ sorry yield missing", "eval error: reached sorry"),
    ("an unused argument is not computed", "let ignore:[_:ℤ, ℤ] ≔ +7 yield (+1 (sorry:[ℤ, ℤ])) ignore", "eval ok: +7"),
    ("an unused local definition is not computed", "yield (let unused:ℤ ≔ +1 (sorry:[ℤ, ℤ]) yield +7)", "eval ok: +7"),
    ("record projection computeth only the selected field", "yield r{kept ≔ +7, unused ≔ +1 (sorry:[ℤ, ℤ])}.kept", "eval ok: +7"),
    ("selfcalling under a match computeth only the chosen branch", rowData ++ "let flips: [r: row, inside: 𝟚, ℕ] ≔ match r { stop ^ 0, _ more rest ^ match inside { yea ^ (rest flips nay) heir, nay ^ rest flips yea } } yield (64 ones) flips yea", "eval ok: 32"),
    ("a user function computeth only its selected recursive input", recursiveChoiceSource, "eval ok: +8"),
    ("an unused constructor field and recursive hypothesis are not computed", rowData ++ "let first: [r: row, 𝟚] ≔ match r { stop ^ nay, c more _ ^ c } yield (yea more (0 (sorry:[ℕ, row]))) first", "eval ok: yea"),
    ("reaching an orsetting is a runtime error", boolData ++ "orsetting missing: 𝟚 yield missing", "eval error: reached orsetting 'missing'"),
    ("a yielded worth is computed in full", "yield r{kept ≔ +1, missing ≔ (sorry: ℤ)}", "eval error: reached sorry"),
    ("a yielded deed is performed", "use ilk/one.tung " ++ sleepBinding ++ "yield 0 sleep", "eval ok: only"),
    ("deed_bind passeth a result on", deedPrelude ++ "let plus:[ℤ, ℤ, ℤ] ≔ 'eke_integer' fremmed yield (+2 sheer) bind { x ^ (x plus +1) sheer }", "eval ok: +3"),
    ("a deed is a worth until performed", deedPrelude ++ "let action:ℤ deed ≔ +1 sheer yield (let unused ≔ action yield +2)", "eval ok: +2"),
    ("flock laws are erased", "flock hath_sameness:[a:*, *] { let sameness:[a, a] let rule:[x: a, (x sameness) = x] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x let rule ≔ sorry } yield +2 sameness", "eval ok: +2"),
    ("result-only member useth expected type", "flock hath_origin:[a:*, *] { let origin:a } bizen:ℤ hath_origin { let origin ≔ +7 } let worth:ℤ ≔ origin yield worth", "eval ok: +7"),
    ("different instances dispatch by inferred type", "flock hath_label:[a:*, *] { let label:[a, text] } bizen:ℤ hath_label { let label: [_:] ≔ 'ℤ' } bizen:text hath_label { let label: [_:] ≔ 'text' } yield 'x' label", "eval ok: 'text'"),
    ("constraint function receiveth its caller dictionary", "flock hath_label:[a:*, *] { let label:[a, text] } bizen:ℤ hath_label { let label: [_:] ≔ 'ℤ' } bizen:text hath_label { let label: [_:] ≔ 'text' } let labelled:[@a:*, @:a hath_label, x: a, text] ≔ x label yield +1 labelled", "eval ok: 'ℤ'"),
    ("child dictionary useth a direct parent instance", "flock hath_parent:[a:*, *] { let parent:[a, a] } flock hath_child:[a:*, @:a hath_parent, *] { let child:[a, a] } bizen:ℤ hath_parent { let parent: [x:] ≔ x } bizen:ℤ hath_child { let child: [x:] ≔ x parent } yield +4 child", "eval ok: +4"),
    ("repeated bizen calls retain a preceding private worth", "use ground.tung flock hath_bump:[a:*, *] { let bump:[a, a] } let offset ≔ +2 bizen:ℤ hath_bump { let bump: [x:] ≔ x + offset } yield (+1 bump) + (+2 bump)", "eval ok: +7"),
    ("bizen may precede its resolved flock declaration", "bizen:ℤ hath_sameness { let sameness: [x:] ≔ x } flock hath_sameness:[a:*, *] { let sameness:[a, a] } yield +3 sameness", "eval ok: +3"),
    ("bizen constraint remaineth an external dictionary", "use ground.tung flock hath_combine:[a:*, *] { let combine:[a, a, a] } bizen:ℤ hath_combine { let combine: [x:, y:] ≔ x + y } ilk _box: [a:*, *] { box: [a, a _box] } bizen:[@a:*, @:a hath_combine, (a _box) hath_combine] { let combine: [x box:, y box:] ≔ (x combine y) box } yield (+1 box) combine (+2 box)", "eval ok: (+3 box)")
  ]

indexedUnpackSource :: String
indexedUnpackSource =
  "ilk tag: [a:*, *] { integer: [ℤ, ℤ tag], textual: [text, text tag] } "
    ++ "let unpack:[@a:*, x:a tag, a] ≔ match x { n integer ^ n, t textual ^ t } "

-- both inputs recurse; the discarded path faileth at its base.
recursiveChoiceSource :: String
recursiveChoiceSource =
  rowData
    ++ """
       let hath_+:[ℤ, ℤ, ℤ] ≔ 'eke_integer' fremmed
       let choose:[flag:𝟚, yes:ℤ, no:ℤ, ℤ] ≔ match flag { yea ^ yes, nay ^ no }
       let count:[r:row, flag:𝟚, ℤ] ≔ match r {
         stop ^ match flag { yea ^ +0, nay ^ +0 (sorry:[ℤ, ℤ]) },
         _ more rest ^ flag choose (+1 hath_+ (rest count yea)) (rest count nay)
       }
       yield (8 ones) count yea

       """

typeErrors :: [(String, String)]
typeErrors =
  [ ("unknown worth", "yield missing"),
    ("captured alias mismatch is rejected before evaluation", "let bad: [x:] ≔ (let y ≔ x let tale:ℤ ≔ y yield tale + +1) yield 'oops' bad"),
    ("non-function application", "yield +1 +2"),
    ("constructor overapplication", "ilk _box: [a:*, *] { box: [a, a _box] } yield +1 box +2"),
    ("missing record field", "let worth ≔ r{x ≔ +1} yield worth.y"),
    ("unknown record removal", "let person ≔ r{name ≔ 'n'} yield r{≔ person, - age}"),
    ("update of non-record", "yield r{≔ +1, field ≔ +2}"),
    ("non-exhaustive match", boolData ++ "yield match nay { yea ^ +1 }"),
    ("a deed is not its result", "use ground.tung " ++ deedPrelude ++ "yield (+1 sheer) + +1")
  ]

importedCases :: Map.Map String String -> [Test]
importedCases imports =
  [ evalOkWith
      "a local term and an imported constructor retain distinct runtime identities"
      "use token.tung let box ≔ +7 yield r{constructor ≔ token~box, local ≔ box}"
      (Map.singleton "token.tung" "show ilk token: * { box: token }")
      "eval ok: r{constructor ≔ box, local ≔ +7}",
    evalOkWith "imported call" "use ground.tung use file.tung yield +2 inc" (Map.insert "file.tung" "use ground.tung show let inc: [x:] ≔ x + +1" imports) "eval ok: +3",
    evalOkWith "a use declaration is initialised before a preceding let" "let answer ≔ dep~worth use dep.tung yield answer" (Map.insert "dep.tung" "show let worth ≔ +7" imports) "eval ok: +7",
    evalOkWith "a local and its imported predecessor retain distinct identities" "use ground.tung use source.tung let worth ≔ source~worth + +1 yield worth + source~worth" (Map.insert "source.tung" "show let worth ≔ +2" imports) "eval ok: +5",
    evalTypeErrWith "a local worth shadoweth an imported constructor in patterns" "use ilk/two.tung let yea:𝟚 ≔ two~yea yield match yea { yea ^ +1, nay ^ +0 }" imports,
    evalOkWith "a qualified pattern still reacheth a shadowed constructor" "use ilk/two.tung let yea ≔ +0 yield match two~yea { two~yea ^ +1, nay ^ +0 }" imports "eval ok: +1",
    evalOkWith "default use alias worketh for values, classes, and constructor patterns" "use ilk/item.tung let worth:item~_item ≔ item~empty yield match (worth item~sameness) { item~item ^ +1 }" (Map.insert "ilk/item.tung" "show ilk _item: * { item: _item } show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:_item hath_sameness { let sameness: [x:] ≔ x } show let empty:_item ≔ item" imports) "eval ok: +1",
    evalOkWith "derived flock operations" "use ground.tung yield (+1 < +2) ∧ (+1 ≭ +2)" imports "eval ok: yea",
    evalOkWith "false implieth false" "use ground.tung yield nay ≤ nay" imports "eval ok: yea",
    evalOkWith "true doth not imply false" "use ground.tung yield yea ≤ nay" imports "eval ok: nay",
    evalOkWith "heir patterns recurse on a natural" "use ground.tung let double: [n: ℕ, ℕ] ≔ match n { 0 ^ 0, m heir ^ (m double) + 2 } yield 3 double" imports "eval ok: 6",
    evalOkWith "heir addeth one to a natural" "yield (2 heir) heir" imports "eval ok: 4",
    evalOkWith "euclidean division returneth quotient and remainder for a undernaught divisor" "use ground.tung use ilk/product.tung yield +5 % -3" imports "eval ok: ((-1 +2 both) some)",
    evalOkWith "euclidean division returneth quotient and remainder for a undernaught dividend" "use ground.tung use ilk/product.tung yield -5 % +3" imports "eval ok: ((-2 +1 both) some)",
    evalOkWith "euclidean quotient and remainder reconstruct the dividend" "use ground.tung use ilk/maybe.tung use ilk/product.tung let dividend ≔ -5 let divisor ≔ -3 yield match dividend % divisor { (quotient both rest) some ^ (quotient × divisor) + rest, none ^ +0 }" imports "eval ok: -5",
    evalOkWith "euclidean division faileth at zero" "use ground.tung yield +1 % +0" imports "eval ok: none",
    evalOkWith "three-way comparison distinguishes each result" "use ground.tung use ilk/product.tung yield (+0 compare +1) both (+1 compare +1) $both (+2 compare +1)" imports "eval ok: ((fore mid both) aft both)",
    evalOkWith "clamp keepeth a worth inside its bounds" "use ground.tung yield +0 clamp +10 +12" imports "eval ok: +10",
    evalOkWith "qualified duplicate values" "use ground.tung use left.tung use right.tung yield left~foo + right~foo" (duplicateImports <> imports) "eval ok: +3",
    evalOkWith "shared diamond import" "use ground.tung use left.tung use right.tung yield left~left + right~right" (diamondImports <> imports) "eval ok: +5",
    evalOkWith "diamond import keepeth one bizen sameness" "use left.tung use right.tung yield +3 left~sameness" (instanceDiamondImports <> imports) "eval ok: +3",
    evalOkWith "qualified classes from different modules stay distinct" "use ground.tung use left.tung use right.tung yield +3 left~sameness" (distinctClassImports <> imports) "eval ok: +4",
    evalOkWith "inherited same-named members select the requested class" (collidingMemberPrelude ++ "bizen:ℤ first { let tag: [_:] ≔ +1 } bizen:ℤ second { let tag: [_:] ≔ +2 } bizen:ℤ both { let own: [_:] ≔ +3 } let result:[@a:*, @:a both, x: a, ℤ] ≔ x right~tag yield +1 result") (collidingMemberImports <> imports) "eval ok: +2",
    evalOkWith "a child member override doth not replace a sibling flock member" ("use ground.tung " ++ collidingMemberPrelude ++ "bizen:ℤ second { let tag: [_:] ≔ +2 } bizen:ℤ both { let tag: [_:] ≔ +10 let own: [_:] ≔ +3 } let result:[@a:*, @:a both, x: a, ℤ] ≔ (x left~tag) + (x right~tag) yield +1 result") (collidingMemberImports <> imports) "eval ok: +12",
    evalOkWith "instances in extension-sharing paths stay distinct" "use ground.tung use a.tung one use a.extra.tung two yield (+1 one~sameness) + (+1 two~sameness)" (samePrefixInstanceImports <> imports) "eval ok: +13",
    evalOkWith "instances beneath dotted directories stay distinct" "use ground.tung use pkg.one/sameness.tung one use pkg.two/sameness.tung two yield (+1 one~sameness) + (+1 two~sameness)" (dottedDirectoryInstanceImports <> imports) "eval ok: +13",
    evalOkWith "same-spelled imported data types dispatch through distinct instances" "use ground.tung use common.tung use left.tung use right.tung yield (left~worth common~label) + (right~worth common~label)" (nominalTypeInstanceImports <> imports) "eval ok: +11",
    evalOkWith "an imported transparent alias useth its underlying instance" "use base.tung use alias.tung yield alias~worth base~label" (transparentAliasInstanceImports <> imports) "eval ok: +7",
    evalOkWith "an exported alias retaineth its private nominal instance" "use opaque.tung opaque yield opaque~worth opaque~label" (privateAliasInstanceImports <> imports) "eval ok: +7",
    evalOkWith "a local flock and bizen shadow an imported namesake" "use ground.tung use left.tung flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +2 } yield (+1 sameness) + (+1 left~sameness)" (distinctClassImports <> imports) "eval ok: +5",
    evalTypeErrWith "local evidence cannot satisfy an imported namesake class" "use left.tung flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x } let imported_use:[@a:*, @:a left~hath_sameness, x: a, a] ≔ x left~sameness let local_use:[@a:*, @:a hath_sameness, x: a, a] ≔ x imported_use yield +1 local_use" (distinctClassImports <> imports),
    evalOkWith "worth survives a named re-export" "use middle.tung yield worth" (reexportImports <> imports) "eval ok: +7",
    evalOkWith "qualified re-export outranketh a shadowing local" "use ground.tung use middle.tung let worth ≔ +3 yield middle~worth + worth" (reexportImports <> imports) "eval ok: +10",
    evalOkWith "flock bizen survives an import" "use sameness.tung yield +3 sameness" (identityImports <> imports) "eval ok: +3",
    evalOkWith "specific bizen outranketh a blanket instance" "use ground.tung flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:[@a:*, a hath_sameness] { let sameness: [x:] ≔ x } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +1 } yield +1 sameness" imports "eval ok: +2",
    evalOkWith "data constructor survives a named re-export" "use data_middle.tung yield +4 box" (dataReexportImports <> imports) "eval ok: (+4 box)",
    evalOkWith "constructor sameness survives a different re-export path" "use data_base.tung use data_middle.tung yield match +4 data_middle~box { x data_base~box ^ x }" (dataReexportImports <> imports) "eval ok: +4",
    evalOkWith "constructor pattern surviveth a middle-module re-export" "use middle.tung yield match middle~off { middle~off ^ +1 }" (constructorReexportImports <> imports) "eval ok: +1",
    evalOkWith "qualified constructor pattern useth import alias" "use alias.tung yield match +4 alias~box { x alias~box ^ x }" (Map.insert "alias.tung" "show ilk _box: [a:*, *] { box: [a, a _box] }" imports) "eval ok: +4",
    evalOkWith "qualified global remaineth distinct from record access" "use public.tung let public ≔ r{visible ≔ +9} yield public~visible" (Map.insert "public.tung" "show let visible ≔ +7" imports) "eval ok: +7",
    evalTypeErrWith "private qualified worth is rejected before runtime" "use private.tung yield private~hidden" (Map.fromList [("private.tung", "let hidden ≔ +1")]),
    evalOkWith "text and unicode-list round trip" "use ground.tung yield 'λ😀' text_to_list $ list_to_text" imports "eval ok: 'λ😀'",
    evalOkWith "text converteth to a unicode list" "use ground.tung yield 'λ😀' text_to_list" imports "eval ok: (`λ (`😀 empty ‥) ‥)",
    evalOkWith "unicode converteth to its scalar ℕ" "use ground.tung yield `😀 unicode_to_natural" imports "eval ok: 128512",
    evalOkWith "scalar ℕ converteth to unicode" "use ground.tung yield 128512 natural_to_unicode" imports "eval ok: (`😀 some)",
    evalOkWith "surrogate ℕ cannot become unicode" "use ground.tung yield 55296 natural_to_unicode" imports "eval ok: none",
    evalOkWith "out-of-range ℕ cannot become unicode" "use ground.tung yield 1114112 natural_to_unicode" imports "eval ok: none",
    evalOkWith "text behead exposeth one code point" "use ground.tung use ilk/list.tung use ilk/maybe.tung use ilk/product.tung use flock/algebra/whole/hath_magma.tung yield match 'λ字' behead_text { (c both rest) maybe~some ^ ((c ‥ empty) list_to_text) · rest, maybe~none ^ '' }" imports "eval ok: 'λ字'",
    evalOkWith "empty text hath no head" "use ground.tung use ilk/maybe.tung yield match '' behead_text { none ^ +1, _ some ^ +0 }" imports "eval ok: +1",
    evalOkWith "generic text fold" "use ground.tung use ilk/list.tung use flock/functor/catamorphism.tung yield ('north' ‥ ('南' ‥ empty)) …*" imports "eval ok: 'north南'",
    evalOkWith "text classes dispatch" "use ground.tung use flock/algebra/whole/hath_magma.tung yield (('a' · 'β') ≍ 'aβ') ∧ ('a' ≤ 'b')" imports "eval ok: yea",
    evalOkWith "unicode classes dispatch" "use ground.tung yield (`a ≍ `a) ∧ (`a ≤ `b)" imports "eval ok: yea",
    evalOkWith "imported bizen doth not shadow native ℤ order" "use ilk/list.tung yield +0 till +3" imports "eval ok: (+0 (+1 (+2 empty ‥) ‥) ‥)",
    evalOkWith "list warp pipeline keepeth the list functor" "use ground.tung use ilk/list.tung yield +0 till +3 $ warp { x ^ x + +1 } $ warp to_text" imports "eval ok: ('1' ('2' ('3' empty ‥) ‥) ‥)",
    evalOkWith "list atfold calleth its separate warp instance" "use ground.tung use ilk/list.tung let values ≔ +1 ‥ (+2 ‥ empty) let functions ≔ { x ^ x + +10 } ‥ ({ x ^ x × +2 } ‥ empty) yield values atfold functions" imports "eval ok: (+11 (+12 (+2 (+4 empty ‥) ‥) ‥) ‥)",
    evalOkWith "list traversal sequences maybe values" "use ground.tung use ilk/list.tung use ilk/maybe.tung use flock/functor/hath_throughwend.tung yield (+1 ‥ (+2 ‥ empty)) throughwend { x ^ x maybe~some }" imports "eval ok: ((+1 (+2 empty ‥) ‥) some)",
    evalOkWith "fold_warp combineth mapped list values" "use ground.tung use ilk/list.tung use flock/functor/catamorphism.tung yield (+0 till +3) gather_warp to_text" imports "eval ok: '012'",
    evalOkWith "bounded conjunction folds values" "use ground.tung use ilk/list.tung use flock/functor/catamorphism.tung yield yea ‥ (nay ‥ empty) $ …∧" imports "eval ok: nay",
    evalOkWith "bounded disjunction folds values" "use ground.tung use ilk/list.tung use flock/functor/catamorphism.tung yield nay ‥ (yea ‥ empty) $ …∨" imports "eval ok: yea",
    evalOkWith "empty bounded conjunction useth the upper endpoint" "use ground.tung use ilk/list.tung use flock/functor/catamorphism.tung let values:𝟚 list ≔ empty yield values …∧" imports "eval ok: yea",
    evalOkWith "empty bounded disjunction useth the lower endpoint" "use ground.tung use ilk/list.tung use flock/functor/catamorphism.tung let values:𝟚 list ≔ empty yield values …∨" imports "eval ok: nay",
    evalOkWith "boolean complement negateth" "use ground.tung yield yea ¬" imports "eval ok: nay",
    evalTypeErrWith "bounded lattice need not have a complement" "use ground.tung yield mid ¬" imports,
    evalOkWith "ℤ lattice chooseth the lesser worth" "use ground.tung yield +3 ∧ +2" imports "eval ok: +2",
    evalOkWith "whole order supplieth a distributive lattice" "use ground.tung let distribute:[@a:*, @:a lattice_distributive, x: a, y: a, z: a, a] ≔ x ∧ (y ∨ z) yield +3 distribute +2 +4" imports "eval ok: +3",
    evalOkWith "non-total powerset lattice joineth predicates" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/functor/catamorphism.tung let one:ℤ powerset ≔ { x ^ x ≍ +1 } let two:ℤ powerset ≔ { x ^ x ≍ +2 } let joined ≔ one ‥ (two ‥ list~empty) $ …∨ yield joined ∋ +2" imports "eval ok: yea",
    evalOkWith "empty powerset meet yieldeth the universal set" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/functor/catamorphism.tung let values:(ℤ powerset) list ≔ list~empty let all ≔ values …∧ yield all ∋ +42" imports "eval ok: yea",
    evalOkWith "pattern binders do not become constructor patterns" "use ground.tung use ilk/list.tung ilk bit: * { off: bit } yield +0 till +3 $ warp { _ ^ off } $ warp { _ ^ +1 }" imports "eval ok: (+1 (+1 (+1 empty ‥) ‥) ‥)",
    evalOkWith "control branch suspends actions" "use ground.tung yield nay branch { _ ^ +1 } { _ ^ +2 }" imports "eval ok: +2",
    evalOkWith "maybe maybe mapeth present worth" "use ground.tung use ilk/maybe.tung yield (+3 some) handle +0 { x ^ x + +1 }" imports "eval ok: +4",
    evalOkWith "sum either consumeth selected side" "use ground.tung use ilk/sum.tung yield (+2 incast₁) either { x ^ x + +1 } { y ^ y × +3 }" imports "eval ok: +6",
    evalOkWith "sum biwarp mapeth the selected side" "use ground.tung use ilk/sum.tung let worth:ℤ ∑ text ≔ +2 incast₀ yield match (worth biwarp { x ^ x + +1 } { text ^ text }) { x incast₀ ^ x, _ incast₁ ^ +0 }" imports "eval ok: +3",
    evalOkWith "sum functor mapeth the right side" "use ground.tung use ilk/sum.tung let worth:text ∑ ℤ ≔ +2 incast₁ yield match (worth warp { x ^ x + +1 }) { _ incast₀ ^ +0, x incast₁ ^ x }" imports "eval ok: +3",
    evalOkWith "sum atfoldsome applieth the right side" "use ground.tung use ilk/sum.tung let worth:text ∑ ℤ ≔ +2 incast₁ let f:text ∑ [ℤ, ℤ] ≔ { x ^ x + +3 } incast₁ yield match worth atfold f { _ incast₀ ^ +0, x incast₁ ^ x }" imports "eval ok: +5",
    evalOkWith "sum monad preserveth a left worth" "use ground.tung use ilk/sum.tung let worth:text ∑ ℤ ≔ 'left' incast₀ yield match (worth bind { x ^ (x + +1) incast₁ }) { message incast₀ ^ message, x incast₁ ^ x to_text }" imports "eval ok: 'left'",
    evalOkWith "sum catamorphism foldeth the right side" "use ground.tung use ilk/sum.tung use flock/functor/catamorphism.tung let worth:text ∑ ℤ ≔ +3 incast₁ yield worth gather₁ +1 +" imports "eval ok: +4",
    evalOkWith "sum traversal preserveth its side" "use ground.tung use ilk/sum.tung use ilk/maybe.tung use flock/functor/hath_throughwend.tung let worth:text ∑ ℤ ≔ +3 incast₁ yield worth throughwend { x ^ (x + +1) some }" imports "eval ok: ((+4 incast₁) some)",
    evalOkWith "product biwarp mapeth both fields" "use ground.tung use ilk/product.tung yield (+1 both +2) biwarp { x ^ x + +1 } { y ^ y × +3 }" imports "eval ok: (+2 +6 both)",
    evalOkWith "product atfoldsome accumulateth worth context first" "use ground.tung use ilk/product.tung let worth ≔ 'worth:' both +2 let f ≔ 'function:' both { x ^ x + +1 } yield worth atfold f" imports "eval ok: ('worth:function:' +3 both)",
    evalOkWith "product monad accumulateth outer context first" "use ground.tung use ilk/product.tung yield ('outer:' both +2) bind { x ^ 'inner:' both (x + +1) }" imports "eval ok: ('outer:inner:' +3 both)",
    evalOkWith "product catamorphism foldeth the second field" "use ground.tung use ilk/product.tung use flock/functor/catamorphism.tung yield ('ignored' both +3) gather₁ +1 +" imports "eval ok: +4",
    evalOkWith "product traversal preserveth the first field" "use ground.tung use ilk/product.tung use ilk/maybe.tung use flock/functor/hath_throughwend.tung yield ('context' both +3) throughwend { x ^ (x + +1) some }" imports "eval ok: (('context' +4 both) some)",
    evalOkWith "atfoldsome lift2 for maybe" "use ground.tung use ilk/maybe.tung yield (+1 some) lift₂ (+2 some) +" imports "eval ok: (+3 some)",
    evalOkWith "atfoldsome keep_other preserveth context order" "use ground.tung use ilk/product.tung yield ('left:' both +1) keep_other ('right:' both +2)" imports "eval ok: ('right:left:' +2 both)",
    evalOkWith "functor void for maybe" "use ilk/maybe.tung use flock/functor.tung yield (+1 some) void" imports "eval ok: (only some)",
    evalOkWith "freer bind transformeth a completed worth" (freerPrelude ++ "yield ((+3 done) freer~bind { worth ^ (worth + +1) done }) run") imports "eval ok: +4",
    evalOkWith "freer lift and fold may repeat a continuation" (freerPrelude ++ "yield ask_freer run") imports "eval ok: +3",
    evalOkWith "freer bind may discard a continuation" (freerPrelude ++ "yield (ask_freer freer~bind { _ ^ +0 done }) run") imports "eval ok: +0",
    evalOkWith "freer mapping and flattening preserve suspended requests" (freerPrelude ++ "yield (ask_freer ground~warp { worth ^ worth + +10 } $ freer~warp { worth ^ worth done } $ freer~flat) run") imports "eval ok: +23",
    evalOkWith "list behead exposeth the head and tail" "use ilk/list.tung use ilk/maybe.tung use ilk/product.tung yield match (+1 ‥ empty) behead { (head product~both _) maybe~some ^ head, maybe~none ^ +0 }" imports "eval ok: +1",
    evalOkWith "till excludeth its stop" "use ilk/list.tung yield r{empty ≔ +2 till +2, reversed ≔ +3 till +1, two ≔ -1 till +1}" imports "eval ok: r{empty ≔ empty, reversed ≔ empty, two ≔ (-1 (+0 empty ‥) ‥)}",
    evalOkWith "list take after drop" "use ilk/list.tung yield ((+0 till +5) drop 2) take 2" imports "eval ok: (+2 (+3 empty ‥) ‥)",
    evalOkWith "list find returneth first match" "use ground.tung use ilk/list.tung yield (+0 till +5) find { x ^ +3 ≤ x }" imports "eval ok: (+3 some)",
    evalOkWith "list indexing is zero based" "use ilk/list.tung yield (+10 ‥ (+20 ‥ empty)) at 1" imports "eval ok: (+20 some)",
    evalOkWith "list index past the end faileth" "use ground.tung use ilk/list.tung yield (+10 ‥ (+20 ‥ empty)) at 2" imports "eval ok: none",
    evalOkWith "natural subtraction stoppeth at zero" "use ground.tung yield (2 - 3) + (5 - 2)" imports "eval ok: 3",
    evalOkWith "list last returneth the final worth" "use ilk/list.tung yield (+1 ‥ (+2 ‥ empty)) last" imports "eval ok: (+2 some)",
    evalOkWith "empty list hath no last worth" "use ilk/list.tung let values:ℤ list ≔ empty yield values last" imports "eval ok: none",
    evalOkWith "list membership findeth a worth" "use ground.tung use ilk/list.tung yield (+1 ‥ (+2 ‥ empty)) ∋ +2" imports "eval ok: yea",
    evalOkWith "list membership rejecteth a missing worth" "use ground.tung use ilk/list.tung yield (+1 ‥ (+2 ‥ empty)) ∋ +3" imports "eval ok: nay",
    evalOkWith "list replicate useth a nonnegative count" "use ilk/list.tung yield 'x' replicate 3" imports "eval ok: ('x' ('x' ('x' empty ‥) ‥) ‥)",
    evalOkWith "list partition preserveth order" "use ground.tung use ilk/list.tung yield (+0 till +5) partition { x ^ +2 ≤ x }" imports "eval ok: ((+2 (+3 (+4 empty ‥) ‥) ‥) (+0 (+1 empty ‥) ‥) both)",
    evalOkWith "list unzip preserveth both sides" "use ilk/list.tung use ilk/product.tung yield ((+1 both 'a') ‥ ((+2 both 'b') ‥ empty)) unzip" imports "eval ok: ((+1 (+2 empty ‥) ‥) ('a' ('b' empty ‥) ‥) both)",
    evalOkWith "n-ary sum addeth a foldable collection" "use ground.tung use ilk/list.tung use flock/functor/catamorphism.tung yield (+1 ‥ (+2 ‥ (+3 ‥ empty))) …+" imports "eval ok: +6",
    evalOkWith "n-ary sum of an empty collection is zero" "use ground.tung use ilk/list.tung use flock/functor/catamorphism.tung let values:ℤ list ≔ empty yield values …+" imports "eval ok: +0",
    evalTypeErrWith "n-ary sum needeth a catamorphism" "use ground.tung use flock/functor/catamorphism.tung ilk _box: [a:*, *] { box: [a, a _box] } let worth:ℤ _box ≔ +1 box yield worth …+" imports,
    evalOkWith "n-ary product multiplies a foldable collection" "use ground.tung use ilk/list.tung use flock/functor/catamorphism.tung yield (+2 ‥ (+3 ‥ (+4 ‥ empty))) …×" imports "eval ok: +24",
    evalOkWith "n-ary product of an empty collection is one" "use ground.tung use ilk/list.tung use flock/functor/catamorphism.tung let values:ℤ list ≔ empty yield values …×" imports "eval ok: +1",
    evalTypeErrWith "n-ary product needeth a fold monoid" "use ground.tung use ilk/list.tung use flock/functor/catamorphism.tung yield ('a' ‥ empty) …×" imports,
    evalOkWith "boolean upper wrapper useth disjunction" "use ground.tung use ilk/list.tung use flock/algebra/whole/semigroup.tung use flock/functor/catamorphism.tung let values ≔ (nay upper) ‥ ((yea upper) ‥ list~empty) yield match values …* { result upper ^ result }" imports "eval ok: yea",
    evalOkWith "empty boolean upper fold yieldeth nay" "use ground.tung use ilk/list.tung use flock/algebra/whole/semigroup.tung use flock/functor/catamorphism.tung let values:(𝟚 _upper) list ≔ list~empty yield match values …* { result upper ^ result }" imports "eval ok: nay",
    evalOkWith "boolean lower wrapper useth conjunction" "use ground.tung use ilk/list.tung use flock/algebra/whole/semigroup.tung use flock/functor/catamorphism.tung let values ≔ (yea lower) ‥ ((nay lower) ‥ list~empty) yield match values …* { result lower ^ result }" imports "eval ok: nay",
    evalOkWith "empty boolean lower fold yieldeth yea" "use ground.tung use ilk/list.tung use flock/algebra/whole/semigroup.tung use flock/functor/catamorphism.tung let values:(𝟚 _lower) list ≔ list~empty yield match values …* { result lower ^ result }" imports "eval ok: yea",
    evalOkWith "natural semiring computeth with both identities" "use ground.tung use ilk/natural.tung let two:ℕ ≔ 2 let three ≔ two + 1 yield ((two × three) + one) to_ℤ" imports "eval ok: +7",
    evalOkWith "natural semiring supplieth fold monoid evidence" "use ground.tung use ilk/list.tung use ilk/natural.tung use flock/functor/catamorphism.tung let two:ℕ ≔ 2 let three ≔ two + 1 yield ((two ‥ (three ‥ list~empty)) …×) to_ℤ" imports "eval ok: +6",
    evalOkWith "nonnegative ℤ converteth to natural" "use ground.tung use ilk/natural.tung yield +3 to_ℕ" imports "eval ok: (3 some)",
    evalOkWith "unsigned digits are a natural" "use ground.tung yield (2 + 3) × 4" imports "eval ok: 20",
    evalOkWith "undernaught ℤ cannot become natural" "use ground.tung yield -1 to_ℕ" imports "eval ok: none",
    evalOkWith "complex sine of zero is zero" "use ground.tung use numeric/evenbraid.tung yield ((0.0 +i 0.0) sine) real" imports "eval ok: 0.0",
    evalOkWith "complex cosine of zero is one" "use ground.tung use numeric/evenbraid.tung yield ((0.0 +i 0.0) cosine) real" imports "eval ok: 1.0",
    evalOkWith "complex exponentiation scaleth by the real exponent" "use ground.tung use numeric/evenbraid.tung yield ((1.0 +i 0.0) exponent) real" imports "eval ok: 2.718281828459045",
    evalOkWith "complex sine of unit imaginary yieldeth hyperbolic sine" "use ground.tung use numeric/evenbraid.tung yield ((0.0 +i 1.0) sine) imaginary" imports "eval ok: 1.1752011936438014",
    evalOkWith "complex cosine of unit imaginary yieldeth hyperbolic cosine" "use ground.tung use numeric/evenbraid.tung yield ((0.0 +i 1.0) cosine) real" imports "eval ok: 1.5430806348152437",
    evalOkWith "nonempty warp preserveth the first element" "use ground.tung use ilk/list.tung use ilk/nonempty.tung yield ((+1 ‥′ (+2 ‥ empty)) warp { x ^ x + +1 }) to_list" imports "eval ok: (+2 (+3 empty ‥) ‥)",
    evalOkWith "nonempty semigroup appendeth without losing the head" "use ground.tung use ilk/list.tung use ilk/nonempty.tung use flock/algebra/whole/hath_magma.tung yield ((+1 ‥′ (+2 ‥ empty)) · (+3 ‥′ empty)) to_list" imports "eval ok: (+1 (+2 (+3 empty ‥) ‥) ‥)",
    evalOkWith "nonempty atfoldsome applieth every function" "use ground.tung use ilk/list.tung use ilk/nonempty.tung let values ≔ +1 ‥′ (+2 ‥ empty) let fs ≔ { x ^ x + +1 } ‥′ ({ x ^ x × +2 } ‥ empty) yield (values atfold fs) to_list" imports "eval ok: (+2 (+3 (+2 (+4 empty ‥) ‥) ‥) ‥)",
    evalOkWith "nonempty monad concatenateth every result" "use ground.tung use ilk/list.tung use ilk/nonempty.tung let values ≔ +1 ‥′ (+2 ‥ empty) yield (values bind { x ^ x ‥′ ((x + +10) ‥ empty) }) to_list" imports "eval ok: (+1 (+11 (+2 (+12 empty ‥) ‥) ‥) ‥)",
    evalOkWith "nonempty catamorphism visiteth the head first" "use ground.tung use ilk/list.tung use ilk/nonempty.tung use flock/functor/catamorphism.tung yield (+1 ‥′ (+2 ‥ empty)) gather₁ +0 +" imports "eval ok: +3",
    evalOkWith "nonempty traversal keepeth a nonempty result" "use ground.tung use ilk/list.tung use ilk/nonempty.tung use ilk/maybe.tung use flock/functor/hath_throughwend.tung yield ((+1 ‥′ (+2 ‥ empty)) throughwend { x ^ (x + +1) some }) warp to_list" imports "eval ok: ((+2 (+3 empty ‥) ‥) some)",
    evalOkWith "nonempty membership delegateth to list" "use ground.tung use ilk/list.tung use ilk/nonempty.tung yield (+1 ‥′ (+2 ‥ empty)) ∋ +2" imports "eval ok: yea",
    evalOkWith "table put replaceth a key" "use ground.tung use ilk/table.tung let table ≔ (empty put 'a' +1) put 'a' +2 yield table lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "table membership dispatcheth through inhold" "use ground.tung use ilk/table.tung let table ≔ empty put 'a' +1 yield table ∋ 'a'" imports "eval ok: yea",
    evalOkWith "table constructor may be qualified" "use ground.tung use ilk/list.tung use ilk/product.tung use ilk/table.tung yield (('a' both +2) ‥ list~empty) table~from_list $ lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "table rid droppeth a key" "use ground.tung use ilk/table.tung let table ≔ empty put 'a' +1 yield (table rid 'a') lookup 'a'" imports "eval ok: none",
    evalOkWith "set put keepeth values unique" "use ground.tung use ilk/set.tung yield ((empty put +1) put +1) to_list" imports "eval ok: (+1 empty ‥)",
    evalOkWith "set constructor may be qualified" "use ground.tung use ilk/list.tung use ilk/set.tung yield (+1 ‥ (+2 ‥ list~empty)) set~from_list $ to_list" imports "eval ok: (+1 (+2 empty ‥) ‥)",
    evalOkWith "set rid droppeth a worth" "use ground.tung use ilk/set.tung let values ≔ (empty put +1) put +2 yield (values rid +1) ∋ +1" imports "eval ok: nay",
    evalOkWith "set supremum keepeth unique values" "use ground.tung use ilk/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +3 yield (left ∨ right) to_list" imports "eval ok: (+3 (+2 (+1 empty ‥) ‥) ‥)",
    evalOkWith "set infimum keepeth shared values" "use ground.tung use ilk/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +3 yield (left ∧ right) to_list" imports "eval ok: (+2 empty ‥)",
    evalOkWith "set is ignoreth insertion order" "use ground.tung use ilk/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +1 yield left ≍ right" imports "eval ok: yea",
    evalOkWith "set half order compareth inclusion" "use ground.tung use ilk/set.tung let smaller ≔ empty put +1 let larger ≔ smaller put +2 yield (smaller ≤ larger) ∧ (smaller < larger)" imports "eval ok: yea",
    evalOkWith "set inclusion rejecteth a proper superset" "use ground.tung use ilk/set.tung let smaller ≔ empty put +1 let larger ≔ smaller put +2 yield larger ≤ smaller" imports "eval ok: nay",
    evalOkWith "powerset addition is evenmete difference" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ { worth ^ (worth ≍ +1) ∨ (worth ≍ +2) } let right:ℤ powerset ≔ { worth ^ (worth ≍ +2) ∨ (worth ≍ +3) } yield ((left + right) ∋ +2)" imports "eval ok: nay",
    evalOkWith "powerset addition keepeth an unshared member" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ { worth ^ worth ≍ +1 } let right:ℤ powerset ≔ { worth ^ worth ≍ +2 } yield ((left + right) ∋ +1)" imports "eval ok: yea",
    evalOkWith "powerset multiplication is intersection" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ { worth ^ (worth ≍ +1) ∨ (worth ≍ +2) } let right:ℤ powerset ≔ { worth ^ worth ≍ +2 } yield ((left × right) ∋ +2)" imports "eval ok: yea",
    evalOkWith "powerset supremum is union" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ { worth ^ worth ≍ +1 } let right:ℤ powerset ≔ { worth ^ worth ≍ +2 } yield (left ∨ right) ∋ +2" imports "eval ok: yea",
    evalOkWith "powerset infimum is intersection" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ { worth ^ (worth ≍ +1) ∨ (worth ≍ +2) } let right:ℤ powerset ≔ { worth ^ worth ≍ +2 } yield (left ∧ right) ∋ +1" imports "eval ok: nay",
    evalOkWith "powerset complement excludeth a former member" "use ground.tung use ilk/powerset.tung let one:ℤ powerset ≔ { worth ^ worth ≍ +1 } let outside:ℤ powerset ≔ one ¬ yield outside ∋ +1" imports "eval ok: nay",
    evalOkWith "powerset complement includeth a former nonmember" "use ground.tung use ilk/powerset.tung let one:ℤ powerset ≔ { worth ^ worth ≍ +1 } let outside:ℤ powerset ≔ one ¬ yield outside ∋ +2" imports "eval ok: yea",
    evalOkWith "powerset updates compose pointwise" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ (powerset~empty put +1) put +2 let right:ℤ powerset ≔ powerset~empty put +2 yield >{∧, left ∋ +1, ((left rid +1) ∋ +1) ¬, (left ∖ right) ∋ +1, ((left ∖ right) ∋ +2) ¬}" imports "eval ok: yea",
    evalOkWith "powerset subtraction is evenmete difference" "use ground.tung use ilk/powerset.tung let values:ℤ powerset ≔ { worth ^ worth ≍ +1 } yield ((values - values) ∋ +1)" imports "eval ok: nay",
    evalOkWith "powerset zero is empty" "use ground.tung use ilk/powerset.tung let values:ℤ powerset ≔ zero yield values ∋ +7" imports "eval ok: nay",
    evalOkWith "powerset one is universal" "use ground.tung use ilk/powerset.tung let values:ℤ powerset ≔ one yield values ∋ +7" imports "eval ok: yea",
    evalOkWith "set becometh a powerset" "use ground.tung use ilk/set.tung use ilk/powerset.tung let finite ≔ set~empty set~put +7 yield (finite to_powerset) ∋ +7" imports "eval ok: yea",
    evalOkWith "powerset lower wrapper useth intersection" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/algebra/whole/semigroup.tung use flock/functor/catamorphism.tung let one:ℤ powerset ≔ { worth ^ worth ≍ +1 } let both:ℤ powerset ≔ { worth ^ (worth ≍ +1) ∨ (worth ≍ +2) } let wrapped ≔ (one lower) ‥ ((both lower) ‥ list~empty) yield match wrapped …* { result lower ^ result ∋ +2 }" imports "eval ok: nay",
    evalOkWith "powerset upper wrapper useth union" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/algebra/whole/semigroup.tung use flock/functor/catamorphism.tung let one:ℤ powerset ≔ { worth ^ worth ≍ +1 } let two:ℤ powerset ≔ { worth ^ worth ≍ +2 } let wrapped ≔ (one upper) ‥ ((two upper) ‥ list~empty) yield match wrapped …* { result upper ^ result ∋ +2 }" imports "eval ok: yea",
    evalOkWith "empty powerset wrapper monoids select their bounds" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/algebra/whole/semigroup.tung use flock/functor/catamorphism.tung let meets:((ℤ powerset) _lower) list ≔ list~empty let joins:((ℤ powerset) _upper) list ≔ list~empty yield >{∧, match meets …* { result lower ^ result ∋ +42 }, match joins …* { result upper ^ (result ∋ +42) ¬ }}" imports "eval ok: yea",
    evalTypeErrWith "powerset hath no arbitrarily chosen monoid" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/algebra/whole/semigroup.tung use flock/functor/catamorphism.tung let values:(ℤ powerset) list ≔ list~empty yield values …*" imports,
    evalOkWith "table functor mapeth values" "use ground.tung use ilk/table.tung let table ≔ (empty put 'a' +1) put 'b' +2 yield (table warp { x ^ x + +10 }) lookup 'a'" imports "eval ok: (+11 some)",
    evalOkWith "table sift keepeth matching values" "use ground.tung use ilk/table.tung use flock/functor/hath_sift.tung let table ≔ (empty put 'a' +1) put 'b' +2 yield (table sift { x ^ +2 ≤ x }) lookup 'a'" imports "eval ok: none",
    evalOkWith "table merge preferreth right values" "use ground.tung use ilk/table.tung let left ≔ empty put 'a' +1 let right ≔ empty put 'a' +2 yield (left merge right) lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "table adjust changeth an existing worth" "use ground.tung use ilk/table.tung let table ≔ empty put 'a' +1 yield (table adjust 'a' { x ^ x + +1 }) lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "text operations use unicode code points" "use ground.tung use ilk/text/operation.tung yield ('aβ字' reverse_text) take_text 2" imports "eval ok: '字β'",
    evalOkWith "text size counteth unicode code points" "use ground.tung use ilk/text/operation.tung use flock/hath_size.tung use ilk/natural.tung yield ('aβ字' size) to_ℤ" imports "eval ok: +3",
    evalOkWith "text split and join preserve empty fields" "use ground.tung use ilk/text/operation.tung yield ('a,b,,c' split_text `,) join_with_text '.'" imports "eval ok: 'a.b..c'",
    evalOkWith "text words collapse whitespace runs" "use ground.tung use ilk/text/operation.tung yield ' red\\tblue\\nred ' words_text $ join_with_text '.'" imports "eval ok: 'red.blue.red'",
    evalOkWith "typed paths join components" "use ground.tung use ilk/path.tung yield (('root' path) path~join ('leaf' path)) to_text" imports "eval ok: 'root/leaf'",
    evalOkWith "time spans drive async sleep" "use ground.tung use ilk/milliseconds.tung yield (0 milliseconds) sleep_for" imports "eval ok: only",
    evalOkWith "process captureth standard output" "use ground.tung use deed/process.tung use process/result.tung use ilk/list.tung use ilk/sum.tung yield 'printf' process~run ('hello' ‥ empty) $ warp { result ^ result warp process_output }" imports "eval ok: ('hello' incast₁)",
    evalTypeErrWith "missing import is rejected before runtime" "use missing.tung" Map.empty,
    evalTypeErrWith "import cycle is rejected before runtime" "use left.tung" (cyclicImports <> imports),
    evalOkWith "arctan range is nonnegative" "use _foreign.tung yield 0.0 arctan_float -1.0" imports "eval ok: 4.71238898038469",
    evalOkWith "fork and wait" "use ground.tung let work:ℤ deed ≔ +42 sheer yield work fork $ bind wait" imports "eval ok: (+42 some)",
    evalOkWith "task result may be awaited repeatedly" "use ground.tung let work:ℤ deed ≔ +21 sheer yield work fork $ bind { task ^ (task wait) lift₂ (task wait) { a, b ^ a lift₂ b + } }" imports "eval ok: (+42 some)",
    evalOkWith "task wait may time out" "use ground.tung let work:ℤ deed ≔ (200 sleep) then (+42 sheer) yield work fork $ bind { task ^ task wait_for 0 }" imports "eval ok: none",
    evalOkWith "task wait_for returneth a finished worth" "use ground.tung let work:ℤ deed ≔ +42 sheer yield work fork $ bind { task ^ task wait_for 1000 }" imports "eval ok: (+42 some)",
    evalOkWith "a cancelled task yieldeth none" "use ground.tung let work:ℤ deed ≔ (1000 sleep) then (+42 sheer) yield work fork $ bind { task ^ (task outstrike) then (task wait) }" imports "eval ok: none",
    evalOkWith "cpu-bound task remaineth cancellable" "use ground.tung let spin:ℤ deed ≔ { again ^ (only sheer) bind { _ ^ again } } deed_steadfast yield spin fork $ bind { task ^ (task outstrike) then (task wait) }" imports "eval ok: none",
    evalTypeErrWith "an opaque task cannot be eliminated as an empty family" "use ground.tung let unwrap:[worth:ℤ task, ℤ] ≔ match worth {} yield +0" imports,
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
        [ ("left.tung", "use ground.tung use shared.tung show let left ≔ shared~base + +1"),
          ("right.tung", "use ground.tung use shared.tung show let right ≔ shared~base + +2"),
          ("shared.tung", "show let base ≔ +1")
        ]
    instanceDiamondImports =
      Map.fromList
        [ ("left.tung", "use shared.tung show shared~sameness"),
          ("right.tung", "use shared.tung"),
          ("shared.tung", "show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x }")
        ]
    distinctClassImports =
      Map.fromList
        [ ("left.tung", "use ground.tung show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +1 }"),
          ("right.tung", "use ground.tung show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + +2 }")
        ]
    collidingMemberPrelude = "use left.tung use right.tung flock both:[a:*, @:a first, @:a second, *] { let own:[a, ℤ] } "
    collidingMemberImports =
      Map.fromList
        [ ("left.tung", "show flock first:[a:*, *] { let tag:[a, ℤ] }"),
          ("right.tung", "show flock second:[a:*, *] { let tag:[a, ℤ] }")
        ]
    samePrefixInstanceImports = Map.fromList [("a.tung", identityInstance 1), ("a.extra.tung", identityInstance 10)]
    dottedDirectoryInstanceImports = Map.fromList [("pkg.one/sameness.tung", identityInstance 1), ("pkg.two/sameness.tung", identityInstance 10)]
    identityInstance :: Int -> String
    identityInstance increment = "use ground.tung show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x + " ++ integerSource increment ++ " }"
    nominalTypeInstanceImports =
      Map.fromList
        [ ("common.tung", "show flock hath_label:[a:*, *] { let label:[a, ℤ] }"),
          ("left.tung", "use common.tung show ilk _token: * { token: _token } bizen:_token common~hath_label { let label: [_:] ≔ +1 } show let worth:_token ≔ token"),
          ("right.tung", "use common.tung show ilk _token: * { token: _token } bizen:_token common~hath_label { let label: [_:] ≔ +10 } show let worth:_token ≔ token")
        ]
    transparentAliasInstanceImports =
      Map.fromList
        [ ("base.tung", "show ilk _token: * { token: _token } show flock hath_label:[a:*, *] { let label:[a, ℤ] } bizen:_token hath_label { let label: [_:] ≔ +7 }"),
          ("alias.tung", "use base.tung show let alias:* ≔ base~_token show let worth:alias ≔ base~token")
        ]
    privateAliasInstanceImports =
      Map.singleton
        "opaque.tung"
        "ilk _secret: * { secret: _secret } show let public:* ≔ _secret show flock hath_label:[a:*, *] { let label:[a, ℤ] } bizen:_secret hath_label { let label: [_:] ≔ +7 } show let worth:public ≔ secret"
    reexportImports = Map.fromList [("base.tung", "show let worth ≔ +7"), ("middle.tung", "use base.tung show base~worth")]
    identityImports = Map.fromList [("sameness.tung", "show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x }")]
    dataReexportImports =
      Map.fromList
        [ ("data_base.tung", "show ilk _box: [a:*, *] { box: [a, a _box] }"),
          ("data_middle.tung", "use data_base.tung show data_base~box")
        ]
    constructorReexportImports =
      Map.fromList
        [ ("base.tung", "show ilk bit: * { off: bit }"),
          ("middle.tung", "use base.tung show base~bit show base~off")
        ]
    cyclicImports = Map.fromList [("left.tung", "use right.tung"), ("right.tung", "use left.tung")]
    -- a request names its answer type; the handler answereth each `ask` twice.
    freerPrelude =
      "use ground.tung use ilk/freer.tung "
        ++ "ilk question: [a:*, *] { ask: ℤ question } "
        ++ "let ask_freer: question freer ℤ ≔ ask lift "
        ++ "let answer: [@ξ:*, request: ξ question, continue: [ξ, ℤ], ℤ] ≔ match request { ask ^ (+1 continue) + (+2 continue) } "
        ++ "let run: [forewrit: question freer ℤ, ℤ] ≔ { worth ^ worth } gather answer forewrit "

randomRange :: Map.Map String String -> Test
randomRange imports = do
  actual <- Harness.evaluateSource "use ground.tung yield random" imports
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
      "use ground.tung "
        ++ "let work:ℤ deed ≔ (600 sleep) then (+21 sheer) "
        ++ "yield work fork $ bind { left ^ work fork $ bind { right ^ (left wait) then (right wait_for 100) } }"

systemArguments :: Map.Map String String -> Test
systemArguments imports = do
  actual <- Harness.evaluateSourceWithArgs ["north", "two words"] "use ground.tung use deed/system.tung yield arguments" imports
  pure $ if actual == "eval ok: ('north' ('two words' empty ‥) ‥)" then Nothing else Just ("system arguments: " ++ actual)

systemEnvironment :: Map.Map String String -> Test
systemEnvironment imports = bracket (Environment.lookupEnv name) restore $ \_ -> do
  Environment.setEnv name "seen"
  actual <- Harness.evaluateSource ("use ground.tung use deed/system.tung yield '" ++ name ++ "' environment") imports
  pure $ if actual == "eval ok: ('seen' some)" then Nothing else Just ("system environment: " ++ actual)
  where
    name = "TUNG_TEST_ENVIRONMENT"
    restore Nothing = Environment.unsetEnv name
    restore (Just value) = Environment.setEnv name value

unixTime :: Map.Map String String -> Test
unixTime imports = do
  before <- floor <$> getPOSIXTime
  actual <- Harness.evaluateSource "use ground.tung use deed/clock.tung yield unix_time" imports
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
