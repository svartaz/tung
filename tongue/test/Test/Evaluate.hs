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
    ("declared type parameters add no runtime arguments", "let constant:[@a:*, @b:*, x:a, _:b, a] ≔ x yield +1 constant 'x'", "eval ok: +1"),
    ("explicit type inputs are erased beside value inputs", "let f:[@a:*, @b:*, x:a, _:b, a] ≔ x yield +1 f @ℤ @text 'x'", "eval ok: +1"),
    ("instance method type inputs are erased", "let id:[@a:*, x:a, a] ≔ x flock owner:[a:*, *] { let copy:[@b:*, a, b, b] } bizen:ℤ owner { let copy:[@c:*, _:ℤ, x:c, c] ≔ x id @c } yield +1 copy 'x'", "eval ok: 'x'"),
    ("unused type inputs requireþ no runtime argument", "let value:[@a:*, ℤ] ≔ +7 yield value @text", "eval ok: +7"),
    ("higher-rank argument is erased and instantiated twice", "let both:[f:[@a:*, a, a], r{number:ℤ, word:text}] ≔ r{number≔+1 f, word≔'x' f} let id: [x:] ≔ x yield (id both).number", "eval ok: +1"),
    ("polymorphic return needs no runtime type arguments", "let make:[_:ℤ, [@a:*, a, a]] ≔ {x ^ x} yield 'yes' (+1 make)", "eval ok: 'yes'"),
    ("left-associated sequence", "use ground.tung yield <{-, +10, +3, +2}", "eval ok: +5"),
    ("right-associated sequence", "use ground.tung yield >{-, +10, +3, +2}", "eval ok: +9"),
    ("nested brace forms share type and expression boundaries", "use ground.tung let record:r{callback:[ℤ, ℤ], nested:r{value:ℤ}} ≔ r{callback≔{x ^ <{+, x, +1}}, nested≔r{value≔+2}} yield record.nested.value record.callback", "eval ok: +3"),
    ("term type ascription is erased before evaluation", "use ground.tung yield (+1 + +2: ℤ)", "eval ok: +3"),
    ("ascribed anonymous function remaineþ recursive", "use ground.tung let factorial ≔ ({ 0 ^ 1, n succeed ^ (n succeed) × (n factorial) }: [ℕ, ℕ]) yield 5 factorial", "eval ok: 120"),
    ("ℤ arithmetic is arbitrary precision", "use ground.tung yield +999999999999999999999999999999 + +1", "eval ok: +1000000000000000000000000000000"),
    ("fremmed key selecteþ a host function independently of the let name", "let plus:[ℤ, ℤ, ℤ] ≔ 'add_integer' fremmed yield +1 plus +2", "eval ok: +3"),
    ("unicode text", "yield 'λ字'", "eval ok: 'λ字'"),
    ("unicode control rendering useþ decimal terminator", "yield `\\1;", "eval ok: `\\1;"),
    ("float arithmetic", "use ground.tung yield 0.5 + 0.25", "eval ok: 0.75"),
    ("text becomeþ a float", "use ground.tung use ilk/option.tung let parsed:float option ≔ '0.5' from_text yield parsed", "eval ok: (0.5 some)"),
    ("unparsable text yieldeþ none", "use ground.tung use ilk/option.tung let parsed:float option ≔ 'not a float' from_text yield parsed", "eval ok: none"),
    ("division by zero yieldeþ none", "use ground.tung " ++ optionData ++ "yield +1 % +0", "eval ok: none"),
    ("float division useþ the division sign", "use ground.tung yield 6.0 ÷ 4.0", "eval ok: 1.5"),
    ("float division by zero followeþ ieee", "use ground.tung yield 1.0 ÷ 0.0", "eval ok: Infinity"),
    ("float equality ignoreþ literal spelling", "use ground.tung ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } yield 1.0 ≍ 1.00", "eval ok: yea"),
    ("bracketed natural constructors construct and match", "ilk nat: * { zero: nat, suc: [nat, nat] } yield match zero suc { x suc ^ +1, zero ^ +0 }", "eval ok: +1"),
    ("bracketed list constructors preserve native ABI", "ilk list: [a:*, *] { empty: a list, ‥: [a, a list, a list] } yield match (+1 ‥ empty) { first ‥ _ ^ first, empty ^ +0 }", "eval ok: +1"),
    ("indexed constructor match useþ its refined payload", indexedUnpackSource ++ "yield (+3 integer) unpack", "eval ok: +3"),
    ("indexed constructor match useþ its other branch", indexedUnpackSource ++ "yield ('hi' textual) unpack", "eval ok: 'hi'"),
    ("float ordering is numeric", "use ground.tung ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } yield 2.0 ≤ 10.0", "eval ok: yea"),
    ("curried partial application", "use ground.tung let add: [a:, b:] ≔ a + b let add_one ≔ +1 add yield +2 add_one", "eval ok: +3"),
    ("three curried arguments", "use ground.tung let add: [a:, b:, c:] ≔ (a + b) + c yield +1 add +2 +3", "eval ok: +6"),
    ("local recursive function", "use ground.tung ilk nat: * { zero: nat, suc: [nat, nat] } let count ≔ (let loop: [nat, ℤ] ≔ { zero ^ +0, n suc ^ +1 + (n loop) } yield loop) yield ((zero suc) suc) count", "eval ok: +2"),
    ("recursive calls retain inferred evidence", "use ground.tung flock haþ_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ haþ_identity { let identity: [x:] ≔ x + +1 } let loop: [ℕ, ℤ, ℤ] ≔ { 0, x ^ x identity, n succeed, x ^ n loop x } yield 2 loop +3", "eval ok: +4"),
    ("recursive evidence surviveþ a nested polymorphic binding", "use ground.tung flock haþ_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ haþ_identity { let identity: [x:] ≔ x + +1 } let loop: [ℕ, ℤ, ℤ] ≔ { 0, x ^ x identity, n succeed, x ^ (let echo: [y:] ≔ y identity yield (n loop x) echo) } yield 2 loop +3", "eval ok: +6"),
    ("second-position function header", "use ground.tung let add: [a:, b:] ≔ a + b yield +1 add +2", "eval ok: +3"),
    ("dollar function segment", "use ground.tung let f: [x:] ≔ x + +1 let h: [x:, y:, z:] ≔ (x + y) × z yield +1 f $h +2 +3", "eval ok: +12"),
    ("lexical closure", "let x ≔ +1 let f: [_:] ≔ x yield (let x ≔ +2 yield +0 f)", "eval ok: +1"),
    ("sequential shadowing preserveþ each preceding local", "use ground.tung yield (let value ≔ +1 let value ≔ value + +1 let value ≔ value + +1 yield value)", "eval ok: +3"),
    ("nested same-text pattern binders remain distinct", "use ground.tung yield match +1 { value ^ (match +2 { value ^ value }) + value }", "eval ok: +3"),
    ("multi-scrutinee match", boolData ++ "yield match yea, nay { yea, yea ^ +1, yea, nay ^ +2, nay, yea ^ +3, nay, nay ^ +4 }", "eval ok: +2"),
    ("nested constructor match", boolData ++ optionData ++ "yield match nay some { yea some ^ +1, nay some ^ +2, none ^ +0 }", "eval ok: +2"),
    ("first matching arm winneþ", boolData ++ "yield match yea { yea ^ +1, _ ^ +2 }", "eval ok: +1"),
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
    ("fremmed arity followeþ a transparent alias", "let binary:* ≔ [ℤ, ℤ, ℤ] let plus:binary ≔ 'add_integer' fremmed yield +1 plus +2", "eval ok: +3"),
    ("an unused top-level definition is not computed", "let missing:ℤ ≔ sorry yield +1", "eval ok: +1"),
    ("a demanded top-level definition is computed", "let missing:ℤ ≔ sorry yield missing", "eval error: reached sorry"),
    ("an unused argument is not computed", "let ignore:[_:ℤ, ℤ] ≔ +7 yield (+1 (sorry:[ℤ, ℤ])) ignore", "eval ok: +7"),
    ("an unused local definition is not computed", "yield (let unused:ℤ ≔ +1 (sorry:[ℤ, ℤ]) yield +7)", "eval ok: +7"),
    ("record projection computeþ only the selected field", "yield r{kept ≔ +7, unused ≔ +1 (sorry:[ℤ, ℤ])}.kept", "eval ok: +7"),
    ("recursion under a match computeþ only þe chosen branch", rowData ++ "let flips: [r: row, inside: 𝟚, ℕ] ≔ match r { stop ^ 0, _ more rest ^ match inside { yea ^ (rest flips nay) succeed, nay ^ rest flips yea } } yield (64 ones) flips yea", "eval ok: 32"),
    ("a user function computeþ only its selected recursive input", recursiveChoiceSource, "eval ok: +8"),
    ("an unused constructor field and recursive hypothesis are not computed", rowData ++ "let first: [r: row, 𝟚] ≔ match r { stop ^ nay, c more _ ^ c } yield (yea more (0 (sorry:[ℕ, row]))) first", "eval ok: yea"),
    ("a yielded value is computed in full", "yield r{kept ≔ +1, missing ≔ (sorry: ℤ)}", "eval error: reached sorry"),
    ("a yielded deed is performed", "use ilk/one.tung " ++ sleepBinding ++ "yield 0 sleep", "eval ok: only"),
    ("deed_bind passeþ a result on", deedPrelude ++ "let plus:[ℤ, ℤ, ℤ] ≔ 'add_integer' fremmed yield (+2 pure) bind { x ^ (x plus +1) pure }", "eval ok: +3"),
    ("a deed is a value until performed", deedPrelude ++ "let action:ℤ deed ≔ +1 pure yield (let unused ≔ action yield +2)", "eval ok: +2"),
    ("flock laws are erased", "flock haþ_identity:[a:*, *] { let identity:[a, a] let rule:[x: a, (x identity) = x] } bizen:ℤ haþ_identity { let identity: [x:] ≔ x let rule ≔ sorry } yield +2 identity", "eval ok: +2"),
    ("result-only member useþ expected type", "flock haþ_origin:[a:*, *] { let origin:a } bizen:ℤ haþ_origin { let origin ≔ +7 } let value:ℤ ≔ origin yield value", "eval ok: +7"),
    ("different instances dispatch by inferred type", "flock haþ_label:[a:*, *] { let label:[a, text] } bizen:ℤ haþ_label { let label: [_:] ≔ 'ℤ' } bizen:text haþ_label { let label: [_:] ≔ 'text' } yield 'x' label", "eval ok: 'text'"),
    ("constraint function receiveþ its caller dictionary", "flock haþ_label:[a:*, *] { let label:[a, text] } bizen:ℤ haþ_label { let label: [_:] ≔ 'ℤ' } bizen:text haþ_label { let label: [_:] ≔ 'text' } let labelled:[@a:*, @:a haþ_label, x: a, text] ≔ x label yield +1 labelled", "eval ok: 'ℤ'"),
    ("child dictionary useþ a direct parent instance", "flock haþ_parent:[a:*, *] { let parent:[a, a] } flock haþ_child:[a:*, @:a haþ_parent, *] { let child:[a, a] } bizen:ℤ haþ_parent { let parent: [x:] ≔ x } bizen:ℤ haþ_child { let child: [x:] ≔ x parent } yield +4 child", "eval ok: +4"),
    ("repeated bizen calls retain a preceding private value", "use ground.tung flock haþ_bump:[a:*, *] { let bump:[a, a] } let offset ≔ +2 bizen:ℤ haþ_bump { let bump: [x:] ≔ x + offset } yield (+1 bump) + (+2 bump)", "eval ok: +7"),
    ("bizen may precede its resolved flock declaration", "bizen:ℤ haþ_identity { let identity: [x:] ≔ x } flock haþ_identity:[a:*, *] { let identity:[a, a] } yield +3 identity", "eval ok: +3"),
    ("bizen constraint remaineþ an external dictionary", "use ground.tung flock haþ_combine:[a:*, *] { let combine:[a, a, a] } bizen:ℤ haþ_combine { let combine: [x:, y:] ≔ x + y } ilk _box: [a:*, *] { box: [a, a _box] } bizen:[@a:*, @:a haþ_combine, (a _box) haþ_combine] { let combine: [x box:, y box:] ≔ (x combine y) box } yield (+1 box) combine (+2 box)", "eval ok: (+3 box)")
  ]

indexedUnpackSource :: String
indexedUnpackSource =
  "ilk tag: [a:*, *] { integer: [ℤ, ℤ tag], textual: [text, text tag] } "
    ++ "let unpack:[@a:*, x:a tag, a] ≔ match x { n integer ^ n, t textual ^ t } "

-- both inputs recurse; the discarded path faileþ at its base.
recursiveChoiceSource :: String
recursiveChoiceSource =
  rowData
    ++ """
       let add:[ℤ, ℤ, ℤ] ≔ 'add_integer' fremmed
       let choose:[flag:𝟚, yes:ℤ, no:ℤ, ℤ] ≔ match flag { yea ^ yes, nay ^ no }
       let count:[r:row, flag:𝟚, ℤ] ≔ match r {
         stop ^ match flag { yea ^ +0, nay ^ +0 (sorry:[ℤ, ℤ]) },
         _ more rest ^ flag choose (+1 add (rest count yea)) (rest count nay)
       }
       yield (8 ones) count yea

       """

typeErrors :: [(String, String)]
typeErrors =
  [ ("unknown value", "yield missing"),
    ("captured alias mismatch is rejected before evaluation", "let bad: [x:] ≔ (let y ≔ x let number:ℤ ≔ y yield number + +1) yield 'oops' bad"),
    ("non-function application", "yield +1 +2"),
    ("constructor overapplication", "ilk _box: [a:*, *] { box: [a, a _box] } yield +1 box +2"),
    ("missing record field", "let value ≔ r{x ≔ +1} yield value.y"),
    ("unknown record removal", "let person ≔ r{name ≔ 'n'} yield r{≔ person, - age}"),
    ("update of non-record", "yield r{≔ +1, field ≔ +2}"),
    ("non-exhaustive match", boolData ++ "yield match nay { yea ^ +1 }"),
    ("a deed is not its result", "use ground.tung " ++ deedPrelude ++ "yield (+1 pure) + +1")
  ]

importedCases :: Map.Map String String -> [Test]
importedCases imports =
  [ evalOkWith
      "a local term and an imported constructor retain distinct runtime identities"
      "use token.tung let box ≔ +7 yield r{constructor ≔ token~box, local ≔ box}"
      (Map.singleton "token.tung" "show ilk token: * { box: token }")
      "eval ok: r{constructor ≔ box, local ≔ +7}",
    evalOkWith "imported call" "use ground.tung use file.tung yield +2 inc" (Map.insert "file.tung" "use ground.tung show let inc: [x:] ≔ x + +1" imports) "eval ok: +3",
    evalOkWith "a use declaration is initialised before a preceding let" "let answer ≔ dep~value use dep.tung yield answer" (Map.insert "dep.tung" "show let value ≔ +7" imports) "eval ok: +7",
    evalOkWith "a local and its imported predecessor retain distinct identities" "use ground.tung use source.tung let value ≔ value + +1 yield value + source~value" (Map.insert "source.tung" "show let value ≔ +2" imports) "eval ok: +5",
    evalTypeErrWith "a local value shadoweþ an imported constructor in patterns" "use ilk/two.tung let yea:𝟚 ≔ two~yea yield match yea { yea ^ +1, nay ^ +0 }" imports,
    evalOkWith "a qualified pattern still reacheþ a shadowed constructor" "use ilk/two.tung let yea ≔ +0 yield match two~yea { two~yea ^ +1, nay ^ +0 }" imports "eval ok: +1",
    evalOkWith "default use alias workeþ for values, classes, and constructor patterns" "use ilk/item.tung let value:item~_item ≔ item~empty yield match (value item~identity) { item~item ^ +1 }" (Map.insert "ilk/item.tung" "show ilk _item: * { item: _item } show flock haþ_identity:[a:*, *] { let identity:[a, a] } bizen:_item haþ_identity { let identity: [x:] ≔ x } show let empty:_item ≔ item" imports) "eval ok: +1",
    evalOkWith "derived flock operations" "use ground.tung yield (+1 < +2) ∧ (+1 ≭ +2)" imports "eval ok: yea",
    evalOkWith "false implieþ false" "use ground.tung yield nay ≤ nay" imports "eval ok: yea",
    evalOkWith "true doth not imply false" "use ground.tung yield yea ≤ nay" imports "eval ok: nay",
    evalOkWith "succeed patterns recurse on a natural" "use ground.tung let double: [n: ℕ, ℕ] ≔ match n { 0 ^ 0, m succeed ^ (m double) + 2 } yield 3 double" imports "eval ok: 6",
    evalOkWith "succeed addeþ one to a natural" "yield (2 succeed) succeed" imports "eval ok: 4",
    evalOkWith "euclidean division returneþ quotient and remainder for a negative divisor" "use ground.tung use ilk/product.tung yield +5 % -3" imports "eval ok: ((-1 +2 boþ) some)",
    evalOkWith "euclidean division returneþ quotient and remainder for a negative dividend" "use ground.tung use ilk/product.tung yield -5 % +3" imports "eval ok: ((-2 +1 boþ) some)",
    evalOkWith "euclidean quotient and remainder reconstruct the dividend" "use ground.tung use ilk/option.tung use ilk/product.tung let dividend ≔ -5 let divisor ≔ -3 yield match dividend % divisor { (quotient boþ rest) some ^ (quotient × divisor) + rest, none ^ +0 }" imports "eval ok: -5",
    evalOkWith "euclidean division faileþ at zero" "use ground.tung yield +1 % +0" imports "eval ok: none",
    evalOkWith "three-way comparison distinguishes each result" "use ground.tung use ilk/product.tung yield (+0 compare +1) boþ (+1 compare +1) $boþ (+2 compare +1)" imports "eval ok: ((fore mid boþ) aft boþ)",
    evalOkWith "clamp keepeþ a value inside its bounds" "use ground.tung yield +0 clamp +10 +12" imports "eval ok: +10",
    evalOkWith "qualified duplicate values" "use ground.tung use left.tung use right.tung yield left~foo + right~foo" (duplicateImports <> imports) "eval ok: +3",
    evalOkWith "shared diamond import" "use ground.tung use left.tung use right.tung yield left~left + right~right" (diamondImports <> imports) "eval ok: +5",
    evalOkWith "diamond import keepeþ one bizen identity" "use left.tung use right.tung yield +3 left~identity" (instanceDiamondImports <> imports) "eval ok: +3",
    evalOkWith "qualified classes from different modules stay distinct" "use ground.tung use left.tung use right.tung yield +3 left~identity" (distinctClassImports <> imports) "eval ok: +4",
    evalOkWith "inherited same-named members select þe requested class" (collidingMemberPrelude ++ "bizen:ℤ first { let tag: [_:] ≔ +1 } bizen:ℤ second { let tag: [_:] ≔ +2 } bizen:ℤ both { let own: [_:] ≔ +3 } let result:[@a:*, @:a both, x: a, ℤ] ≔ x right~tag yield +1 result") (collidingMemberImports <> imports) "eval ok: +2",
    evalOkWith "a child member override doth not replace a sibling flock member" ("use ground.tung " ++ collidingMemberPrelude ++ "bizen:ℤ second { let tag: [_:] ≔ +2 } bizen:ℤ both { let tag: [_:] ≔ +10 let own: [_:] ≔ +3 } let result:[@a:*, @:a both, x: a, ℤ] ≔ (x left~tag) + (x right~tag) yield +1 result") (collidingMemberImports <> imports) "eval ok: +12",
    evalOkWith "instances in extension-sharing paths stay distinct" "use ground.tung use a.tung one use a.extra.tung two yield (+1 one~identity) + (+1 two~identity)" (samePrefixInstanceImports <> imports) "eval ok: +13",
    evalOkWith "instances beneath dotted directories stay distinct" "use ground.tung use pkg.one/identity.tung one use pkg.two/identity.tung two yield (+1 one~identity) + (+1 two~identity)" (dottedDirectoryInstanceImports <> imports) "eval ok: +13",
    evalOkWith "same-spelled imported data types dispatch through distinct instances" "use ground.tung use common.tung use left.tung use right.tung yield (left~value common~label) + (right~value common~label)" (nominalTypeInstanceImports <> imports) "eval ok: +11",
    evalOkWith "an imported transparent alias useþ its underlying instance" "use base.tung use alias.tung yield alias~value base~label" (transparentAliasInstanceImports <> imports) "eval ok: +7",
    evalOkWith "an exported alias retaineth its private nominal instance" "use opaque.tung opaque yield opaque~value opaque~label" (privateAliasInstanceImports <> imports) "eval ok: +7",
    evalOkWith "a local flock and bizen shadow an imported namesake" "use ground.tung use left.tung flock haþ_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ haþ_identity { let identity: [x:] ≔ x + +2 } yield (+1 identity) + (+1 left~identity)" (distinctClassImports <> imports) "eval ok: +5",
    evalTypeErrWith "local evidence cannot satisfy an imported namesake class" "use left.tung flock haþ_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ haþ_identity { let identity: [x:] ≔ x } let imported_use:[@a:*, @:a left~haþ_identity, x: a, a] ≔ x left~identity let local_use:[@a:*, @:a haþ_identity, x: a, a] ≔ x imported_use yield +1 local_use" (distinctClassImports <> imports),
    evalOkWith "value survives a named re-export" "use middle.tung yield value" (reexportImports <> imports) "eval ok: +7",
    evalOkWith "qualified re-export outrankeþ a shadowing local" "use ground.tung use middle.tung let value ≔ +3 yield middle~value + value" (reexportImports <> imports) "eval ok: +10",
    evalOkWith "flock bizen survives an import" "use identity.tung yield +3 identity" (identityImports <> imports) "eval ok: +3",
    evalOkWith "specific bizen outrankeþ a blanket instance" "use ground.tung flock haþ_identity:[a:*, *] { let identity:[a, a] } bizen:[@a:*, a haþ_identity] { let identity: [x:] ≔ x } bizen:ℤ haþ_identity { let identity: [x:] ≔ x + +1 } yield +1 identity" imports "eval ok: +2",
    evalOkWith "data constructor survives a named re-export" "use data_middle.tung yield +4 box" (dataReexportImports <> imports) "eval ok: (+4 box)",
    evalOkWith "constructor identity survives a different re-export path" "use data_base.tung use data_middle.tung yield match +4 data_middle~box { x data_base~box ^ x }" (dataReexportImports <> imports) "eval ok: +4",
    evalOkWith "constructor pattern surviveþ a middle-module re-export" "use middle.tung yield match middle~off { middle~off ^ +1 }" (constructorReexportImports <> imports) "eval ok: +1",
    evalOkWith "qualified constructor pattern useþ import alias" "use alias.tung yield match +4 alias~box { x alias~box ^ x }" (Map.insert "alias.tung" "show ilk _box: [a:*, *] { box: [a, a _box] }" imports) "eval ok: +4",
    evalOkWith "qualified global remaineþ distinct from record access" "use public.tung let public ≔ r{visible ≔ +9} yield public~visible" (Map.insert "public.tung" "show let visible ≔ +7" imports) "eval ok: +7",
    evalTypeErrWith "private qualified value is rejected before runtime" "use private.tung yield private~hidden" (Map.fromList [("private.tung", "let hidden ≔ +1")]),
    evalOkWith "text and unicode-list round trip" "use ground.tung yield 'λ😀' text_to_list $ list_to_text" imports "eval ok: 'λ😀'",
    evalOkWith "text converteþ to a unicode list" "use ground.tung yield 'λ😀' text_to_list" imports "eval ok: (`λ (`😀 empty ‥) ‥)",
    evalOkWith "unicode converteþ to its scalar ℕ" "use ground.tung yield `😀 unicode_to_natural" imports "eval ok: 128512",
    evalOkWith "scalar ℕ converteþ to unicode" "use ground.tung yield 128512 natural_to_unicode" imports "eval ok: (`😀 some)",
    evalOkWith "surrogate ℕ cannot become unicode" "use ground.tung yield 55296 natural_to_unicode" imports "eval ok: none",
    evalOkWith "out-of-range ℕ cannot become unicode" "use ground.tung yield 1114112 natural_to_unicode" imports "eval ok: none",
    evalOkWith "text behead exposeþ one code point" "use ground.tung use ilk/list.tung use ilk/option.tung use ilk/product.tung use flock/algebra/total/magma.tung yield match 'λ字' behead_text { (c boþ rest) option~some ^ ((c ‥ empty) list_to_text) · rest, option~none ^ '' }" imports "eval ok: 'λ字'",
    evalOkWith "empty text hath no head" "use ground.tung use ilk/option.tung yield match '' behead_text { none ^ +1, _ some ^ +0 }" imports "eval ok: +1",
    evalOkWith "generic text fold" "use ground.tung use ilk/list.tung use flock/functor/cata.tung yield ('north' ‥ ('南' ‥ empty)) …*" imports "eval ok: 'north南'",
    evalOkWith "text classes dispatch" "use ground.tung use flock/algebra/total/magma.tung yield (('a' · 'β') ≍ 'aβ') ∧ ('a' ≤ 'b')" imports "eval ok: yea",
    evalOkWith "unicode classes dispatch" "use ground.tung yield (`a ≍ `a) ∧ (`a ≤ `b)" imports "eval ok: yea",
    evalOkWith "imported bizen doth not shadow native ℤ order" "use ilk/list.tung yield +0 till +3" imports "eval ok: (+0 (+1 (+2 empty ‥) ‥) ‥)",
    evalOkWith "list map pipeline keepeþ the list functor" "use ground.tung use ilk/list.tung yield +0 till +3 $ map { x ^ x + +1 } $ map to_text" imports "eval ok: ('1' ('2' ('3' empty ‥) ‥) ‥)",
    evalOkWith "list apply calleþ its separate map instance" "use ground.tung use ilk/list.tung let values ≔ +1 ‥ (+2 ‥ empty) let functions ≔ { x ^ x + +10 } ‥ ({ x ^ x × +2 } ‥ empty) yield values apply functions" imports "eval ok: (+11 (+12 (+2 (+4 empty ‥) ‥) ‥) ‥)",
    evalOkWith "list traversal sequences option values" "use ground.tung use ilk/list.tung use ilk/option.tung use flock/functor/traverse.tung yield (+1 ‥ (+2 ‥ empty)) traverse { x ^ x option~some }" imports "eval ok: ((+1 (+2 empty ‥) ‥) some)",
    evalOkWith "fold_map combineþ mapped list values" "use ground.tung use ilk/list.tung use flock/functor/cata.tung yield (+0 till +3) fold_map to_text" imports "eval ok: '012'",
    evalOkWith "bounded conjunction folds values" "use ground.tung use ilk/list.tung use flock/functor/cata.tung yield yea ‥ (nay ‥ empty) $ …∧" imports "eval ok: nay",
    evalOkWith "bounded disjunction folds values" "use ground.tung use ilk/list.tung use flock/functor/cata.tung yield nay ‥ (yea ‥ empty) $ …∨" imports "eval ok: yea",
    evalOkWith "empty bounded conjunction useþ the upper endpoint" "use ground.tung use ilk/list.tung use flock/functor/cata.tung let values:𝟚 list ≔ empty yield values …∧" imports "eval ok: yea",
    evalOkWith "empty bounded disjunction useþ the lower endpoint" "use ground.tung use ilk/list.tung use flock/functor/cata.tung let values:𝟚 list ≔ empty yield values …∨" imports "eval ok: nay",
    evalOkWith "boolean complement negateþ" "use ground.tung yield yea ¬" imports "eval ok: nay",
    evalTypeErrWith "bounded lattice need not have a complement" "use ground.tung yield mid ¬" imports,
    evalOkWith "ℤ lattice chooseþ the lesser value" "use ground.tung yield +3 ∧ +2" imports "eval ok: +2",
    evalOkWith "total order supplieþ a distributive lattice" "use ground.tung let distribute:[@a:*, @:a lattice_distributive, x: a, y: a, z: a, a] ≔ x ∧ (y ∨ z) yield +3 distribute +2 +4" imports "eval ok: +3",
    evalOkWith "non-total powerset lattice joineþ predicates" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/functor/cata.tung let one:ℤ powerset ≔ { x ^ x ≍ +1 } let two:ℤ powerset ≔ { x ^ x ≍ +2 } let joined ≔ one ‥ (two ‥ list~empty) $ …∨ yield joined ∋ +2" imports "eval ok: yea",
    evalOkWith "empty powerset meet yieldeþ the universal set" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/functor/cata.tung let values:(ℤ powerset) list ≔ list~empty let all ≔ values …∧ yield all ∋ +42" imports "eval ok: yea",
    evalOkWith "pattern binders do not become constructor patterns" "use ground.tung use ilk/list.tung ilk bit: * { off: bit } yield +0 till +3 $ map { _ ^ off } $ map { _ ^ +1 }" imports "eval ok: (+1 (+1 (+1 empty ‥) ‥) ‥)",
    evalOkWith "control branch suspends actions" "use ground.tung yield nay branch { _ ^ +1 } { _ ^ +2 }" imports "eval ok: +2",
    evalOkWith "option maybe mapeþ present value" "use ground.tung use ilk/option.tung yield (+3 some) maybe +0 { x ^ x + +1 }" imports "eval ok: +4",
    evalOkWith "sum eiþer consumeþ selected side" "use ground.tung use ilk/sum.tung yield (+2 inject₁) eiþer { x ^ x + +1 } { y ^ y × +3 }" imports "eval ok: +6",
    evalOkWith "sum bimap mapeþ þe selected side" "use ground.tung use ilk/sum.tung let value:ℤ ∑ text ≔ +2 inject₀ yield match (value bimap { x ^ x + +1 } { text ^ text }) { x inject₀ ^ x, _ inject₁ ^ +0 }" imports "eval ok: +3",
    evalOkWith "sum functor mapeþ the right side" "use ground.tung use ilk/sum.tung let value:text ∑ ℤ ≔ +2 inject₁ yield match (value map { x ^ x + +1 }) { _ inject₀ ^ +0, x inject₁ ^ x }" imports "eval ok: +3",
    evalOkWith "sum applicative applieþ the right side" "use ground.tung use ilk/sum.tung let value:text ∑ ℤ ≔ +2 inject₁ let f:text ∑ [ℤ, ℤ] ≔ { x ^ x + +3 } inject₁ yield match value apply f { _ inject₀ ^ +0, x inject₁ ^ x }" imports "eval ok: +5",
    evalOkWith "sum monad preserveþ a left value" "use ground.tung use ilk/sum.tung let value:text ∑ ℤ ≔ 'left' inject₀ yield match (value map_flat { x ^ (x + +1) inject₁ }) { message inject₀ ^ message, x inject₁ ^ x to_text }" imports "eval ok: 'left'",
    evalOkWith "sum catamorphism foldeþ the right side" "use ground.tung use ilk/sum.tung use flock/functor/cata.tung let value:text ∑ ℤ ≔ +3 inject₁ yield value fold₁ +1 +" imports "eval ok: +4",
    evalOkWith "sum traversal preserveþ its side" "use ground.tung use ilk/sum.tung use ilk/option.tung use flock/functor/traverse.tung let value:text ∑ ℤ ≔ +3 inject₁ yield value traverse { x ^ (x + +1) some }" imports "eval ok: ((+4 inject₁) some)",
    evalOkWith "product bimap mapeþ both fields" "use ground.tung use ilk/product.tung yield (+1 boþ +2) bimap { x ^ x + +1 } { y ^ y × +3 }" imports "eval ok: (+2 +6 boþ)",
    evalOkWith "product applicative accumulateþ value context first" "use ground.tung use ilk/product.tung let value ≔ 'value:' boþ +2 let f ≔ 'function:' boþ { x ^ x + +1 } yield value apply f" imports "eval ok: ('value:function:' +3 boþ)",
    evalOkWith "product monad accumulateþ outer context first" "use ground.tung use ilk/product.tung yield ('outer:' boþ +2) map_flat { x ^ 'inner:' boþ (x + +1) }" imports "eval ok: ('outer:inner:' +3 boþ)",
    evalOkWith "product catamorphism foldeþ the second field" "use ground.tung use ilk/product.tung use flock/functor/cata.tung yield ('ignored' boþ +3) fold₁ +1 +" imports "eval ok: +4",
    evalOkWith "product traversal preserveþ the first field" "use ground.tung use ilk/product.tung use ilk/option.tung use flock/functor/traverse.tung yield ('context' boþ +3) traverse { x ^ (x + +1) some }" imports "eval ok: (('context' +4 boþ) some)",
    evalOkWith "applicative lift2 for option" "use ground.tung use ilk/option.tung yield (+1 some) lift₂ (+2 some) +" imports "eval ok: (+3 some)",
    evalOkWith "applicative keep_oþer preserveþ context order" "use ground.tung use ilk/product.tung yield ('left:' boþ +1) keep_oþer ('right:' boþ +2)" imports "eval ok: ('right:left:' +2 boþ)",
    evalOkWith "functor void for option" "use ilk/option.tung use flock/functor.tung yield (+1 some) void" imports "eval ok: (only some)",
    evalOkWith "freer bind transformeþ a completed value" (freerPrelude ++ "yield ((+3 done) bind { value ^ (value + +1) done }) run") imports "eval ok: +4",
    evalOkWith "freer lift and fold may repeat a continuation" (freerPrelude ++ "yield ask_freer run") imports "eval ok: +3",
    evalOkWith "freer bind may discard a continuation" (freerPrelude ++ "yield (ask_freer bind { _ ^ +0 done }) run") imports "eval ok: +0",
    evalOkWith "freer mapping and flattening preserve suspended requests" (freerPrelude ++ "yield (ask_freer map { value ^ value + +10 } $ map_freer { value ^ value done } $ flat_freer) run") imports "eval ok: +23",
    evalOkWith "list behead exposeþ the head and tail" "use ilk/list.tung use ilk/option.tung use ilk/product.tung yield match (+1 ‥ empty) behead { (head product~boþ _) option~some ^ head, option~none ^ +0 }" imports "eval ok: +1",
    evalOkWith "till excludeþ its stop" "use ilk/list.tung yield r{empty ≔ +2 till +2, reversed ≔ +3 till +1, two ≔ -1 till +1}" imports "eval ok: r{empty ≔ empty, reversed ≔ empty, two ≔ (-1 (+0 empty ‥) ‥)}",
    evalOkWith "list take after drop" "use ilk/list.tung yield ((+0 till +5) drop 2) take 2" imports "eval ok: (+2 (+3 empty ‥) ‥)",
    evalOkWith "list find returneþ first match" "use ground.tung use ilk/list.tung yield (+0 till +5) find { x ^ +3 ≤ x }" imports "eval ok: (+3 some)",
    evalOkWith "list indexing is zero based" "use ilk/list.tung yield (+10 ‥ (+20 ‥ empty)) at 1" imports "eval ok: (+20 some)",
    evalOkWith "list index past þe end faileþ" "use ground.tung use ilk/list.tung yield (+10 ‥ (+20 ‥ empty)) at 2" imports "eval ok: none",
    evalOkWith "natural subtraction stoppeþ at zero" "use ground.tung yield (2 - 3) + (5 - 2)" imports "eval ok: 3",
    evalOkWith "list last returneþ the final value" "use ilk/list.tung yield (+1 ‥ (+2 ‥ empty)) last" imports "eval ok: (+2 some)",
    evalOkWith "empty list hath no last value" "use ilk/list.tung let values:ℤ list ≔ empty yield values last" imports "eval ok: none",
    evalOkWith "list membership findeþ a value" "use ground.tung use ilk/list.tung yield (+1 ‥ (+2 ‥ empty)) ∋ +2" imports "eval ok: yea",
    evalOkWith "list membership rejecteþ a missing value" "use ground.tung use ilk/list.tung yield (+1 ‥ (+2 ‥ empty)) ∋ +3" imports "eval ok: nay",
    evalOkWith "list replicate useþ a nonnegative count" "use ilk/list.tung yield 'x' replicate 3" imports "eval ok: ('x' ('x' ('x' empty ‥) ‥) ‥)",
    evalOkWith "list partition preserveþ order" "use ground.tung use ilk/list.tung yield (+0 till +5) partition { x ^ +2 ≤ x }" imports "eval ok: ((+2 (+3 (+4 empty ‥) ‥) ‥) (+0 (+1 empty ‥) ‥) boþ)",
    evalOkWith "list unzip preserveþ both sides" "use ilk/list.tung use ilk/product.tung yield ((+1 boþ 'a') ‥ ((+2 boþ 'b') ‥ empty)) unzip" imports "eval ok: ((+1 (+2 empty ‥) ‥) ('a' ('b' empty ‥) ‥) boþ)",
    evalOkWith "n-ary sum addeþ a foldable collection" "use ground.tung use ilk/list.tung use flock/functor/cata.tung yield (+1 ‥ (+2 ‥ (+3 ‥ empty))) …+" imports "eval ok: +6",
    evalOkWith "n-ary sum of an empty collection is zero" "use ground.tung use ilk/list.tung use flock/functor/cata.tung let values:ℤ list ≔ empty yield values …+" imports "eval ok: +0",
    evalTypeErrWith "n-ary sum needeþ a catamorphism" "use ground.tung use flock/functor/cata.tung ilk _box: [a:*, *] { box: [a, a _box] } let value:ℤ _box ≔ +1 box yield value …+" imports,
    evalOkWith "n-ary product multiplies a foldable collection" "use ground.tung use ilk/list.tung use flock/functor/cata.tung yield (+2 ‥ (+3 ‥ (+4 ‥ empty))) …×" imports "eval ok: +24",
    evalOkWith "n-ary product of an empty collection is one" "use ground.tung use ilk/list.tung use flock/functor/cata.tung let values:ℤ list ≔ empty yield values …×" imports "eval ok: +1",
    evalTypeErrWith "n-ary product needeþ a multiplicative monoid" "use ground.tung use ilk/list.tung use flock/functor/cata.tung yield ('a' ‥ empty) …×" imports,
    evalOkWith "boolean supremal wrapper useþ disjunction" "use ground.tung use ilk/list.tung use flock/algebra/total/semigroup.tung use flock/functor/cata.tung let values ≔ (nay supremal) ‥ ((yea supremal) ‥ list~empty) yield match values …* { result supremal ^ result }" imports "eval ok: yea",
    evalOkWith "empty boolean supremal fold yieldeþ nay" "use ground.tung use ilk/list.tung use flock/algebra/total/semigroup.tung use flock/functor/cata.tung let values:(𝟚 _supremal) list ≔ list~empty yield match values …* { result supremal ^ result }" imports "eval ok: nay",
    evalOkWith "boolean infimal wrapper useþ conjunction" "use ground.tung use ilk/list.tung use flock/algebra/total/semigroup.tung use flock/functor/cata.tung let values ≔ (yea infimal) ‥ ((nay infimal) ‥ list~empty) yield match values …* { result infimal ^ result }" imports "eval ok: nay",
    evalOkWith "empty boolean infimal fold yieldeþ yea" "use ground.tung use ilk/list.tung use flock/algebra/total/semigroup.tung use flock/functor/cata.tung let values:(𝟚 _infimal) list ≔ list~empty yield match values …* { result infimal ^ result }" imports "eval ok: yea",
    evalOkWith "natural semiring computeþ with both identities" "use ground.tung use ilk/natural.tung let two:ℕ ≔ 2 let three ≔ two + 1 yield ((two × three) + one) to_ℤ" imports "eval ok: +7",
    evalOkWith "natural semiring supplieþ multiplicative monoid evidence" "use ground.tung use ilk/list.tung use ilk/natural.tung use flock/functor/cata.tung let two:ℕ ≔ 2 let three ≔ two + 1 yield ((two ‥ (three ‥ list~empty)) …×) to_ℤ" imports "eval ok: +6",
    evalOkWith "nonnegative ℤ converteþ to natural" "use ground.tung use ilk/natural.tung yield +3 to_ℕ" imports "eval ok: (3 some)",
    evalOkWith "unsigned digits are a natural" "use ground.tung yield (2 + 3) × 4" imports "eval ok: 20",
    evalOkWith "negative ℤ cannot become natural" "use ground.tung yield -1 to_ℕ" imports "eval ok: none",
    evalOkWith "complex sine of zero is zero" "use ground.tung use numeric/complex.tung yield ((0.0 +i 0.0) sine) real" imports "eval ok: 0.0",
    evalOkWith "complex cosine of zero is one" "use ground.tung use numeric/complex.tung yield ((0.0 +i 0.0) cosine) real" imports "eval ok: 1.0",
    evalOkWith "complex exponentiation scaleþ by the real exponent" "use ground.tung use numeric/complex.tung yield ((1.0 +i 0.0) exponent) real" imports "eval ok: 2.718281828459045",
    evalOkWith "complex sine of unit imaginary yieldeþ hyperbolic sine" "use ground.tung use numeric/complex.tung yield ((0.0 +i 1.0) sine) imaginary" imports "eval ok: 1.1752011936438014",
    evalOkWith "complex cosine of unit imaginary yieldeþ hyperbolic cosine" "use ground.tung use numeric/complex.tung yield ((0.0 +i 1.0) cosine) real" imports "eval ok: 1.5430806348152437",
    evalOkWith "nonempty map preserveþ the first element" "use ground.tung use ilk/list.tung use ilk/nonempty.tung yield ((+1 ‥′ (+2 ‥ empty)) map { x ^ x + +1 }) to_list" imports "eval ok: (+2 (+3 empty ‥) ‥)",
    evalOkWith "nonempty semigroup appendeþ without losing the head" "use ground.tung use ilk/list.tung use ilk/nonempty.tung use flock/algebra/total/magma.tung yield ((+1 ‥′ (+2 ‥ empty)) · (+3 ‥′ empty)) to_list" imports "eval ok: (+1 (+2 (+3 empty ‥) ‥) ‥)",
    evalOkWith "nonempty applicative applieþ every function" "use ground.tung use ilk/list.tung use ilk/nonempty.tung let values ≔ +1 ‥′ (+2 ‥ empty) let fs ≔ { x ^ x + +1 } ‥′ ({ x ^ x × +2 } ‥ empty) yield (values apply fs) to_list" imports "eval ok: (+2 (+3 (+2 (+4 empty ‥) ‥) ‥) ‥)",
    evalOkWith "nonempty monad concatenateþ every result" "use ground.tung use ilk/list.tung use ilk/nonempty.tung let values ≔ +1 ‥′ (+2 ‥ empty) yield (values map_flat { x ^ x ‥′ ((x + +10) ‥ empty) }) to_list" imports "eval ok: (+1 (+11 (+2 (+12 empty ‥) ‥) ‥) ‥)",
    evalOkWith "nonempty catamorphism visiteþ the head first" "use ground.tung use ilk/list.tung use ilk/nonempty.tung use flock/functor/cata.tung yield (+1 ‥′ (+2 ‥ empty)) fold₁ +0 +" imports "eval ok: +3",
    evalOkWith "nonempty traversal keepeþ a nonempty result" "use ground.tung use ilk/list.tung use ilk/nonempty.tung use ilk/option.tung use flock/functor/traverse.tung yield ((+1 ‥′ (+2 ‥ empty)) traverse { x ^ (x + +1) some }) map to_list" imports "eval ok: ((+2 (+3 empty ‥) ‥) some)",
    evalOkWith "nonempty membership delegateþ to list" "use ground.tung use ilk/list.tung use ilk/nonempty.tung yield (+1 ‥′ (+2 ‥ empty)) ∋ +2" imports "eval ok: yea",
    evalOkWith "table put replaceþ a key" "use ground.tung use ilk/table.tung let table ≔ (empty put 'a' +1) put 'a' +2 yield table lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "table membership dispatcheþ through inhold" "use ground.tung use ilk/table.tung let table ≔ empty put 'a' +1 yield table ∋ 'a'" imports "eval ok: yea",
    evalOkWith "table constructor may be qualified" "use ground.tung use ilk/list.tung use ilk/product.tung use ilk/table.tung yield (('a' boþ +2) ‥ list~empty) table~from_list $ lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "table rid droppeþ a key" "use ground.tung use ilk/table.tung let table ≔ empty put 'a' +1 yield (table rid 'a') lookup 'a'" imports "eval ok: none",
    evalOkWith "set put keepeþ values unique" "use ground.tung use ilk/set.tung yield ((empty put +1) put +1) to_list" imports "eval ok: (+1 empty ‥)",
    evalOkWith "set constructor may be qualified" "use ground.tung use ilk/list.tung use ilk/set.tung yield (+1 ‥ (+2 ‥ list~empty)) set~from_list $ to_list" imports "eval ok: (+1 (+2 empty ‥) ‥)",
    evalOkWith "set rid droppeþ a value" "use ground.tung use ilk/set.tung let values ≔ (empty put +1) put +2 yield (values rid +1) ∋ +1" imports "eval ok: nay",
    evalOkWith "set supremum keepeþ unique values" "use ground.tung use ilk/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +3 yield (left ∨ right) to_list" imports "eval ok: (+3 (+2 (+1 empty ‥) ‥) ‥)",
    evalOkWith "set infimum keepeþ shared values" "use ground.tung use ilk/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +3 yield (left ∧ right) to_list" imports "eval ok: (+2 empty ‥)",
    evalOkWith "set equality ignoreþ insertion order" "use ground.tung use ilk/set.tung let left ≔ (empty put +1) put +2 let right ≔ (empty put +2) put +1 yield left ≍ right" imports "eval ok: yea",
    evalOkWith "set partial order compareþ inclusion" "use ground.tung use ilk/set.tung let smaller ≔ empty put +1 let larger ≔ smaller put +2 yield (smaller ≤ larger) ∧ (smaller < larger)" imports "eval ok: yea",
    evalOkWith "set inclusion rejecteþ a proper superset" "use ground.tung use ilk/set.tung let smaller ≔ empty put +1 let larger ≔ smaller put +2 yield larger ≤ smaller" imports "eval ok: nay",
    evalOkWith "powerset addition is symmetric difference" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ { value ^ (value ≍ +1) ∨ (value ≍ +2) } let right:ℤ powerset ≔ { value ^ (value ≍ +2) ∨ (value ≍ +3) } yield ((left + right) ∋ +2)" imports "eval ok: nay",
    evalOkWith "powerset addition keepeþ an unshared member" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ { value ^ value ≍ +1 } let right:ℤ powerset ≔ { value ^ value ≍ +2 } yield ((left + right) ∋ +1)" imports "eval ok: yea",
    evalOkWith "powerset multiplication is intersection" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ { value ^ (value ≍ +1) ∨ (value ≍ +2) } let right:ℤ powerset ≔ { value ^ value ≍ +2 } yield ((left × right) ∋ +2)" imports "eval ok: yea",
    evalOkWith "powerset supremum is union" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ { value ^ value ≍ +1 } let right:ℤ powerset ≔ { value ^ value ≍ +2 } yield (left ∨ right) ∋ +2" imports "eval ok: yea",
    evalOkWith "powerset infimum is intersection" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ { value ^ (value ≍ +1) ∨ (value ≍ +2) } let right:ℤ powerset ≔ { value ^ value ≍ +2 } yield (left ∧ right) ∋ +1" imports "eval ok: nay",
    evalOkWith "powerset complement excludeþ a former member" "use ground.tung use ilk/powerset.tung let one:ℤ powerset ≔ { value ^ value ≍ +1 } let outside:ℤ powerset ≔ one ¬ yield outside ∋ +1" imports "eval ok: nay",
    evalOkWith "powerset complement includeþ a former nonmember" "use ground.tung use ilk/powerset.tung let one:ℤ powerset ≔ { value ^ value ≍ +1 } let outside:ℤ powerset ≔ one ¬ yield outside ∋ +2" imports "eval ok: yea",
    evalOkWith "powerset updates compose pointwise" "use ground.tung use ilk/powerset.tung let left:ℤ powerset ≔ (powerset~empty put +1) put +2 let right:ℤ powerset ≔ powerset~empty put +2 yield >{∧, left ∋ +1, ((left rid +1) ∋ +1) ¬, (left ∖ right) ∋ +1, ((left ∖ right) ∋ +2) ¬}" imports "eval ok: yea",
    evalOkWith "powerset subtraction is symmetric difference" "use ground.tung use ilk/powerset.tung let values:ℤ powerset ≔ { value ^ value ≍ +1 } yield ((values - values) ∋ +1)" imports "eval ok: nay",
    evalOkWith "powerset zero is empty" "use ground.tung use ilk/powerset.tung let values:ℤ powerset ≔ zero yield values ∋ +7" imports "eval ok: nay",
    evalOkWith "powerset one is universal" "use ground.tung use ilk/powerset.tung let values:ℤ powerset ≔ one yield values ∋ +7" imports "eval ok: yea",
    evalOkWith "set becomeþ a powerset" "use ground.tung use ilk/set.tung use ilk/powerset.tung let finite ≔ set~empty set~put +7 yield (finite to_powerset) ∋ +7" imports "eval ok: yea",
    evalOkWith "powerset infimal wrapper useþ intersection" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/algebra/total/semigroup.tung use flock/functor/cata.tung let one:ℤ powerset ≔ { value ^ value ≍ +1 } let both:ℤ powerset ≔ { value ^ (value ≍ +1) ∨ (value ≍ +2) } let wrapped ≔ (one infimal) ‥ ((both infimal) ‥ list~empty) yield match wrapped …* { result infimal ^ result ∋ +2 }" imports "eval ok: nay",
    evalOkWith "powerset supremal wrapper useþ union" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/algebra/total/semigroup.tung use flock/functor/cata.tung let one:ℤ powerset ≔ { value ^ value ≍ +1 } let two:ℤ powerset ≔ { value ^ value ≍ +2 } let wrapped ≔ (one supremal) ‥ ((two supremal) ‥ list~empty) yield match wrapped …* { result supremal ^ result ∋ +2 }" imports "eval ok: yea",
    evalOkWith "empty powerset wrapper monoids select þeir bounds" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/algebra/total/semigroup.tung use flock/functor/cata.tung let meets:((ℤ powerset) _infimal) list ≔ list~empty let joins:((ℤ powerset) _supremal) list ≔ list~empty yield >{∧, match meets …* { result infimal ^ result ∋ +42 }, match joins …* { result supremal ^ (result ∋ +42) ¬ }}" imports "eval ok: yea",
    evalTypeErrWith "powerset hath no arbitrarily chosen monoid" "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/algebra/total/semigroup.tung use flock/functor/cata.tung let values:(ℤ powerset) list ≔ list~empty yield values …*" imports,
    evalOkWith "table functor mapeþ values" "use ground.tung use ilk/table.tung let table ≔ (empty put 'a' +1) put 'b' +2 yield (table map { x ^ x + +10 }) lookup 'a'" imports "eval ok: (+11 some)",
    evalOkWith "table filter keepeþ matching values" "use ground.tung use ilk/table.tung use flock/functor/filter.tung let table ≔ (empty put 'a' +1) put 'b' +2 yield (table filter { x ^ +2 ≤ x }) lookup 'a'" imports "eval ok: none",
    evalOkWith "table merge preferreþ right values" "use ground.tung use ilk/table.tung let left ≔ empty put 'a' +1 let right ≔ empty put 'a' +2 yield (left merge right) lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "table adjust changeþ an existing value" "use ground.tung use ilk/table.tung let table ≔ empty put 'a' +1 yield (table adjust 'a' { x ^ x + +1 }) lookup 'a'" imports "eval ok: (+2 some)",
    evalOkWith "text operations use unicode code points" "use ground.tung use ilk/text/operation.tung yield ('aβ字' reverse_text) take_text 2" imports "eval ok: '字β'",
    evalOkWith "text size counteþ unicode code points" "use ground.tung use ilk/text/operation.tung use flock/size.tung use ilk/natural.tung yield ('aβ字' size) to_ℤ" imports "eval ok: +3",
    evalOkWith "text split and join preserve empty fields" "use ground.tung use ilk/text/operation.tung yield ('a,b,,c' split_text `,) join_wiþ_text '.'" imports "eval ok: 'a.b..c'",
    evalOkWith "text words collapse whitespace runs" "use ground.tung use ilk/text/operation.tung yield ' red\\tblue\\nred ' words_text $ join_wiþ_text '.'" imports "eval ok: 'red.blue.red'",
    evalOkWith "typed paþs join components" "use ground.tung use ilk/path.tung yield (('root' paþ) join_paþ ('leaf' paþ)) to_text" imports "eval ok: 'root/leaf'",
    evalOkWith "time spans drive async sleep" "use ground.tung use ilk/milliseconds.tung yield (0 milliseconds) sleep_for" imports "eval ok: only",
    evalOkWith "process captureþ standard output" "use ground.tung use deed/process.tung use process/result.tung use ilk/list.tung use ilk/sum.tung yield 'printf' run_process ('hello' ‥ empty) $ map { result ^ result map process_output }" imports "eval ok: ('hello' inject₁)",
    evalTypeErrWith "missing import is rejected before runtime" "use missing.tung" Map.empty,
    evalTypeErrWith "import cycle is rejected before runtime" "use left.tung" (cyclicImports <> imports),
    evalOkWith "arctan range is nonnegative" "use _foreign.tung yield 0.0 arctan_float -1.0" imports "eval ok: 4.71238898038469",
    evalOkWith "fork and wait" "use ground.tung let work:ℤ deed ≔ +42 pure yield work fork $ map_flat wait" imports "eval ok: (+42 some)",
    evalOkWith "task result may be awaited repeatedly" "use ground.tung let work:ℤ deed ≔ +21 pure yield work fork $ map_flat { task ^ (task wait) lift₂ (task wait) { a, b ^ a lift₂ b + } }" imports "eval ok: (+42 some)",
    evalOkWith "task wait may time out" "use ground.tung let work:ℤ deed ≔ (200 sleep) þen (+42 pure) yield work fork $ map_flat { task ^ task wait_for 0 }" imports "eval ok: none",
    evalOkWith "task wait_for returneþ a finished value" "use ground.tung let work:ℤ deed ≔ +42 pure yield work fork $ map_flat { task ^ task wait_for 1000 }" imports "eval ok: (+42 some)",
    evalOkWith "a cancelled task yieldeþ none" "use ground.tung let work:ℤ deed ≔ (1000 sleep) þen (+42 pure) yield work fork $ map_flat { task ^ (task cancel) þen (task wait) }" imports "eval ok: none",
    evalOkWith "cpu-bound task remaineþ cancellable" "use ground.tung let spin:ℤ deed ≔ { again ^ (only pure) map_flat { _ ^ again } } deed_fix yield spin fork $ map_flat { task ^ (task cancel) þen (task wait) }" imports "eval ok: none",
    evalTypeErrWith "an opaque task cannot be eliminated as an empty family" "use ground.tung let unwrap:[value:ℤ task, ℤ] ≔ match value {} yield +0" imports,
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
        [ ("left.tung", "use shared.tung show shared~identity"),
          ("right.tung", "use shared.tung"),
          ("shared.tung", "show flock haþ_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ haþ_identity { let identity: [x:] ≔ x }")
        ]
    distinctClassImports =
      Map.fromList
        [ ("left.tung", "use ground.tung show flock haþ_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ haþ_identity { let identity: [x:] ≔ x + +1 }"),
          ("right.tung", "use ground.tung show flock haþ_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ haþ_identity { let identity: [x:] ≔ x + +2 }")
        ]
    collidingMemberPrelude = "use left.tung use right.tung flock both:[a:*, @:a first, @:a second, *] { let own:[a, ℤ] } "
    collidingMemberImports =
      Map.fromList
        [ ("left.tung", "show flock first:[a:*, *] { let tag:[a, ℤ] }"),
          ("right.tung", "show flock second:[a:*, *] { let tag:[a, ℤ] }")
        ]
    samePrefixInstanceImports = Map.fromList [("a.tung", identityInstance 1), ("a.extra.tung", identityInstance 10)]
    dottedDirectoryInstanceImports = Map.fromList [("pkg.one/identity.tung", identityInstance 1), ("pkg.two/identity.tung", identityInstance 10)]
    identityInstance :: Int -> String
    identityInstance increment = "use ground.tung show flock haþ_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ haþ_identity { let identity: [x:] ≔ x + " ++ integerSource increment ++ " }"
    nominalTypeInstanceImports =
      Map.fromList
        [ ("common.tung", "show flock haþ_label:[a:*, *] { let label:[a, ℤ] }"),
          ("left.tung", "use common.tung show ilk _token: * { token: _token } bizen:_token common~haþ_label { let label: [_:] ≔ +1 } show let value:_token ≔ token"),
          ("right.tung", "use common.tung show ilk _token: * { token: _token } bizen:_token common~haþ_label { let label: [_:] ≔ +10 } show let value:_token ≔ token")
        ]
    transparentAliasInstanceImports =
      Map.fromList
        [ ("base.tung", "show ilk _token: * { token: _token } show flock haþ_label:[a:*, *] { let label:[a, ℤ] } bizen:_token haþ_label { let label: [_:] ≔ +7 }"),
          ("alias.tung", "use base.tung show let alias:* ≔ base~_token show let value:alias ≔ base~token")
        ]
    privateAliasInstanceImports =
      Map.singleton
        "opaque.tung"
        "ilk _secret: * { secret: _secret } show let public:* ≔ _secret show flock haþ_label:[a:*, *] { let label:[a, ℤ] } bizen:_secret haþ_label { let label: [_:] ≔ +7 } show let value:public ≔ secret"
    reexportImports = Map.fromList [("base.tung", "show let value ≔ +7"), ("middle.tung", "use base.tung show base~value")]
    identityImports = Map.fromList [("identity.tung", "show flock haþ_identity:[a:*, *] { let identity:[a, a] } bizen:ℤ haþ_identity { let identity: [x:] ≔ x }")]
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
    -- a request names its answer type; þe handler answereþ each `ask` twice.
    freerPrelude =
      "use ground.tung use ilk/freer.tung "
        ++ "ilk question: [a:*, *] { ask: ℤ question } "
        ++ "let ask_freer: question freer ℤ ≔ ask lift "
        ++ "let answer: [@ξ:*, request: ξ question, continue: [ξ, ℤ], ℤ] ≔ match request { ask ^ (+1 continue) + (+2 continue) } "
        ++ "let run: [program: question freer ℤ, ℤ] ≔ { value ^ value } fold answer program "

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
    -- awaiting one equal-duration task giveþ the other time to finish. its
    -- already-available result testeþ overlap without timing the whole compiler.
    source =
      "use ground.tung "
        ++ "let work:ℤ deed ≔ (600 sleep) þen (+21 pure) "
        ++ "yield work fork $ map_flat { left ^ work fork $ map_flat { right ^ (left wait) þen (right wait_for 100) } }"

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
optionData = "ilk option: [a:*, *] { none: a option, some: [a, a option] } "
rowData = boolData ++ "ilk row: * { stop: row, more: [𝟚, row, row] } let ones: [n: ℕ, row] ≔ match n { 0 ^ stop, k succeed ^ yea more (k ones) } "
deedPrelude = "let pure:[@a:*, a, a deed] ≔ 'deed_pure' fremmed let bind:[@a:*, @b:*, a deed, [a, b deed], b deed] ≔ 'deed_bind' fremmed "
sleepBinding = "let sleep:[ℕ, 𝟙 deed] ≔ 'sleep' fremmed "
