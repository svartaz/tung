-- static semantics: positive inference and adversarial rejection cases live here.
module Test.Type (group) where

import Control.Monad (replicateM)
import Data.List (intercalate, isInfixOf, isPrefixOf, isSuffixOf)
import Data.Map.Strict qualified as Map
import Test.Compile (compileProject, compileSource)
import Test.Harness (Group, Test, checkSource, expect, expectEq, expectPrefix, integerSource, runnableErr, typeErr, typeErrContaining, typeErrWith, typeOk, typeOkWith)
import Test.Harness qualified as Harness
import Test.QuickCheck qualified as QuickCheck
import Tung (ModuleId (..), SymbolId (..), readLibraryImports)
import Tung.Dependent qualified as Kernel
import Tung.Dependent.Source (normaliseSourceExpression, sourceDefinitions, sourceEnvironment, typeOfName)

group :: IO Group
group = do
  imports <- readLibraryImports "." >>= either fail pure
  Harness.group "type" $
    map (\(name, source) -> typeOkWith name source imports) accepted
      ++ map (\(name, source) -> typeErrWith name source imports) rejected
      ++ importCases
      ++ tableAndSetCases imports
      ++ orderCases imports
      ++ boundCases imports
      ++ numericHierarchyCases imports
      ++ kindCases
      ++ typeCompositionCases
      ++ [ typeErr "declaration annotations still check the body" "let wrong:ℤ ≔ 'text'",
           typeErr "named declaration slots retain universal checking" "let wrong:[@α:*, x:α, α] ≔ +1",
           typeErr "declaration annotation names require scope" "let wrong:[x:α, α] ≔ x"
         ]
      ++ annotationScopeCases
      ++ generatedCoverageCases
      ++ redundantCoverageCases
      ++ inferenceProperties
      ++ evidenceProperties
      ++ coverageProperties

typeCompositionCases :: [Test]
typeCompositionCases =
  [ typeOk "general type composition preserveth left and right association" "ilk pair: [a:*, b:*, *] {} ilk _box: [a:*, *] { box: a _box } let left:* ≔ <{pair, ℤ, text, unicode} let right:* ≔ >{pair, ℤ, text, unicode} let l:left _box ≔ (box:((ℤ pair text) pair unicode) _box) let r:right _box ≔ (box:(ℤ pair (text pair unicode)) _box)",
    typeOk "explicit type inputs accept composition" "ilk pair: [a:*, b:*, *] {} let keep:[@a:*, x:ℤ, ℤ] ≔ x let worth:ℤ ≔ +1 keep @>{pair, ℤ, text, unicode}"
  ]

kindCases :: [Test]
kindCases =
  [ typeOk "requirement inferreth a higher kind" "flock functor:[f:[*, *], *] {} flock atfoldsome:[f:[*, *], @:f functor, *] {}",
    typeOk "requirements reuse an owner parameter" "flock hath_≍:[a:*, *] {} flock owner:[a:*, *] { let id:[@:a hath_≍, a, a] }",
    typeOk "explicit requirement parameter may shadow a visible type" "ilk a: * {} flock hath_≍:[x:*, *] {} let keep:[@a:*, @:a hath_≍, x:a, a] ≔ x",
    typeOk "a compound requirement useth declared kinds" "flock hath_≍:[x:*, *] {} flock higher:[a:*, f:[*, *], @:(a f) hath_≍, *] { let keep:[a f, a f] }",
    typeOk "requirement parameter order supporteth explicit type input" "flock hath_≍:[a:*, *] {} bizen:ℤ hath_≍ {} let keep:[@a:*, @:a hath_≍, @b:*, x:a, _:b, a] ≔ x let result:ℤ ≔ +1 keep @ℤ @text 'x'",
    typeOk "compound requirement followeth source parameter order" "ilk _pair: [a:*, b:*, *] { pair: [a, b, a _pair b] } flock hath_≍:[a:*, *] {} bizen:(ℤ _pair text) hath_≍ {} let keep:[@a:*, @f:[*, *, *], @b:*, @:(a f b) hath_≍, x:a f b, a f b] ≔ x let result:ℤ _pair text ≔ (+1 pair 'x') keep @ℤ @_pair @text",
    typeOk "forward class requirements resolve kinds" "flock atfoldsome:[f:[*, *], @:f functor, *] {} flock functor:[f:[*, *], *] {}",
    typeOk "a child may require a parent declared later" "flock child:[a:*, f:[*, *], @:a parent f, *] {} flock parent:[a:*, f:[*, *], @:(a f) hath_≍, *] { let worth:[ℤ f, ℤ f] } flock hath_≍:[a:*, *] {}",
    typeErrContaining "a requirement's kinds must agree with its flock" "cannot unify * with [*, *]" "flock child:[a:*, f:*, @:a parent f, *] {} flock parent:[a:*, f:[*, *], *] {}",
    typeErrContaining "a requirement nameth only declared parameters" "unknown name 'a'" "flock hath_≍:[a:*, *] {} let bad:[@:a hath_≍, @a:*, x:a, a] ≔ x",
    typeOk "expected GADT index floweth through a local block" "ilk tag: [a:*, *] { integer: [ℤ, ℤ tag], word: [text, text tag] } let get:[@a:*, x:a tag, a] ≔ (let y ≔ x yield match y { n integer ^ n, s word ^ s })",
    typeOk "expected GADT index floweth through a record field" "ilk tag: [a:*, *] { integer: [ℤ, ℤ tag], word: [text, text tag] } let get:[@a:*, x:a tag, r{worth:a}] ≔ r{worth ≔ match x { n integer ^ n, s word ^ s }}",
    typeErr "an annotated strict initializer cannot refer to itself" "let worth:ℤ ≔ worth",
    typeOkWith "imported class supplyeth parameter kinds" "use classes.tung c flock atfoldsome:[f:[*, *], @:f c~functor, *] {}" (Map.singleton "classes.tung" "show flock functor:[f:[*, *], *] {}"),
    typeErr "ordinary type parameter cannot be a constructor" "let bad:[@a:*, @f:*, a f, a f] ≔ {x ^ x}",
    typeErr "requirements reject conflicting kinds" "flock hath_≍:[a:*, *] {} flock functor:[f:[*, *], *] {} flock bad:[a:*, @:a hath_≍, @:a functor, *] {}",
    typeErrContaining "a flock requirement nameth only declared parameters" "unknown name 'f'" "flock functor:[f:[*, *], *] {} flock bad:[@:f functor, *] {}"
  ]
    ++ explicitKindCases
    ++ map
      (uncurry typeErr)
      [ ("higher-kinded parameter cannot be a worth type", "ilk wrong: [f:[*, *], *] { make: [f, f wrong] }"),
        ("ordinary ilk parameter cannot be applied", "ilk box: [a:*, *] { make: [a a, a box] }"),
        ("primitive type cannot bizen a higher kind parameter", "ilk free: [f:[*, *], a:*, *] { bad: ℤ free a }"),
        ("flock member cannot use a constructor parameter as a worth type", "flock bad:[f:[*, *], *] { let wrong:[f, f] }"),
        ("flock member cannot atfold an ordinary type parameter", "flock bad:[a:*, *] { let wrong:[ℤ a, ℤ] }")
      ]

-- unused binders still have kinds. exercise the same rule through binding,
-- ascription, higher-rank input, constructors, and imported schemes.
explicitKindCases :: [Test]
explicitKindCases =
  concat
    [ [ test (label ++ " accepts its declared kind") (arrowAlias ++ source valid),
        reject (label ++ " rejects a different kind") (arrowAlias ++ source invalid)
      ]
    | (label, test, reject, source, valid, invalid) <-
        [ ("unused ordinary binder", typeOk, typeErr, \ty -> "let keep:[@a:*, x:ℤ, ℤ] ≔ x let worth:ℤ ≔ +1 keep @" ++ ty, "text", "→"),
          ("unused constructor binder", typeOk, typeErr, \ty -> "let keep:[@f:[*, *, *], x:ℤ, ℤ] ≔ x let worth:ℤ ≔ +1 keep @" ++ ty, "→", "ℤ"),
          ("ascribed binder", typeOk, typeErr, \ty -> "let keep ≔ ({x ^ x}:[@f:[*, *, *], ℤ, ℤ]) let worth:ℤ ≔ +1 keep @" ++ ty, "→", "ℤ"),
          ("higher-rank binder", typeOk, typeErr, \ty -> "let call:[f:[@g:[*, *, *], ℤ, ℤ], ℤ] ≔ +1 f @" ++ ty, "→", "ℤ"),
          ("constructor binder", typeOk, typeErr, \ty -> "ilk _box: [f:[*, *, *], *] { box: [ℤ, f _box] } let worth ≔ +1 box @" ++ ty, "→", "ℤ"),
          ("imported binder", \label source -> typeOkWith label source imports, \label source -> typeErrWith label source imports, \ty -> "use keep.tung let worth:ℤ ≔ +1 keep @" ++ ty, "→", "ℤ")
        ]
    ]
  where
    imports = Map.singleton "keep.tung" "show let keep:[@f:[*, *, *], x:ℤ, ℤ] ≔ x"
    arrowAlias = "let →:[α:*, β:*, *] ≔ [α, β] "

annotationScopeCases :: [Test]
annotationScopeCases =
  [ typeErrContaining label ("unknown name '" ++ name ++ "'") source
  | (label, name, source) <-
      [ ("annotation requireth an explicit parameter", "a", "let id:[x:a, a] ≔ x"),
        ("nested annotation cannot introduce a free variable", "b", "let atfold:[@a:*, f:[a, b], x:a, a] ≔ x"),
        ("ascription requireth a scoped type", "a", "let id: [x:] ≔ (x:a)"),
        ("type constructor variable requireth a declaration", "f", "let id:[x:ℤ f, ℤ f] ≔ x"),
        ("constructor existential requireth a declaration", "a", "ilk packed: * { pack: [a, packed] }"),
        ("instance head requireth declared variables", "a", "ilk _box: [a:*, *] { box: [a, a _box] } flock hath_≍:[a:*, *] {} bizen:(a _box) hath_≍ {}"),
        ("law requireth declared variables", "b", "flock hath_≍:[a:*, *] { let rule:[x:b, x = x] }"),
        ("instance member annotation cannot declare a free variable", "b", "flock hath_≍:[a:*, *] { let same:[a, a] } bizen:ℤ hath_≍ { let same:[x:b, b] ≔ x }")
      ]
  ]

accepted :: [(String, String)]
accepted =
  [ ("literal annotation", "let answer:ℤ ≔ +42"),
    ("an annotated function worth checks its own binder", "let sameness:[@a:*, a, a] ≔ { x ^ x } let answer:ℤ ≔ +1 sameness"),
    ("sorry hath any type", "let tale:ℤ ≔ sorry let word:text ≔ sorry let f:[@a:*, a, a] ≔ sorry"),
    ("deed is a primitive unary type constructor", "let wrap:[@a:*, x: a deed, a deed] ≔ x let nested:[(ℤ deed) deed, (ℤ deed) deed] ≔ { x ^ x }"),
    ("second-position header pattern binds an argument", "ilk _box: [a:*, *] { box: [a, a _box] } let unbox:[@a:*, x box: a _box, a] ≔ x let answer:ℤ ≔ (+1 box) unbox"),
    ("second-position header pattern binds several fields", "ilk _pair: * { pair: [ℤ, text, _pair] } let first:[tale pair word: _pair, ℤ] ≔ tale let answer:ℤ ≔ (+1 pair 'x') first"),
    ("second-position law patterns bind distinct arguments", "ilk _box: [a:*, *] { box: [a, a _box] } flock sameness:[a:*, *] { let rule:[x box:a _box, y box:a _box, x = y] }"),
    ("bare argument after named prefix is supplied by the body", "use ground.tung let eke_after:[x: ℤ, ℤ, ℤ] ≔ { y ^ x + y } let answer:ℤ ≔ +1 eke_after +2"),
    ("an inferred result followeth a written slot type", "let sameness: [x: ℤ] ≔ x let answer:ℤ ≔ +1 sameness"),
    ("inferred and written slot types mix", "use ground.tung let eke_after: [x:, y: ℤ, ℤ] ≔ x + y let answer:ℤ ≔ +1 eke_after +2"),
    ("an inferred slot with a written result", "let sameness: [x:, ℤ] ≔ x let answer:ℤ ≔ +1 sameness"),
    ("local alias constraineth its captured parameter", "use ground.tung let eke_one: [x:] ≔ (let y ≔ x let tale:ℤ ≔ y yield tale + +1) let result:ℤ ≔ +2 eke_one"),
    ("inlocal function remaineth polymorphic", "let keep: [x: ℤ] ≔ (let sameness:[@α:*, y:α, α] ≔ y let tale:ℤ ≔ +1 sameness let word:text ≔ 'x' sameness yield x)"),
    ("constructor variables remain linked through composition", "ilk _box: [a:*, *] { box: [a, a _box] } let lift:[@a:*, @f:[*, *], x: a f, a f] ≔ x let twice: [x: ℤ _box, ℤ _box] ≔ (x lift) lift let good:ℤ _box ≔ (+1 box) twice"),
    ("annotated global function may call itself", "use ground.tung let factorial:[ℕ, ℕ] ≔ { 0 ^ 1, n heir ^ (n heir) × (n factorial) } let answer:ℕ ≔ 5 factorial"),
    ("annotated local initializer seeth its preceding binding", "let answer:text ≔ (let worth ≔ +1 let worth:text ≔ match worth { +0 ^ 'zero', _ ^ 'other' } yield worth)"),
    ("arbitrary term type ascription", "use ground.tung let answer ≔ (+1 + +2: ℤ)"),
    ("polymorphic term type ascription is reusable", "let sameness ≔ ({ x ^ x }: [@a:*, a, a]) let tale:ℤ ≔ +1 sameness let word:text ≔ 'x' sameness"),
    ("ascribed anonymous function remaineth recursive", "use ground.tung let factorial ≔ ({ 0 ^ 1, n heir ^ (n heir) × (n factorial) }: [ℕ, ℕ]) let answer:ℕ ≔ 5 factorial"),
    ("type ascription preserveth a constraint", equalPrelude ++ "let alike:[@a:*, @:a hath_≍, x: a, y: a, 𝟚] ≔ (x ≍ y: 𝟚)"),
    ("unicode primitive", "let letter:unicode ≔ `a"),
    ("text primitive", "let word:text ≔ 'λ字'"),
    ("annotated polymorphic sameness", "let id:[@a:*, x: a, a] ≔ x let tale:ℤ ≔ +1 id let word:text ≔ 'x' id"),
    ("declared type parameters remain inferred at calls", "let constant:[@a:*, @b:*, x:a, _:b, a] ≔ x let tale:ℤ ≔ +1 constant 'x' let word:text ≔ 'x' constant +1"),
    ("explicit type arguments select declaration order around worth arguments", "ilk list: [a:*, *] { empty: a list } let f:[@a:*, @b:*, x:a, _:b, a] ≔ x let explicit:text ≔ 'a' f @text @(text list) empty"),
    ("declared type parameters are in scope in the body", "let id:[@a:*, x:a, a] ≔ x let forward:[@a:*, x:a, a] ≔ x id @a let answer:ℤ ≔ +1 forward @ℤ"),
    ("outer parameter scopes a local annotation", "let id:[@a:*, x:a, a] ≔ (let y:a ≔ x yield y)"),
    ("explicit higher-kinded parameters remain usable", "ilk _box: [a:*, *] { box: [a, a _box] } let id:[@f:[*, *], @a:*, x:a f, a f] ≔ x let answer:ℤ _box ≔ (+1 box) id @_box @ℤ"),
    ("law may declare a local parameter", "flock hath_≍:[a:*, *] { let rule:[@b:*, x:b, x = x] }"),
    ("method quantifiers cannot capture instance parameters", "use ground.tung ilk product: [a:*, b:*, *] { pair: [a, b, a product b] } flock mapper:[f:[*, *], *] { let warp:[@a:*, @b:*, a f, [a, b], b f] } bizen:[@a:*, (a product) mapper] { let warp: [x pair y:, f:] ≔ x pair (y f) } let good:ℤ product text ≔ (+1 pair +2) warp to_text"),
    ("instance parameter scopes explicit type inputs", "ilk _box: [a:*, *] { box: [a, a _box] } let id:[@a:*, x:a, a] ≔ x flock hath_copy:[a:*, *] { let copy:[a, a] } bizen:[@a:*, (a _box) hath_copy] { let copy: [x box:] ≔ (x id @a) box } let answer:ℤ _box ≔ (+1 box) copy"),
    ("instance method annotation scopes its own parameters", "let id:[@a:*, x:a, a] ≔ x flock owner:[a:*, *] { let copy:[@b:*, a, b, b] } bizen:ℤ owner { let copy:[@c:*, _:ℤ, x:c, c] ≔ x id @c } let answer:text ≔ +1 copy 'x'"),
    ("polymorphic argument accepteth explicit type input", "let call:[f:[@a:*, a, a], ℤ] ≔ +1 f @ℤ let id:[@a:*, x:a, a] ≔ x let answer:ℤ ≔ id call"),
    ("explicit type application may precede worth application", "let keep:[@a:*, x:a, a] ≔ x let copy ≔ (keep @ℤ) let answer:ℤ ≔ +1 copy"),
    ("a quantified ascription retaineth explicit input after let binding", "let id ≔ ({x ^ x}:[@a:*, a, a]) let answer:ℤ ≔ +1 id @ℤ"),
    ("constructor fields preserve polymorphism through a match", "ilk holder: * { hold: [[@a:*, a, a], holder] } let unpack:[h:holder, [@a:*, a, a]] ≔ match h { f hold ^ f } let id:[@a:*, x:a, a] ≔ x let answer:ℤ ≔ +1 ((id hold) unpack) @ℤ"),
    ("higher-rank argument instantiateth at distinct types", polymorphicPrelude ++ "let sameness:[@a:*, x:a, a] ≔ x let good ≔ sameness both let lambda ≔ {x ^ x} both"),
    ("rank-three annotation floweth into a lambda argument", "let run:[k:[[@a:*, a, a], ℤ], ℤ] ≔ {x ^ x} k let good:ℤ ≔ {f ^ +1 f} run"),
    ("polymorphic result is checked and reused", polymorphicPrelude ++ "let make:[_:ℤ, [@a:*, a, a]] ≔ {x ^ x} let good ≔ (+1 make) both"),
    ("explicit polymorphic ascription retaineth its quantifier", polymorphicPrelude ++ "let good ≔ ({x ^ x}:[@t1:*, t1, t1]) both"),
    ("quantified alias accepteth higher-kinded parameters", "ilk _box: [a:*, *] { box: [a, a _box] } let ⇒:[f:[*, *], g:[*, *], *] ≔ [@a:*, a f, a g] let lift:_box ⇒ _box ≔ {x ^ x}"),
    ("nested quantifiers shadow outer type variables", "let first:[@a:*, x:a, [@a:*, a, a]] ≔ {y ^ y} let good:ℤ ≔ +1 (('x' first):[@b:*, b, b])"),
    ("subscripted type variable", "let id:[@a₀:*, x: a₀, a₀] ≔ x let tale:ℤ ≔ +1 id let word:text ≔ 'x' id"),
    ("half application of a flock member", "use ground.tung let half ≔ +1 %"),
    ("type alias is transparent", "let count:* ≔ ℤ let answer:count ≔ +42"),
    ("type alias accepteth higher-kinded parameters", "ilk _box: [a:*, *] { box: [a, a _box] } let applied:[f:[*, *], a:*, *] ≔ a f let worth:_box applied ℤ ≔ +1 box"),
    ("forward type-alias chains resolve by dependency", "let first:* ≔ second let second:* ≔ _token ilk _token: * { token: _token } let good:first ≔ token"),
    ("type-alias parameters shadow nominal types", "ilk a: * { make_a: a } let wrapper:[a:*, *] ≔ a let good:ℤ wrapper ≔ +1"),
    ("data parameters shadow type aliases", "let a:* ≔ ℤ ilk _box: [a:*, *] { box: [a, a _box] } let good:text _box ≔ 'x' box"),
    ("flock parameters shadow type aliases", "let a:* ≔ ℤ flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:text hath_sameness { let sameness: [x:] ≔ x } let good:text ≔ 'x' sameness"),
    ("parameterised type alias is transparent", boolData ++ "let predicate:[a:*, *] ≔ [a, 𝟚] let member:ℤ predicate ≔ { _ ^ yea } let answer:𝟚 ≔ +1 member"),
    ("an arrow alias equaleth a unary function type", "let →:[α:*, β:*, *] ≔ [α, β] let id:[x: ℤ, ℤ] ≔ x let hath_≍:ℤ → ℤ ≔ id"),
    ("an alias applying a constructor to its parameters may stay unapplied", "let →:[α:*, β:*, *] ≔ [α, β] flock marker:[φ:[*, *, *], *] { let mark:[@α:*, α φ α, ℤ] } bizen fallback:→ marker { let mark: [_:] ≔ +1 } let worth:ℤ ≔ ({x ^ x}:[ℤ, ℤ]) mark"),
    ("curried triple function", "let pick:[x: ℤ, _: text, _: float, ℤ] ≔ x"),
    ("constructor application is curried", "ilk maybe: [a:*, *] { none: a maybe, some: [a, a maybe] } let make ≔ some let worth:ℤ maybe ≔ +1 make"),
    ("kinded data constructor hath an explicit result", "ilk _box: [a:*, *] { box: [a, a _box] } let worth:ℤ _box ≔ +1 box"),
    ("nullary constructor hath an explicit result", "ilk nat: * { zero: nat, suc: [nat, nat] } let worth:nat ≔ zero suc"),
    ("indexed constructor refines a scrutinee in each branch", "ilk tag: [a:*, *] { integer: ℤ tag, textual: text tag } let inspect:[@a:*, x:a tag, ℤ] ≔ match x { integer ^ +1, textual ^ +2 }"),
    ("indexed payload returneth the refined result type", "ilk tag: [a:*, *] { integer: [ℤ, ℤ tag], textual: [text, text tag] } let unpack:[@a:*, x:a tag, a] ≔ match x { n integer ^ n, s textual ^ s }"),
    ("higher-kinded GADT index refineth a type constructor", "ilk list: [a:*, *] { empty: a list } ilk maybe: [a:*, *] { none: a maybe } ilk tag: [f:[*, *], *] { listed: list tag, optional: maybe tag } let choose:[@f:[*, *], @a:*, x:f tag, a f] ≔ match x { listed ^ empty, optional ^ none }"),
    ("existential payload may be inspected without escaping", "ilk packed: * { pack: [@a:*, a, packed] } let discard:[x:packed, ℤ] ≔ match x { worth pack ^ +1 }"),
    ("empty type eliminator", "ilk 𝟘: * {} let initial:[@a:*, 𝟘, a] ≔ {} let eliminate:[𝟘, ℤ] ≔ initial"),
    ("multi-scrutinee exhaustive match", boolData ++ "let ok:ℤ ≔ match yea, nay { yea, yea ^ +1, yea, nay ^ +2, nay, yea ^ +3, nay, nay ^ +4 }"),
    ("alternative rows contribute to coverage", boolData ++ "let ok:ℤ ≔ match yea, nay { yea, _; _, yea ^ +1, nay, nay ^ +0 }"),
    ("overlapping wildcards cover a product", boolData ++ "let ok:ℤ ≔ match yea, nay { yea, _ ^ +1, _, yea ^ +2, nay, nay ^ +3 }"),
    ("nested exhaustive match", boolData ++ optionData ++ "let ok:ℤ ≔ match yea some { yea some ^ +1, nay some ^ +2, none ^ +0 }"),
    ("variable pattern closeth coverage", boolData ++ "let ok:ℤ ≔ match yea { yea ^ +1, other ^ +0 }"),
    ("ℤ match with fallback", "let ok:ℤ ≔ match +1 { +0 ^ +0, +1 ^ +1, _ ^ +2 }"),
    ("ℤ patterns in a function", "let classify:[ℤ, ℤ] ≔ { +0 ^ +10, -1 ^ +20, _ ^ +30 }"),
    ("text match with fallback", "let ok:ℤ ≔ match 'yes' { 'yes' ^ +1, _ ^ +0 }"),
    ("text patterns in a function", "let classify:[text, ℤ] ≔ { 'yes' ^ +1, _ ^ +0 }"),
    ("closed record", "let person:r{age: ℤ, name: text} ≔ r{name ≔ 'n', age ≔ +1}"),
    ("record access", "let person ≔ r{name ≔ 'n', age ≔ +1} let age:ℤ ≔ person.age"),
    ("chained record access", "let person ≔ r{address ≔ r{city ≔ 'kyoto'}} let city:text ≔ person.address.city"),
    ("record update changeth a field type", "let person ≔ r{worth ≔ +1} let changed:r{worth: text} ≔ r{≔ person, worth ≔ 'one'}"),
    ("record removal changeth the row", "let person ≔ r{name ≔ 'n', age ≔ +1} let public:r{name: text} ≔ r{≔ person, - age}"),
    ("flock constraint dischargeth member need", equalPrelude ++ "let alike:[@a:*, @:a hath_≍, x: a, y: a, 𝟚] ≔ x ≍ y"),
    ("bizen context dischargeth inner need", equalPrelude ++ boxData ++ "bizen:[@a:*, @:a hath_≍, (a _box) hath_≍] { let ≍: [x box:, y box:] ≔ x ≍ y }"),
    ("flock law useth its own methods", "flock hath_sameness:[a:*, *] { let sameness:[a, a] let rule:[x: a, (x sameness) = x] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x let rule ≔ sorry }"),
    ("well-typed unequal flock law remaineth checked documentation", "flock claimed:[a:*, *] { let rule:[x: ℤ, x = +0] }"),
    ("flock member carrieth its own constraint", memberConstraint ++ "bizen:maybe functor { let warp: [worth:, f:] ≔ match worth { none ^ none, x some ^ x f $ some } } bizen:maybe atfoldsome { let sheer ≔ some let atfold ≔ { x some, f some ^ x f $ some, _, _ ^ none } } bizen:maybe hath_throughwend { let throughwend: [worth:, f:] ≔ match worth { none ^ none sheer, x some ^ (x f) warp some } } let lifted:(ℤ maybe) maybe ≔ (+1 some) throughwend some"),
    ("existing parent bizen satisfieth child", classHierarchy ++ "bizen:ℤ hath_parent { let parent: [x:] ≔ x } bizen:ℤ hath_child { let child: [x:] ≔ x }"),
    ("specific bizen outranketh a blanket instance", "flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:[@a:*, a hath_sameness] { let sameness: [x:] ≔ x } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x } let ok ≔ +1 sameness"),
    ("specific bizen winneth when blanket with constraint cometh later", instancePriorityPrefix ++ specificIdentityInstance ++ blanketIdentityInstance ++ "let answer:ℤ ≔ +1 sameness"),
    ("specific bizen winneth when blanket with constraint cometh earlier", instancePriorityPrefix ++ blanketIdentityInstance ++ specificIdentityInstance ++ "let answer:ℤ ≔ +1 sameness"),
    ("inferred need chooseth specific bizen before later blanket", instancePriorityPrefix ++ specificIdentityInstance ++ blanketIdentityInstance ++ "let answer ≔ +1 sameness"),
    ("inferred need chooseth specific bizen after earlier blanket", instancePriorityPrefix ++ blanketIdentityInstance ++ specificIdentityInstance ++ "let answer ≔ +1 sameness"),
    ("child bizen may supply parent member", classHierarchy ++ "bizen:ℤ hath_child { let parent: [x:] ≔ x let child: [x:] ≔ x } let ok:ℤ ≔ +1 parent"),
    ("parametric child bizen useth its parent method", inheritedMethodHierarchy),
    ("bizen constraint may construct a parent dictionary", parentDictionaryConstraint),
    ("fremmed key entereth worth scope under another name", "let plus:[ℤ, ℤ, ℤ] ≔ 'eke_integer' fremmed let answer:ℤ ≔ +1 plus +2"),
    ("declaration-only file is runnable", "let answer ≔ +42")
  ]
  where
    instancePriorityPrefix = "flock hath_label:[a:*, *] { let label:[a, a] } flock hath_sameness:[a:*, *] { let sameness:[a, a] } "
    specificIdentityInstance = "bizen:ℤ hath_sameness { let sameness: [x:] ≔ x } "
    blanketIdentityInstance = "bizen:[@a:*, @:a hath_label, a hath_sameness] { let sameness: [x:] ≔ x label } "

rejected :: [(String, String)]
rejected =
  [ ("literal type mismatch", "let bad:ℤ ≔ 'wrong'"),
    ("a bizen defineth each law", "flock hath_sameness:[a:*, *] { let sameness:[a, a] let rule:[x: a, (x sameness) = x] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x }"),
    ("the ordinary checker accepteth only sorry as a law proof", "flock hath_sameness:[a:*, *] { let sameness:[a, a] let rule:[x: a, (x sameness) = x] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x let rule ≔ +1 }"),
    ("a bizen oweth the laws of a parent it witnesseth", "flock parent:[a:*, *] { let tag:[a, ℤ] let tagged:[x: a, (x tag) = (x tag)] } flock child:[a:*, @:a parent, *] {} bizen:ℤ child { let tag: [_:] ≔ +1 }"),
    ("deed taketh a type argument", "let bad:[deed, deed] ≔ { x ^ x }"),
    ("a deed is not its result", deedPrelude ++ "let bad:ℤ ≔ +1 sheer"),
    ("instance annotation must satisfy its interface", "flock copy:[a:*, *] { let copy:[a, a] } bizen:ℤ copy { let copy:[x:text, text] ≔ x }"),
    ("instance annotation cannot claim false polymorphism", "flock copy:[a:*, *] { let copy:[a, a] } bizen:ℤ copy { let copy:[@a:*, x:a, a] ≔ x + +1 }"),
    ("explicit type argument cannot contradict a worth argument", "let id:[@a:*, x:a, a] ≔ x let bad ≔ +1 id @text"),
    ("explicit type arguments cannot exceed declared parameters", "let id:[@a:*, x:a, a] ≔ x let bad ≔ +1 id @ℤ @text"),
    ("monomorphic function cannot satisfy a polymorphic argument", polymorphicPrelude ++ "let numeric:[x:ℤ, ℤ] ≔ x let bad ≔ numeric both"),
    ("captured inference variable cannot escape a quantified check", polymorphicPrelude ++ "let bad: [f:] ≔ f both"),
    ("a local declared quantifier cannot capture an outer variable", "let bad: [x:] ≔ (let worth:[@a:*, _:ℤ, a] ≔ x yield +1 worth @ℤ)"),
    ("explicit quantifiers are rigid even with a hole-like name", "let bad:[@t1:*, t1, t1] ≔ {_ ^ +1}"),
    ("polymorphic result cannot capture an outer argument", "let make:[@a:*, x:a, [@b:*, b, b]] ≔ {_ ^ x}"),
    ("polymorphic alias cannot merge a free and a bound variable", "let alias:[a:*, *] ≔ [@b:*, b, a] let bad:[@a:*, x:a, a alias] ≔ {y ^ y}"),
    ("a bare slot bindeth no name", "let bad:[ℤ, ℤ] ≔ +1"),
    ("a later local function shadoweth an earlier one in application", "let foo:[x: text, text] ≔ x let foo:[x: ℤ, ℤ] ≔ x + +1 let bad:text ≔ 'x' foo"),
    ("captured local alias cannot become polymorphic", "let bad: [x:] ≔ (let y ≔ x let tale:ℤ ≔ y yield tale + +1) yield 'oops' bad"),
    ("nested function cannot generalise a captured variable", "let bad: [x:] ≔ (let capture: [_:] ≔ x let tale:ℤ ≔ +0 capture let word:text ≔ +0 capture yield tale)"),
    ("constructor unification cannot change a nominal head", "ilk _box: [a:*, *] { box: [a, a _box] } ilk maybe: [a:*, *] { some: [a, a maybe] } let lift:[@a:*, @f:[*, *], x: a f, a f] ≔ x let twice: [x:] ≔ (x lift) lift let bad:ℤ maybe ≔ (+1 box) twice"),
    ("constructor result must be its data type", "ilk box: [a:*, *] { box: [a, ℤ] }"),
    ("indexed constructor cannot inhabit a different index", "ilk tag: [a:*, *] { integer: ℤ tag, textual: text tag } let wrong:ℤ tag ≔ textual"),
    ("GADT branch cannot return a wrong indexed type", "ilk tag: [a:*, *] { integer: ℤ tag, textual: text tag } let wrong:[@a:*, x:a tag, a] ≔ match x { integer ^ 'no', textual ^ 'yes' }"),
    ("existential constructor field cannot escape its branch", "ilk packed: * { pack: [@a:*, a, packed] } let leak:[@a:*, x:packed, a] ≔ match x { pack worth ^ worth }"),
    ("inferred existential constructor field cannot escape", "ilk packed: * { pack: [@a:*, a, packed] } let leak ≔ { pack worth ^ worth }"),
    ("higher-kinded existential head cannot escape", "ilk packed: * { pack: [@a:*, @g:[*, *], a g, packed] } let leak ≔ { pack worth ^ worth }"),
    ("quantification cannot hide an escaping constructor existential", "ilk packed: * { pack: [@f:[*, *], [@a:*, a f, a f], packed] } let leak ≔ { pack worth ^ worth }"),
    ("term type ascription rejecteth a mismatch", "let bad ≔ ('wrong': ℤ)"),
    ("parameterised type alias needeth its argument", "let predicate:[a:*, *] ≔ [a, ℤ] let bad: [_:, predicate] ≔ +1"),
    ("parameterised type alias rejecteth extra arguments", "let predicate:[a:*, *] ≔ [a, ℤ] let bad: [_:, ℤ predicate ℤ] ≔ +1"),
    ("recursive type aliases are rejected", "let first:* ≔ second let second:* ≔ first"),
    ("local type declarations cannot share a name", "let token:* ≔ ℤ ilk token: * { token: token }"),
    ("occurs check rejecteth self application", "let omega: [x:] ≔ x x"),
    ("occurs check followeth nested records", "let omega: [x:] ≔ r{worth ≔ x} x"),
    ("annotation cannot claim false polymorphism", "let bad:[@a:*, _: a, a] ≔ +1"),
    ("function branches must agree", boolData ++ "let bad ≔ { yea ^ +1, nay ^ 'no' }"),
    ("function cases share arity", "let bad ≔ { x ^ x, x, y ^ x }"),
    ("inhabited empty function", "let bad:[ℤ, ℤ] ≔ {}"),
    ("unannotated empty function", "let bad ≔ {}"),
    ("non-exhaustive data match", boolData ++ "let bad:ℤ ≔ match yea { yea ^ +1 }"),
    ("a natural match needeth a heir row", "let bad:[n: ℕ, ℕ] ≔ match n { 0 ^ 0, 1 ^ 1 }"),
    ("multi-match missing one product case", boolData ++ "let bad:ℤ ≔ match yea, nay { yea, yea ^ +1, yea, nay ^ +2, nay, yea ^ +3 }"),
    ("overlapping wildcards can miss a product", boolData ++ "let bad:ℤ ≔ match yea, nay { yea, _ ^ +1, _, yea ^ +2 }"),
    ("nested match misses constructor", boolData ++ optionData ++ "let bad:ℤ ≔ match yea some { yea some ^ +1, none ^ +0 }"),
    ("constructor pattern arity", optionData ++ "let bad ≔ match +1 some { some ^ +1, none ^ +0 }"),
    ("ℤ pattern needeth ℤ input", "let bad ≔ match 'one' { +1 ^ +1, _ ^ +0 }"),
    ("finite ℤ patterns are not exhaustive", "let bad ≔ match +1 { +0 ^ +0, +1 ^ +1 }"),
    ("text pattern needeth text input", "let bad ≔ match +1 { 'one' ^ +1, _ ^ +0 }"),
    ("finite text patterns are not exhaustive", "let bad ≔ match 'one' { 'one' ^ +1 }"),
    ("closed record rejecteth extra field", "let bad:r{name: text} ≔ r{name ≔ 'n', age ≔ +1}"),
    ("missing record field", "let person ≔ r{name ≔ 'n'} let bad ≔ person.age"),
    ("unknown record removal", "let person ≔ r{name ≔ 'n'} let bad ≔ r{≔ person, - age}"),
    ("record update needeth a record", "let bad ≔ r{≔ +1, worth ≔ +2}"),
    ("missing function constraint", equalPrelude ++ "let hath_≍:[@a:*, x: a, y: a, 𝟚] ≔ x ≍ y"),
    ("insufficient constraint", equalPrelude ++ "flock order_half:[a:*, @:a hath_≍, *] { let ≤:[a, a, 𝟚] } let leq:[@a:*, @:a hath_≍, x: a, y: a, 𝟚] ≔ x ≤ y"),
    ("unknown bizen class", "bizen:ℤ missing { let missing: [x:] ≔ x }"),
    ("bizen misses required member", "flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness {}"),
    ("bizen rejecteth unknown member", "flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let other: [x:] ≔ x }"),
    ("bizen member hath declared type", "flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ 'wrong' }"),
    ("duplicate bizen is incoherent", "flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x } bizen:ℤ hath_sameness { let sameness: [x:] ≔ x }"),
    ("flock law sides share a worth type", "flock bad:[a:*, *] { let rule:[x: a, x = +1] }"),
    ("flock law rejecteth an unbound worth", "flock bad:[a:*, *] { let rule:[x: a, x = missing] }"),
    ("flock law needeth must be declared", equalPrelude ++ "flock bad:[a:*, *] { let rule:[x: a, (x ≍ x) = (x ≍ x)] }"),
    ("flock member constraint sameness required at use", memberConstraint ++ "bizen:_box hath_throughwend { let throughwend: [x box:, f:] ≔ (x f) warp box } let bad:(ℤ _box) _box ≔ (+1 box) throughwend { x ^ x box }"),
    ("bizen arity followeth class", "flock convert:[a:*, b:*, *] { let convert:[a, b] } bizen:ℤ convert { let convert: [x:] ≔ x }"),
    ("fremmed key requireth a host implementation", "let unknown:[ℤ, ℤ] ≔ 'unknown' fremmed"),
    ("fremmed key must match its host signature", "let plus:[ℤ, ℤ] ≔ 'eke_integer' fremmed"),
    ("a slot pattern must name a constructor", "let bad:[some x:*, *] ≔ ℤ"),
    ("a slot cannot use a later slot's name", "let bad:[x:a, @a:*, a] ≔ x"),
    ("a nested slot cannot use a later slot's name", "let bad:[f:[a, @a:*, a], ℤ] ≔ +1"),
    ("an ilk header names its parameters", "ilk _box: [a, *] { box: [@a:*, a, a _box] }"),
    ("a flock parent requirement is written @:parent", "flock hath_+:[a, *] { let +:[@a:*, a, a, a] }"),
    ("a bizen type applieth its flock", "flock hath_≍:[a:*, *] {} bizen:hath_≍ {}"),
    ("a bizen type taketh only implicit parameters", "flock hath_≍:[a:*, *] {} bizen:[a:*, a hath_≍] {}"),
    ("a flock member is a type without a body", "flock bad:[a:*, *] { let hath_≍:[x: a, a] x }")
  ]

importCases :: [Test]
importCases =
  [ typeOkWith "shown worth and type cross a use" "use file.tung let worth:_box ≔ box" shown,
    typeErrWith "a local function shadoweth an imported one in application" "use source.tung let foo:[x: text, text] ≔ x let bad:ℤ ≔ +1 foo" shadowedFunctionImport,
    typeOkWith "qualification still reacheth a shadowed import" "use source.tung let foo:[x: text, text] ≔ x let good:ℤ ≔ +1 source~foo" shadowedFunctionImport,
    typeOkWith "default use namespace covereth terms, types, and classes" "use ilk/item.tung let worth:item~_item ≔ item~empty let hath_≍:item~_item ≔ worth let result ≔ hath_≍ item~sameness" aliased,
    typeOkWith "custom use alias surviveth resolved flock inheritance" "use dep.tung d flock hath_child:[a:*, @:a d~hath_parent, *] { let child:[a, a] }" (Map.singleton "dep.tung" "show flock hath_parent:[a:*, *] { let parent:[a, a] }"),
    expect "re-exported nominal mismatch nameth both outer aliases" $
      let message = checkSource False "use middle_left.tung left use middle_right.tung right let bad:left~_token ≔ right~worth" reexportMismatchImports
       in "left~_token" `isInfixOf` message && "right~_token" `isInfixOf` message,
    expect "concrete aliases are not rendered as applied constructors" $
      let message = checkSource False "use middle.tung outer let bad:text ≔ outer~worth" concreteAliasProjection
       in "type error:" `isPrefixOf` message && not ("outer~boxed<ℤ>" `isInfixOf` message),
    let message = checkSource False "use middle_left.tung left use middle_right.tung right let bad:[@a:*, @:a left~hath_sameness, x: a, a] ≔ x right~sameness" reexportClassImports
     in expect ("re-exported constraint mismatch: " ++ message) ("left~hath_sameness" `isInfixOf` message && "right~hath_sameness" `isInfixOf` message),
    expect "imported class-member mismatch nameth both type aliases" $
      let message = checkSource False "use left_data.tung left use right_data.tung right bizen:ℤ left~hath_maker { let maker ≔ right~token }" fixedClassTypeImports
       in "left~_token" `isInfixOf` message && "right~_token" `isInfixOf` message,
    let message = checkSource False "use dep.tung left let bad ≔ left~worth left~sameness" nestedInstanceImport
     in expect ("imported bizen constraint: " ++ message) ("left~_token" `isInfixOf` message && "left~hath_label" `isInfixOf` message),
    let message = checkSource False "use base.tung first use base.tung second let bad ≔ first~worth first~child" duplicatedInstanceImport
     in expect ("duplicate imported bizen alias: " ++ message) ("first~_token" `isInfixOf` message && "first~hath_parent" `isInfixOf` message && not ("second~" `isInfixOf` message)),
    typeOkWith "two aliases of one module shareth data sameness" "use shared_data.tung first use shared_data.tung second let left:first~_token ≔ second~token let right:second~_token ≔ first~token" sharedTypeAlias,
    typeErrWith "unknown qualified imported type is rejected" "use shared_data.tung shared let bad:shared~missing ≔ shared~token" sharedTypeAlias,
    typeErrWith "private imported type spelling stayeth hidden" "use opaque.tung opaque let bad:opaque~_secret ≔ opaque~worth" opaqueTypeImport,
    typeOkWith "worth with a private imported type remaineth inferable" "use opaque.tung opaque let worth ≔ opaque~worth" opaqueTypeImport,
    typeOkWith "type sameness surviveth a re-export" "use base_data.tung original use middle_data.tung reexport let from_original:reexport~_token ≔ original~worth let from_reexport:original~_token ≔ reexport~worth" reexportedTypeImport,
    typeOkWith "coverage separateth same-spelled imported data" "use left_token.tung left use right_token.tung right let result:ℤ ≔ match left~worth { left~zero ^ +0, left~one ^ +1 }" nominalCoverageImports,
    typeErrWith "use aliases cannot collide" "use left.tung common use right.tung common" duplicateAliases,
    typeErrWith "default use aliases cannot collide" "use ilk/item.tung use syntax/item.tung" defaultAliasCollisionImports,
    typeOkWith "explicit use aliases override colliding defaults" "use ilk/item.tung ilk_item use syntax/item.tung syntax_item let result ≔ r{left ≔ ilk_item~worth, right ≔ syntax_item~worth}" defaultAliasCollisionImports,
    expect "ambiguous imports suggest surface namespaces" $
      let message = checkSource False "use ilk/natural.tung use flock/algebra/arithmetic/semiring.tung let bad ≔ zero" ambiguousZeros
       in "natural~zero" `isInfixOf` message && "semiring~zero" `isInfixOf` message && not ("/" `isInfixOf` message),
    typeErrWith "unshown worth stayeth hidden" "use file.tung let bad ≔ hidden" shown,
    typeErrWith "a throughgo flock requireth an explicit re-export" "use middle.tung flock child:[a:*, @:a hidden, *] { let child:[a, a] }" privateClassImports,
    typeErrWith "a throughgo flock cannot be reached through its private namespace" "use middle.tung flock child:[a:*, @:a leaf~hidden, *] { let child:[a, a] }" privateClassImports,
    typeErrWith "missing use is rejected" "use missing.tung" Map.empty,
    expectPrefix "bad imported source is rejected" "parse error:" (checkSource False "use bad.tung" (Map.singleton "bad.tung" "let []")),
    typeErrWith "self use cycle is rejected" "use self.tung" (Map.singleton "self.tung" "use self.tung"),
    typeErrWith "mutual use cycle is rejected" "use left.tung" cyclic,
    runnableErr "module without main is not runnable" "let answer ≔ +42",
    expectEq "a unit deed main is runnable" "type ok" (checkSource True (deedPrelude ++ "let main:𝟙 deed ≔ only sheer") unitModule),
    expectEq "main's deed type may be inferred" "type ok" (checkSource True (deedPrelude ++ "let main ≔ only sheer") unitModule),
    runnableErr "main must be a deed" (unitData ++ "let main ≔ only"),
    runnableErr "main is not a function" (deedPrelude ++ "let main:[_: 𝟙, 𝟙 deed] ≔ { _ ^ only sheer }"),
    runnableErr "main's deed yieldeth unit" (deedPrelude ++ "let main:ℤ deed ≔ +42 sheer"),
    expectEq "reporteth a source type" (Right "[@α: *, α, α]") (inspectType "show let sameness: [@α: *, x: α, α] ≔ x" Map.empty "sameness"),
    expectEq "type display showeth a deed result" (Right "[@α: *, α, α deed]") (inspectType (deedPrelude ++ "let wrap: [@α: *, x: α, α deed] ≔ x sheer") unitModule "wrap"),
    expectEq "reporteth an unknown inspected name" (Left "unknown name 'missing'") (inspectType "let answer ≔ +42" Map.empty "missing"),
    expect "elaboration resolveth every type-class evidence hole" evidenceIsResolved,
    typeOkWith "shared diamond imports" "use left.tung use right.tung yield r{left ≔ left~left, right ≔ right~right}" sharedImports
  ]
  where
    shown = Map.fromList [("file.tung", "show ilk _box: * { box: _box } let hidden ≔ +1")]
    unitModule = Map.singleton "ilk/one.tung" "show ilk 𝟙: * { only: 𝟙 }"
    shadowedFunctionImport = Map.singleton "source.tung" "show let foo:[x: ℤ, ℤ] ≔ x"
    aliased = Map.singleton "ilk/item.tung" "show ilk _item: * { item: _item } show flock hath_sameness:[a:*, *] { let sameness:[a, a] } bizen:_item hath_sameness { let sameness: [x:] ≔ x } show let empty:_item ≔ item"
    reexportMismatchImports =
      Map.fromList
        [ ("base_left.tung", "show ilk _token: * { token: _token } show let worth:_token ≔ token"),
          ("base_right.tung", "show ilk _token: * { token: _token } show let worth:_token ≔ token"),
          ("middle_left.tung", "use base_left.tung base show base~_token show base~worth"),
          ("middle_right.tung", "use base_right.tung base show base~_token show base~worth")
        ]
    concreteAliasProjection =
      Map.fromList
        [ ("base.tung", "show ilk _box: [a:*, *] { box: [a, a _box] }"),
          ("middle.tung", "use base.tung base show let boxed:* ≔ ℤ base~_box show let worth:boxed ≔ +1 base~box")
        ]
    reexportClassImports =
      Map.fromList
        [ ("base_left.tung", "show flock hath_sameness:[a:*, *] { let sameness:[a, a] }"),
          ("base_right.tung", "show flock hath_sameness:[a:*, *] { let sameness:[a, a] }"),
          ("middle_left.tung", "use base_left.tung base_left show base_left~hath_sameness, base_left~sameness"),
          ("middle_right.tung", "use base_right.tung base_right show base_right~hath_sameness, base_right~sameness")
        ]
    fixedClassTypeImports =
      Map.fromList
        [ ("left_data.tung", "show ilk _token: * { token: _token } show flock hath_maker:[a:*, *] { let maker:_token }"),
          ("right_data.tung", "show ilk _token: * { token: _token }")
        ]
    nestedInstanceImport =
      Map.singleton
        "dep.tung"
        "show ilk _token: * { token: _token } show flock hath_sameness:[a:*, *] { let sameness:[a, a] } show flock hath_label:[a:*, *] { let label:[a, a] } bizen:[@:_token hath_label, _token hath_sameness] { let sameness: [x:] ≔ x label } show let worth:_token ≔ token"
    duplicatedInstanceImport =
      Map.singleton
        "base.tung"
        "show ilk _token: * { token: _token } show flock hath_parent:[a:*, *] { let parent:[a, ℤ] } show flock hath_child:[a:*, *] { let child:[a, ℤ] } bizen:[@:_token hath_parent, _token hath_child] { let child: [x:] ≔ x parent } show let worth:_token ≔ token"
    sharedTypeAlias = Map.singleton "shared_data.tung" "show ilk _token: * { token: _token }"
    opaqueTypeImport = Map.singleton "opaque.tung" "ilk _secret: * { secret: _secret } show let worth:_secret ≔ secret"
    reexportedTypeImport =
      Map.fromList
        [ ("base_data.tung", "show ilk _token: * { token: _token } show let worth:_token ≔ token"),
          ("middle_data.tung", "use base_data.tung base show base~_token show base~worth")
        ]
    nominalCoverageImports =
      Map.fromList
        [ ("left_token.tung", "show ilk token: * { zero: token, one: token } show let worth:token ≔ zero"),
          ("right_token.tung", "show ilk token: * { only: token } show let worth:token ≔ only")
        ]
    duplicateAliases = Map.fromList [("left.tung", "show let left ≔ +1"), ("right.tung", "show let right ≔ +2")]
    defaultAliasCollisionImports = Map.fromList [("ilk/item.tung", "show let worth ≔ +1"), ("syntax/item.tung", "show let worth ≔ +2")]
    ambiguousZeros = Map.fromList [("ilk/natural.tung", "show let zero ≔ +0"), ("flock/algebra/arithmetic/semiring.tung", "show let zero ≔ +1")]
    privateClassImports = Map.fromList [("leaf.tung", "show flock hidden:[a:*, *] { let hidden:[a, a] }"), ("middle.tung", "use leaf.tung")]
    cyclic = Map.fromList [("left.tung", "use right.tung"), ("right.tung", "use left.tung")]
    sharedImports =
      Map.fromList
        [ ("left.tung", "use shared.tung show let left ≔ shared~base"),
          ("right.tung", "use shared.tung show let right ≔ shared~base"),
          ("shared.tung", "show let base ≔ +1")
        ]
    evidenceIsResolved = evidenceResolved (equalPrelude ++ "bizen:ℤ hath_≍ { let ≍: [x:, y:] ≔ yea } let answer ≔ +1 ≍ +1")

tableAndSetCases :: Map.Map String String -> [Test]
tableAndSetCases imports =
  [ typeOkWith "table, set, and powerset may qualify shared names" (source ++ qualifiedValues) imports,
    typeErrWith "table, set, powerset, and list empty values are ambiguous bare" (source ++ "let bad ≔ empty") imports,
    typeErrWith "table and set from_list constructors are ambiguous bare" (source ++ "let values:ℤ list ≔ list~empty let bad ≔ values from_list") imports
  ]
  where
    source = "use ilk/list.tung use ilk/table.tung use ilk/set.tung use ilk/powerset.tung "
    qualifiedValues =
      "let table_worth:ℤ table text ≔ table~empty "
        ++ "let set_worth:ℤ set ≔ set~empty "
        ++ "let powerset_worth:ℤ powerset ≔ powerset~empty "
        ++ "let table_built:ℤ table text ≔ list~empty table~from_list "
        ++ "let set_built:ℤ set ≔ list~empty set~from_list"

orderCases :: Map.Map String String -> [Test]
orderCases imports =
  [ typeOkWith "half order supplieth strict comparison" (partialPrefix ++ "let good ≔ lesser < greater") imports,
    typeErrWith "half order doth not supply compare" (partialPrefix ++ "let bad ≔ lesser compare greater") imports,
    typeErrWith "half order doth not supply clamp" (partialPrefix ++ "let bad ≔ lesser clamp greater lesser") imports,
    typeOkWith "whole order inherits half operations" (totalPrefix ++ "let before ≔ lesser < greater let compared ≔ lesser compare greater let bounded ≔ lesser clamp greater greater") imports,
    typeErrWith "whole order bizen requireth its half parent" (rankPrefix ++ "bizen:rank order_whole {}") imports,
    typeOkWith "finite set supplieth half order" (setPrefix ++ "let included ≔ smaller ≤ larger") imports,
    typeErrWith "finite set doth not claim whole order" (setPrefix ++ "let bad ≔ smaller compare larger") imports
  ]
  where
    rankPrefix =
      "use ilk/two.tung use flock/hath_same.tung use flock/order/hath_at_most.tung use flock/order/order_half.tung use flock/order/order_whole.tung "
        ++ "ilk rank: * { lesser: rank, greater: rank } "
        ++ "bizen:rank hath_≍ { let ≍ ≔ { lesser, lesser ^ yea, greater, greater ^ yea, _, _ ^ nay } } "
    partialPrefix =
      rankPrefix
        ++ "bizen:rank order_half { let ≤ ≔ { lesser, _ ^ yea, greater, greater ^ yea, greater, lesser ^ nay } let ≤_eftbend ≔ sorry let ≤_whitherevenmete ≔ sorry let ≤_throughgo ≔ sorry } "
    totalPrefix = partialPrefix ++ "bizen:rank order_whole { let ≤_whole ≔ sorry } "
    setPrefix =
      "use ground.tung use ilk/set.tung "
        ++ "let smaller:ℤ set ≔ empty put +1 "
        ++ "let larger:ℤ set ≔ smaller put +2 "

boundCases :: Map.Map String String -> [Test]
boundCases imports =
  [ typeOkWith "finite orders provide both endpoints" (prefix ++ "let low:𝟚 ≔ ⟂ let high:𝟛 ≔ ⊤") imports,
    typeOkWith "natural supporteth the lower-bound fold" (prefix ++ "let worth:ℕ ≔ (0 ‥ list~empty) …∨") imports,
    typeErrWith "natural doth not claim an upper bound" (prefix ++ "let worth:ℕ ≔ (natural~zero ‥ list~empty) …∧") imports,
    typeOkWith "powerset is a bounded lattice without whole order" (powersetPrefix ++ "let joined:ℤ powerset ≔ (empty_set ‥ (full_set ‥ list~empty)) …∨") imports,
    typeErrWith "lattice doth not imply whole order" (powersetPrefix ++ "let bad ≔ empty_set ≤ full_set") imports,
    typeErrWith "float doth not claim a lawful lattice" "use ground.tung let bad:float ≔ 1.0 ∧ 2.0" imports,
    typeOkWith "infimum semilattice stands without supremum" (semilatticePrefix ++ "let good ≔ item ∧ item") imports,
    typeErrWith "infimum semilattice doth not supply supremum" (semilatticePrefix ++ "let bad ≔ item ∨ item") imports,
    typeOkWith "supremum semilattice stands without infimum" (supremumPrefix ++ "let good ≔ item ∨ item") imports,
    typeErrWith "supremum semilattice doth not supply infimum" (supremumPrefix ++ "let bad ≔ item ∧ item") imports
  ]
  where
    prefix = "use ground.tung use ilk/list.tung use ilk/natural.tung use flock/functor/catamorphism.tung "
    powersetPrefix = "use ground.tung use ilk/list.tung use ilk/powerset.tung use flock/functor/catamorphism.tung let empty_set:ℤ powerset ≔ powerset~empty let full_set:ℤ powerset ≔ all "
    semilatticePrefix = "use flock/order/semilattice_lower.tung ilk one_sided: * { item: one_sided } bizen:one_sided semilattice_lower { let ∧: [_:, _:] ≔ item let ∧_absorb ≔ sorry let ∧_commute ≔ sorry let ∧_∧ ≔ sorry } "
    supremumPrefix = "use flock/order/semilattice_upper.tung ilk one_sided: * { item: one_sided } bizen:one_sided semilattice_upper { let ∨: [_:, _:] ≔ item let ∨_absorb ≔ sorry let ∨_commute ≔ sorry let ∨_∨ ≔ sorry } "

numericHierarchyCases :: Map.Map String String -> [Test]
numericHierarchyCases imports =
  [ typeOkWith "ℤ supplieth euclidean division" "use ground.tung use ilk/maybe.tung use ilk/product.tung let deal_with_rest:[@a:*, @:a euclidean, x: a, y: a, (a ∏ a) maybe] ≔ x % y let worth:(ℤ ∏ ℤ) maybe ≔ -5 deal_with_rest +3" imports,
    typeOkWith "float retaineth raw numeric and comparison operations" "use ground.tung let sum:float ≔ 1.0 + 2.0 let quotient:float ≔ 1.0 ÷ 2.0 let compared:𝟚 ≔ 1.0 ≤ 2.0" imports,
    typeErrWith "float doth not claim exact semiring laws" "use ground.tung let twice:[@a:*, @:a semiring, x: a, a] ≔ x + x let bad:float ≔ 1.0 twice" imports,
    typeErrWith "float doth not claim exact field laws" "use ground.tung let reciprocal:[@a:*, @:a field, x: a, a] ≔ one ÷ x let bad:float ≔ 2.0 reciprocal" imports,
    typeErrWith "float doth not claim partial-order laws" "use ground.tung let eftbend:[@a:*, @:a order_half, x: a, 𝟚] ≔ x ≤ x let bad:𝟚 ≔ 1.0 eftbend" imports
  ]

generatedCoverageCases :: [Test]
generatedCoverageCases = complete ++ incomplete
  where
    complete =
      [ typeOk ("generated exhaustive match of arity " ++ show arity) (matchSource arity Nothing)
      | arity <- [1 .. 3]
      ]
    incomplete =
      [ typeErr
          ("generated match of arity " ++ show arity ++ " misses " ++ intercalate "," missing)
          (matchSource arity (Just missing))
      | arity <- [1 .. 3],
        missing <- booleanRows arity
      ]

redundantCoverageCases :: [Test]
redundantCoverageCases =
  [ typeErrContaining "duplicate ℤ pattern is reported" "case 2 is redundant" "let bad ≔ match +1 { +0 ^ +0, +0 ^ +1, _ ^ +2 }",
    typeErrContaining "duplicate text pattern is reported" "case 2 is redundant" "let bad ≔ match 'hath_≍' { 'hath_≍' ^ +0, 'hath_≍' ^ +1, _ ^ +2 }",
    typeErrContaining "wildcard hideth constructor pattern" "case 2 is redundant" (boolData ++ "let bad ≔ match yea { _ ^ +0, yea ^ +1 }"),
    typeErrContaining "constructor pattern hidden inside product" "case 3 is redundant" (boolData ++ "let bad ≔ match yea, nay { yea, _ ^ +1, nay, _ ^ +2, _, yea ^ +3 }"),
    typeErrContaining "nested constructor pattern is reported" "case 2 is redundant" (boolData ++ optionData ++ "let bad ≔ match yea some { _ some ^ +1, yea some ^ +2, none ^ +0 }")
  ]

memberConstraint :: String
memberConstraint =
  "ilk maybe: [a:*, *] { none: a maybe, some: [a, a maybe] } ilk _box: [a:*, *] { box: [a, a _box] } "
    ++ "flock functor:[f:[*, *], *] { let warp:[@a:*, @b:*, a f, [a, b], b f] } "
    ++ "flock atfoldsome:[f:[*, *], @:f functor, *] { let sheer:[@a:*, a, a f] let atfold:[@a:*, @b:*, a f, [a, b] f, b f] } "
    ++ "flock hath_throughwend:[f:[*, *], *] { let throughwend:[@m:[*, *], @:m atfoldsome, @a:*, @b:*, a f, [a, b m], (b f) m] } "

matchSource :: Int -> Maybe [String] -> String
matchSource arity omitted =
  boolData
    ++ "let checked:ℤ ≔ match "
    ++ intercalate ", " (replicate arity "yea")
    ++ " { "
    ++ intercalate
      ", "
      [ intercalate ", " row ++ " ^ " ++ integerSource result
      | (result, row) <- zip [0 :: Int ..] (booleanRows arity),
        Just row /= omitted
      ]
    ++ " }"

booleanRows :: Int -> [[String]]
booleanRows arity = replicateM arity ["yea", "nay"]

inferenceProperties :: [Test]
inferenceProperties =
  [ Harness.propertyTest "property: polymorphic sameness inferreth every generated primitive use" $
      QuickCheck.forAll (QuickCheck.listOf1 (QuickCheck.elements primitiveValues)) \values ->
        let declarations =
              [ "let worth" ++ show index ++ ":" ++ ty ++ " ≔ " ++ literal ++ " sameness "
              | (index, (ty, literal)) <- zip [(0 :: Int) ..] (take 12 values)
              ]
            source = "let sameness: [@α: *, x: α, α] ≔ x " ++ concat declarations
         in QuickCheck.counterexample source (checkSource False source Map.empty QuickCheck.=== "type ok"),
    Harness.propertyTest "property: primitive annotations rejecteth a different inferred type" $
      QuickCheck.forAll (QuickCheck.elements primitiveValues) \(actualType, literal) ->
        QuickCheck.forAll (QuickCheck.elements [ty | (ty, _) <- primitiveValues, ty /= actualType]) \claimedType ->
          let source = "let worth:" ++ claimedType ++ " ≔ " ++ literal
           in QuickCheck.counterexample source ("type error:" `isPrefixOf` checkSource False source Map.empty)
  ]

primitiveValues :: [(String, String)]
primitiveValues =
  [ ("ℕ", "42"),
    ("ℤ", "+42"),
    ("float", "1.5"),
    ("text", "'word'"),
    ("unicode", "`x")
  ]

evidenceProperties :: [Test]
evidenceProperties =
  [ Harness.propertyTest "property: unrelated bizen order keepeth evidence coherent" $
      QuickCheck.forAll (QuickCheck.shuffle evidenceCases) \orderedCases ->
        let source = equalPrelude ++ concatMap evidenceInstance orderedCases ++ concatMap evidenceUse orderedCases
         in QuickCheck.counterexample source (QuickCheck.conjoin [checkSource False source Map.empty QuickCheck.=== "type ok", QuickCheck.property (evidenceResolved source)])
  ]

data EvidenceCase = EvidenceCase String String
  deriving stock (Show)

evidenceCases :: [EvidenceCase]
evidenceCases =
  [ EvidenceCase "ℤ" "+1",
    EvidenceCase "float" "1.5",
    EvidenceCase "text" "'word'",
    EvidenceCase "unicode" "`x"
  ]

evidenceInstance :: EvidenceCase -> String
evidenceInstance (EvidenceCase ty _) = "bizen:" ++ ty ++ " hath_≍ { let ≍: [x:, y:] ≔ yea }"

evidenceUse :: EvidenceCase -> String
evidenceUse (EvidenceCase ty literal) = "let " ++ ty ++ "-evidence:𝟚 ≔ " ++ literal ++ " ≍ " ++ literal ++ " "

-- the kernel independently validateth dictionary terms; normalisation must
-- select the registered member for every generated evidence use.
evidenceResolved :: String -> Bool
evidenceResolved source = case compileSource (SourceModule "main.tung") source of
  Left _ -> False
  Right program ->
    all (either (const False) (const True) . Kernel.validate (sourceEnvironment program) . snd) (sourceDefinitions program)
      && all
        (\name -> isYea (normaliseSourceExpression program name))
        [symbolName symbol | (symbol, _) <- sourceDefinitions program, symbolName symbol == "answer" || "-evidence" `isSuffixOf` symbolName symbol]
  where
    -- universe arguments may differ; the constant is what matters.
    isYea = \case
      Right (Kernel.Global symbol _) -> symbolName symbol == "yea"
      _ -> False

inspectType :: String -> Map.Map String String -> String -> Either String String
inspectType source imports name = compileProject (SourceModule "main.tung") source imports >>= (`typeOfName` name)

coverageProperties :: [Test]
coverageProperties =
  [ Harness.propertyTest "property: generated product coverage accepteth all rows and rejecteth one omission" $
      QuickCheck.forAll (QuickCheck.chooseInt (1, 4)) \arity ->
        QuickCheck.forAll (QuickCheck.elements (booleanRows arity)) \omitted ->
          let complete = matchSource arity Nothing
              incomplete = matchSource arity (Just omitted)
           in QuickCheck.counterexample incomplete (checkSource False complete Map.empty QuickCheck.=== "type ok" QuickCheck..&&. ("type error:" `isPrefixOf` checkSource False incomplete Map.empty))
  ]

polymorphicPrelude :: String
polymorphicPrelude = "let both:[f:[@a:*, a, a], r{tale:ℤ, word:text}] ≔ r{tale≔+1 f, word≔'x' f} "

unitData, boolData, optionData, boxData, equalPrelude, classHierarchy, inheritedMethodHierarchy, parentDictionaryConstraint, deedPrelude :: String
unitData = "ilk 𝟙: * { only: 𝟙 } "
boolData = "ilk 𝟚: * { yea: 𝟚, nay: 𝟚 } "
optionData = "ilk maybe: [a:*, *] { none: a maybe, some: [a, a maybe] } "
boxData = "ilk _box: [a:*, *] { box: [a, a _box] } "
equalPrelude = boolData ++ "flock hath_≍:[a:*, *] { let ≍:[a, a, 𝟚] } "
classHierarchy = "flock hath_parent:[a:*, *] { let parent:[a, a] } flock hath_child:[a:*, @:a hath_parent, *] { let child:[a, a] } "
inheritedMethodHierarchy =
  "flock hath_·:[a:*, *] { let combine:[a, a, a] } "
    ++ "flock semigroup:[a:*, @:a hath_·, *] {} "
    ++ "ilk maybe: [a:*, *] { none: a maybe, some: [a, a maybe] } "
    ++ "bizen:[@a:*, @:a semigroup, (a maybe) semigroup] { "
    ++ "let combine ≔ { none, b ^ b, a, none ^ a, a some, b some ^ a combine b $ some } "
    ++ "}"
parentDictionaryConstraint =
  "flock hath_parent:[a:*, *] { let parent:[a, a] } "
    ++ "flock child:[a:*, @:a hath_parent, *] {} "
    ++ boxData
    ++ "bizen:[@a:*, @:a hath_parent, (a _box) hath_parent] { let parent: [x box:] ≔ (x parent) box } "
    ++ "bizen:[@a:*, @:a hath_parent, (a _box) child] {}"
deedPrelude = "use ilk/one.tung let sheer:[@a:*, a, a deed] ≔ 'deed_sheer' fremmed "
