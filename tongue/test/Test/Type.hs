-- static semantics: positive inference and adversarial rejection cases live here.
module Test.Type (group) where

import Control.Monad (replicateM)
import Data.List (intercalate, isInfixOf, isPrefixOf, isSuffixOf, permutations)
import Data.Map.Strict qualified as Map
import Test.Compile (compileProject, compileSource)
import Test.Harness (Group, Test, checkSource, expect, expectEq, expectPrefix, integerSource, runnableErr, typeErr, typeErrContaining, typeErrWith, typeOk, typeOkWith)
import Test.Harness qualified as Harness
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
      ++ annotationScopeCases
      ++ redundantCoverageCases
      ++ primitiveCases
      ++ evidenceCases
      ++ coverageCases

typeCompositionCases :: [Test]
typeCompositionCases =
  [ typeOk "general type composition preserveth left and right association" "type pair: [a:*, b:*, *] {} type _box: [a:*, *] { box: a _box } let left:* ≔ <{pair, ℤ, string, unicode} let right:* ≔ >{pair, ℤ, string, unicode} let l:left _box ≔ (box:((ℤ pair string) pair unicode) _box) let r:right _box ≔ (box:(ℤ pair (string pair unicode)) _box)",
    typeOk "explicit type inputs accept composition" "type pair: [a:*, b:*, *] {} let keep:[@a:*, x:ℤ, ℤ] ≔ x let value:ℤ ≔ +1 keep @>{pair, ℤ, string, unicode}"
  ]

kindCases :: [Test]
kindCases =
  [ typeOk "requirement inferreth a higher kind" "class functor:[f:[*, *], *] {} class applicative:[f:[*, *], @:f functor, *] {}",
    typeOk "requirements reuse an owner parameter" "class hath_≍:[a:*, *] {} class owner:[a:*, *] { let id:[@:a hath_≍, a, a] }",
    typeOk "explicit requirement parameter may shadow a visible type" "type a: * {} class hath_≍:[x:*, *] {} let keep:[@a:*, @:a hath_≍, x:a, a] ≔ x",
    typeOk "a compound requirement useth declared kinds" "class hath_≍:[x:*, *] {} class higher:[a:*, f:[*, *], @:(a f) hath_≍, *] { let keep:[a f, a f] }",
    typeOk "requirement parameter order supporteth explicit type input" "class hath_≍:[a:*, *] {} bizen:ℤ hath_≍ {} let keep:[@a:*, @:a hath_≍, @b:*, x:a, _:b, a] ≔ x let outcome:ℤ ≔ +1 keep @ℤ @string 'x'",
    typeOk "compound requirement followeth source parameter order" "type _pair: [a:*, b:*, *] { pair: [a, b, a _pair b] } class hath_≍:[a:*, *] {} bizen:(ℤ _pair string) hath_≍ {} let keep:[@a:*, @f:[*, *, *], @b:*, @:(a f b) hath_≍, x:a f b, a f b] ≔ x let outcome:ℤ _pair string ≔ (+1 pair 'x') keep @ℤ @_pair @string",
    typeOk "forward class requirements resolve kinds" "class applicative:[f:[*, *], @:f functor, *] {} class functor:[f:[*, *], *] {}",
    typeOk "a child may require a parent declared later" "class child:[a:*, f:[*, *], @:a parent f, *] {} class parent:[a:*, f:[*, *], @:(a f) hath_≍, *] { let value:[ℤ f, ℤ f] } class hath_≍:[a:*, *] {}",
    typeErrContaining "a requirement's kinds must agree with its class" "cannot unify * with [*, *]" "class child:[a:*, f:*, @:a parent f, *] {} class parent:[a:*, f:[*, *], *] {}",
    typeErrContaining "a requirement nameth only declared parameters" "unknown name 'a'" "class hath_≍:[a:*, *] {} let bad:[@:a hath_≍, @a:*, x:a, a] ≔ x",
    typeOk "expected GADT index floweth through a local block" "type tag: [a:*, *] { integer: [ℤ, ℤ tag], word: [string, string tag] } let get:[@a:*, x:a tag, a] ≔ (let y ≔ x yield match y { n integer ^ n, s word ^ s })",
    typeOk "expected GADT index floweth through a field" "type tag: [a:*, *] { integer: [ℤ, ℤ tag], word: [string, string tag] } type box: [a:*, *] { box_of: [value: a, a box] } let get:[@a:*, x:a tag, a box] ≔ (match x { n integer ^ n, s word ^ s }) box_of",
    typeErr "an annotated strict initializer cannot refer to itself" "let value:ℤ ≔ value",
    typeOkWith "imported class supplyeth parameter kinds" "bring classes.tung c class applicative:[f:[*, *], @:f c~functor, *] {}" (Map.singleton "classes.tung" "show class functor:[f:[*, *], *] {}"),
    typeErr "ordinary type parameter cannot be a constructor" "let bad:[@a:*, @f:*, a f, a f] ≔ {x ^ x}",
    typeErr "requirements reject conflicting kinds" "class hath_≍:[a:*, *] {} class functor:[f:[*, *], *] {} class bad:[a:*, @:a hath_≍, @:a functor, *] {}",
    typeErrContaining "a class requirement nameth only declared parameters" "unknown name 'f'" "class functor:[f:[*, *], *] {} class bad:[@:f functor, *] {}"
  ]
    ++ explicitKindCases
    ++ map
      (uncurry typeErr)
      [ ("higher-kinded parameter cannot be a value type", "type wrong: [f:[*, *], *] { make: [f, f wrong] }"),
        ("ordinary type parameter cannot be applied", "type box: [a:*, *] { make: [a a, a box] }"),
        ("primitive type cannot bizen a higher kind parameter", "type free: [f:[*, *], a:*, *] { bad: ℤ free a }"),
        ("class member cannot use a constructor parameter as a value type", "class bad:[f:[*, *], *] { let wrong:[f, f] }"),
        ("class member cannot apply an ordinary type parameter", "class bad:[a:*, *] { let wrong:[ℤ a, ℤ] }")
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
        [ ("unused ordinary binder", typeOk, typeErr, \ty -> "let keep:[@a:*, x:ℤ, ℤ] ≔ x let value:ℤ ≔ +1 keep @" ++ ty, "string", "→"),
          ("unused constructor binder", typeOk, typeErr, \ty -> "let keep:[@f:[*, *, *], x:ℤ, ℤ] ≔ x let value:ℤ ≔ +1 keep @" ++ ty, "→", "ℤ"),
          ("ascribed binder", typeOk, typeErr, \ty -> "let keep ≔ ({x ^ x}:[@f:[*, *, *], ℤ, ℤ]) let value:ℤ ≔ +1 keep @" ++ ty, "→", "ℤ"),
          ("higher-rank binder", typeOk, typeErr, \ty -> "let call:[f:[@g:[*, *, *], ℤ, ℤ], ℤ] ≔ +1 f @" ++ ty, "→", "ℤ"),
          ("constructor binder", typeOk, typeErr, \ty -> "type _box: [f:[*, *, *], *] { box: [ℤ, f _box] } let value ≔ +1 box @" ++ ty, "→", "ℤ"),
          ("imported binder", \label source -> typeOkWith label source imports, \label source -> typeErrWith label source imports, \ty -> "bring keep.tung let value:ℤ ≔ +1 keep @" ++ ty, "→", "ℤ")
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
        ("nested annotation cannot introduce a free variable", "b", "let apply:[@a:*, f:[a, b], x:a, a] ≔ x"),
        ("ascription requireth a scoped type", "a", "let id: [x:] ≔ (x:a)"),
        ("type constructor variable requireth a declaration", "f", "let id:[x:ℤ f, ℤ f] ≔ x"),
        ("constructor existential requireth a declaration", "a", "type packed: * { pack: [a, packed] }"),
        ("instance head requireth declared variables", "a", "type _box: [a:*, *] { box: [a, a _box] } class hath_≍:[a:*, *] {} bizen:(a _box) hath_≍ {}"),
        ("law requireth declared variables", "b", "bring is.tung class hath_≍:[a:*, *] { let rule:[x:b, x = x] }"),
        ("instance member annotation cannot declare a free variable", "b", "class hath_≍:[a:*, *] { let same:[a, a] } bizen:ℤ hath_≍ { let same:[x:b, b] ≔ x }")
      ]
  ]

accepted :: [(String, String)]
accepted =
  [ ("literal annotation", "let answer:ℤ ≔ +42"),
    ("an annotated function value checks its own binder", "let identity:[@a:*, a, a] ≔ { x ^ x } let answer:ℤ ≔ +1 identity"),
    ("sorry hath any type", "let tale:ℤ ≔ sorry let word:string ≔ sorry let f:[@a:*, a, a] ≔ sorry"),
    ("effect is a primitive unary type constructor", "let wrap:[@a:*, x: a effect, a effect] ≔ x let nested:[(ℤ effect) effect, (ℤ effect) effect] ≔ { x ^ x }"),
    ("second-position header pattern binds an argument", "type _box: [a:*, *] { box: [a, a _box] } let unbox:[@a:*, x box: a _box, a] ≔ x let answer:ℤ ≔ (+1 box) unbox"),
    ("second-position header pattern binds several fields", "type _pair: * { pair: [ℤ, string, _pair] } let first:[tale pair word: _pair, ℤ] ≔ tale let answer:ℤ ≔ (+1 pair 'x') first"),
    ("law types may match distinct arguments", "bring is.tung type _box: [a:*, *] { box: [a, a _box] } class identity:[a:*, *] { let rule:[left:a _box, right:a _box, match left, right { x box, y box ^ x = y }] }"),
    ("bare argument after named prefix is supplied by the body", "bring often.tung let add_after:[x: ℤ, ℤ, ℤ] ≔ { y ^ x + y } let answer:ℤ ≔ +1 add_after +2"),
    ("an inferred result followeth a written slot type", "let identity: [x: ℤ] ≔ x let answer:ℤ ≔ +1 identity"),
    ("inferred and written slot types mix", "bring often.tung let add_after: [x:, y: ℤ, ℤ] ≔ x + y let answer:ℤ ≔ +1 add_after +2"),
    ("an inferred slot with a written result", "let identity: [x:, ℤ] ≔ x let answer:ℤ ≔ +1 identity"),
    ("local alias constraineth its captured parameter", "bring often.tung let add_one: [x:] ≔ (let y ≔ x let tale:ℤ ≔ y yield tale + +1) let outcome:ℤ ≔ +2 add_one"),
    ("inlocal function remaineth polymorphic", "let keep: [x: ℤ] ≔ (let identity:[@α:*, y:α, α] ≔ y let tale:ℤ ≔ +1 identity let word:string ≔ 'x' identity yield x)"),
    ("constructor variables remain linked through composition", "type _box: [a:*, *] { box: [a, a _box] } let lift:[@a:*, @f:[*, *], x: a f, a f] ≔ x let twice: [x: ℤ _box, ℤ _box] ≔ (x lift) lift let good:ℤ _box ≔ (+1 box) twice"),
    ("annotated global function may call itself", "bring often.tung let factorial:[ℕ, ℕ] ≔ { 0 ^ 1, n next ^ (n next) · (n factorial) } let answer:ℕ ≔ 5 factorial"),
    ("annotated local initializer seeth its preceding binding", "let answer:string ≔ (let value ≔ +1 let value:string ≔ match value { +0 ^ 'zero', _ ^ 'other' } yield value)"),
    ("arbitrary term type ascription", "bring often.tung let answer ≔ (+1 + +2: ℤ)"),
    ("polymorphic term type ascription is reusable", "let identity ≔ ({ x ^ x }: [@a:*, a, a]) let tale:ℤ ≔ +1 identity let word:string ≔ 'x' identity"),
    ("ascribed anonymous function remaineth recursive", "bring often.tung let factorial ≔ ({ 0 ^ 1, n next ^ (n next) · (n factorial) }: [ℕ, ℕ]) let answer:ℕ ≔ 5 factorial"),
    ("type ascription preserveth a constraint", equalPrelude ++ "let alike:[@a:*, @:a hath_≍, x: a, y: a, 𝟚] ≔ (x ≍ y: 𝟚)"),
    ("declared type parameters remain inferred at calls", "let constant:[@a:*, @b:*, x:a, _:b, a] ≔ x let tale:ℤ ≔ +1 constant 'x' let word:string ≔ 'x' constant +1"),
    ("explicit type arguments select declaration order around value arguments", "type list: [a:*, *] { empty: a list } let f:[@a:*, @b:*, x:a, _:b, a] ≔ x let explicit:string ≔ 'a' f @string @(string list) empty"),
    ("declared type parameters are in scope in the body", "let id:[@a:*, x:a, a] ≔ x let forward:[@a:*, x:a, a] ≔ x id @a let answer:ℤ ≔ +1 forward @ℤ"),
    ("outer parameter scopes a local annotation", "let id:[@a:*, x:a, a] ≔ (let y:a ≔ x yield y)"),
    ("explicit higher-kinded parameters remain usable", "type _box: [a:*, *] { box: [a, a _box] } let id:[@f:[*, *], @a:*, x:a f, a f] ≔ x let answer:ℤ _box ≔ (+1 box) id @_box @ℤ"),
    ("law may declare a local parameter", "bring is.tung class hath_≍:[a:*, *] { let rule:[@b:*, x:b, x = x] }"),
    ("method quantifiers cannot capture instance parameters", "bring often.tung type product: [a:*, b:*, *] { pair: [a, b, a product b] } class mapper:[f:[*, *], *] { let map:[@a:*, @b:*, a f, [a, b], b f] } bizen:[@a:*, (a product) mapper] { let map: [x pair y:, f:] ≔ x pair (y f) } let good:ℤ product string ≔ (+1 pair +2) map to_string"),
    ("instance parameter scopes explicit type inputs", "type _box: [a:*, *] { box: [a, a _box] } let id:[@a:*, x:a, a] ≔ x class hath_copy:[a:*, *] { let copy:[a, a] } bizen:[@a:*, (a _box) hath_copy] { let copy: [x box:] ≔ (x id @a) box } let answer:ℤ _box ≔ (+1 box) copy"),
    ("instance method annotation scopes its own parameters", "let id:[@a:*, x:a, a] ≔ x class owner:[a:*, *] { let copy:[@b:*, a, b, b] } bizen:ℤ owner { let copy:[@c:*, _:ℤ, x:c, c] ≔ x id @c } let answer:string ≔ +1 copy 'x'"),
    ("polymorphic argument accepteth explicit type input", "let call:[f:[@a:*, a, a], ℤ] ≔ +1 f @ℤ let id:[@a:*, x:a, a] ≔ x let answer:ℤ ≔ id call"),
    ("explicit type application may precede value application", "let keep:[@a:*, x:a, a] ≔ x let copy ≔ (keep @ℤ) let answer:ℤ ≔ +1 copy"),
    ("a quantified ascription retaineth explicit input after let binding", "let id ≔ ({x ^ x}:[@a:*, a, a]) let answer:ℤ ≔ +1 id @ℤ"),
    ("constructor fields preserve polymorphism through a match", "type holder: * { hold: [[@a:*, a, a], holder] } let unpack:[h:holder, [@a:*, a, a]] ≔ match h { f hold ^ f } let id:[@a:*, x:a, a] ≔ x let answer:ℤ ≔ +1 ((id hold) unpack) @ℤ"),
    ("higher-rank argument instantiateth at distinct types", polymorphicPrelude ++ "let identity:[@a:*, x:a, a] ≔ x let good ≔ identity both let lambda ≔ {x ^ x} both"),
    ("rank-three annotation floweth into a lambda argument", "let run:[k:[[@a:*, a, a], ℤ], ℤ] ≔ {x ^ x} k let good:ℤ ≔ {f ^ +1 f} run"),
    ("a hole maketh its application a function of each hole", "type nat: * { zero: nat, succ: [nat, nat] } let first:[nat, nat, nat] ≔ {a, _ ^ a} let pick:[nat, nat] ≔ zero first _ let both:[nat, nat, nat] ≔ _ first _"),
    ("polymorphic result is checked and reused", polymorphicPrelude ++ "let make:[_:ℤ, [@a:*, a, a]] ≔ {x ^ x} let good ≔ (+1 make) both"),
    ("explicit polymorphic ascription retaineth its quantifier", polymorphicPrelude ++ "let good ≔ ({x ^ x}:[@t1:*, t1, t1]) both"),
    ("quantified alias accepteth higher-kinded parameters", "type _box: [a:*, *] { box: [a, a _box] } let ⇒:[f:[*, *], g:[*, *], *] ≔ [@a:*, a f, a g] let lift:_box ⇒ _box ≔ {x ^ x}"),
    ("nested quantifiers shadow outer type variables", "let first:[@a:*, x:a, [@a:*, a, a]] ≔ {y ^ y} let good:ℤ ≔ +1 (('x' first):[@b:*, b, b])"),
    ("subscripted type variable", "let id:[@a₀:*, x: a₀, a₀] ≔ x let tale:ℤ ≔ +1 id let word:string ≔ 'x' id"),
    ("half application of a class member", "bring often.tung let half ≔ +1 %"),
    ("type alias is transparent", "let count:* ≔ ℤ let answer:count ≔ +42"),
    ("type alias accepteth higher-kinded parameters", "type _box: [a:*, *] { box: [a, a _box] } let applied:[f:[*, *], a:*, *] ≔ a f let value:_box applied ℤ ≔ +1 box"),
    ("forward type-alias chains resolve by dependency", "let first:* ≔ second let second:* ≔ _token type _token: * { token: _token } let good:first ≔ token"),
    ("type-alias parameters shadow nominal types", "type a: * { make_a: a } let wrapper:[a:*, *] ≔ a let good:ℤ wrapper ≔ +1"),
    ("data parameters shadow type aliases", "let a:* ≔ ℤ type _box: [a:*, *] { box: [a, a _box] } let good:string _box ≔ 'x' box"),
    ("class parameters shadow type aliases", "let a:* ≔ ℤ class hath_identity:[a:*, *] { let identity:[a, a] } bizen:string hath_identity { let identity: [x:] ≔ x } let good:string ≔ 'x' identity"),
    ("parameterised type alias is transparent", boolData ++ "let predicate:[a:*, *] ≔ [a, 𝟚] let member:ℤ predicate ≔ { _ ^ yea } let answer:𝟚 ≔ +1 member"),
    ("an arrow alias equaleth a unary function type", "let →:[α:*, β:*, *] ≔ [α, β] let id:[x: ℤ, ℤ] ≔ x let hath_≍:ℤ → ℤ ≔ id"),
    ("an alias applying a constructor to its parameters may stay unapplied", "let →:[α:*, β:*, *] ≔ [α, β] class marker:[φ:[*, *, *], *] { let mark:[@α:*, α φ α, ℤ] } bizen fallback:→ marker { let mark: [_:] ≔ +1 } let value:ℤ ≔ ({x ^ x}:[ℤ, ℤ]) mark"),
    ("constructor application is curried", "type optional: [a:*, *] { none: a optional, some: [a, a optional] } let make ≔ some let value:ℤ optional ≔ +1 make"),
    ("indexed constructor refines a scrutinee in each branch", "type tag: [a:*, *] { integer: ℤ tag, textual: string tag } let inspect:[@a:*, x:a tag, ℤ] ≔ match x { integer ^ +1, textual ^ +2 }"),
    ("indexed payload returneth the refined result type", "type tag: [a:*, *] { integer: [ℤ, ℤ tag], textual: [string, string tag] } let unpack:[@a:*, x:a tag, a] ≔ match x { n integer ^ n, s textual ^ s }"),
    ("higher-kinded GADT index refineth a type constructor", "type list: [a:*, *] { empty: a list } type optional: [a:*, *] { none: a optional } type tag: [f:[*, *], *] { listed: list tag, optioned: optional tag } let choose:[@f:[*, *], @a:*, x:f tag, a f] ≔ match x { listed ^ empty, optioned ^ none }"),
    ("existential payload may be inspected without escaping", "type packed: * { pack: [@a:*, a, packed] } let discard:[x:packed, ℤ] ≔ match x { value pack ^ +1 }"),
    ("empty type eliminator", "type 𝟘: * {} let initial:[@a:*, 𝟘, a] ≔ {} let eliminate:[𝟘, ℤ] ≔ initial"),
    ("alternative rows contribute to coverage", boolData ++ "let ok:ℤ ≔ match yea, nay { yea, _; _, yea ^ +1, nay, nay ^ +0 }"),
    ("overlapping wildcards cover a product", boolData ++ "let ok:ℤ ≔ match yea, nay { yea, _ ^ +1, _, yea ^ +2, nay, nay ^ +3 }"),
    ("nested exhaustive match", boolData ++ optionData ++ "let ok:ℤ ≔ match yea some { yea some ^ +1, nay some ^ +2, none ^ +0 }"),
    ("variable pattern closeth coverage", boolData ++ "let ok:ℤ ≔ match yea { yea ^ +1, other ^ +0 }"),
    ("ℤ match with fallback", "let ok:ℤ ≔ match +1 { +0 ^ +0, +1 ^ +1, _ ^ +2 }"),
    ("string match with fallback", "let ok:ℤ ≔ match 'yes' { 'yes' ^ +1, _ ^ +0 }"),
    ("class constraint dischargeth member need", equalPrelude ++ "let alike:[@a:*, @:a hath_≍, x: a, y: a, 𝟚] ≔ x ≍ y"),
    ("bizen context dischargeth inner need", equalPrelude ++ boxData ++ "bizen:[@a:*, @:a hath_≍, (a _box) hath_≍] { let ≍: [x box:, y box:] ≔ x ≍ y }"),
    ("class law useth its own methods", "bring is.tung class hath_identity:[a:*, *] { let identity:[a, a] let rule:[x: a, (x identity) = x] } bizen:ℤ hath_identity { let identity: [x:] ≔ x let rule ≔ sorry }"),
    ("a class may require a proposition that its instances must prove", "bring is.tung class claimed:[a:*, *] { let rule:[x: ℤ, x = +0] }"),
    ("class member carrieth its own constraint", memberConstraint ++ "bizen:optional functor { let map: [value:, f:] ≔ match value { none ^ none, x some ^ x f $ some } } bizen:optional applicative { let sheer ≔ some let apply ≔ { x some, f some ^ x f $ some, _, _ ^ none } } bizen:optional hath_traverse { let traverse: [value:, f:] ≔ match value { none ^ none sheer, x some ^ (x f) map some } } let lifted:(ℤ optional) optional ≔ (+1 some) traverse some"),
    ("existing parent bizen satisfieth child", classHierarchy ++ "bizen:ℤ hath_parent { let parent: [x:] ≔ x } bizen:ℤ hath_child { let child: [x:] ≔ x }"),
    ("child bizen may supply parent member", classHierarchy ++ "bizen:ℤ hath_child { let parent: [x:] ≔ x let child: [x:] ≔ x } let ok:ℤ ≔ +1 parent"),
    ("parametric child bizen useth its parent method", inheritedMethodHierarchy),
    ("bizen constraint may construct a parent dictionary", parentDictionaryConstraint),
    ("foreign key entereth value scope under another name", "let plus:[ℤ, ℤ, ℤ] ≔ 'add_integer' foreign let answer:ℤ ≔ +1 plus +2")
  ]

rejected :: [(String, String)]
rejected =
  [ ("literal type mismatch", "let bad:ℤ ≔ 'wrong'"),
    ("a hole belongeth to its innermost application", "type nat: * { zero: nat, succ: [nat, nat] } let bad:[nat, nat] ≔ (_ succ) succ"),
    ("a lone hole is no term", "type nat: * { zero: nat } let bad:nat ≔ _"),
    ("a bizen oweth the laws of a parent it witnesseth", "bring is.tung class parent:[a:*, *] { let tag:[a, ℤ] let tagged:[x: a, (x tag) = (x tag)] } class child:[a:*, @:a parent, *] {} bizen:ℤ child { let tag: [_:] ≔ +1 }"),
    ("effect taketh a type argument", "let bad:[effect, effect] ≔ { x ^ x }"),
    ("an effect is not its result", effectPrelude ++ "let bad:ℤ ≔ +1 sheer"),
    ("instance annotation must satisfy its interface", "class copy:[a:*, *] { let copy:[a, a] } bizen:ℤ copy { let copy:[x:string, string] ≔ x }"),
    ("instance annotation cannot claim false polymorphism", "class copy:[a:*, *] { let copy:[a, a] } bizen:ℤ copy { let copy:[@a:*, x:a, a] ≔ x + +1 }"),
    ("explicit type argument cannot contradict a value argument", "let id:[@a:*, x:a, a] ≔ x let bad ≔ +1 id @string"),
    ("explicit type arguments cannot exceed declared parameters", "let id:[@a:*, x:a, a] ≔ x let bad ≔ +1 id @ℤ @string"),
    ("monomorphic function cannot satisfy a polymorphic argument", polymorphicPrelude ++ "let numeric:[x:ℤ, ℤ] ≔ x let bad ≔ numeric both"),
    ("captured inference variable cannot escape a quantified check", polymorphicPrelude ++ "let bad: [f:] ≔ f both"),
    ("a local declared quantifier cannot capture an outer variable", "let bad: [x:] ≔ (let value:[@a:*, _:ℤ, a] ≔ x yield +1 value @ℤ)"),
    ("explicit quantifiers are rigid even with a hole-like name", "let bad:[@t1:*, t1, t1] ≔ {_ ^ +1}"),
    ("polymorphic result cannot capture an outer argument", "let make:[@a:*, x:a, [@b:*, b, b]] ≔ {_ ^ x}"),
    ("polymorphic alias cannot merge a free and a bound variable", "let alias:[a:*, *] ≔ [@b:*, b, a] let bad:[@a:*, x:a, a alias] ≔ {y ^ y}"),
    ("a bare slot bindeth no name", "let bad:[ℤ, ℤ] ≔ +1"),
    ("a later local function shadoweth an earlier one in application", "let foo:[x: string, string] ≔ x let foo:[x: ℤ, ℤ] ≔ x + +1 let bad:string ≔ 'x' foo"),
    ("captured local alias cannot become polymorphic", "let bad: [x:] ≔ (let y ≔ x let tale:ℤ ≔ y yield tale + +1) yield 'oops' bad"),
    ("nested function cannot generalise a captured variable", "let bad: [x:] ≔ (let capture: [_:] ≔ x let tale:ℤ ≔ +0 capture let word:string ≔ +0 capture yield tale)"),
    ("constructor unification cannot change a nominal head", "type _box: [a:*, *] { box: [a, a _box] } type optional: [a:*, *] { some: [a, a optional] } let lift:[@a:*, @f:[*, *], x: a f, a f] ≔ x let twice: [x:] ≔ (x lift) lift let bad:ℤ optional ≔ (+1 box) twice"),
    ("GADT branch cannot return a wrong indexed type", "type tag: [a:*, *] { integer: ℤ tag, textual: string tag } let wrong:[@a:*, x:a tag, a] ≔ match x { integer ^ 'no', textual ^ 'yes' }"),
    ("existential constructor field cannot escape its branch", "type packed: * { pack: [@a:*, a, packed] } let leak:[@a:*, x:packed, a] ≔ match x { pack value ^ value }"),
    ("inferred existential constructor field cannot escape", "type packed: * { pack: [@a:*, a, packed] } let leak ≔ { pack value ^ value }"),
    ("quantification cannot hide an escaping constructor existential", "type packed: * { pack: [@f:[*, *], [@a:*, a f, a f], packed] } let leak ≔ { pack value ^ value }"),
    ("term type ascription rejecteth a mismatch", "let bad ≔ ('wrong': ℤ)"),
    ("parameterised type alias needeth its argument", "let predicate:[a:*, *] ≔ [a, ℤ] let bad: [_:, predicate] ≔ +1"),
    ("parameterised type alias rejecteth extra arguments", "let predicate:[a:*, *] ≔ [a, ℤ] let bad: [_:, ℤ predicate ℤ] ≔ +1"),
    ("recursive type aliases are rejected", "let first:* ≔ second let second:* ≔ first"),
    ("occurs check followeth constructor fields", "type box: [a:*, *] { box_of: [value: a, a box] } let omega: [x:] ≔ (x box_of) x"),
    ("annotation cannot claim false polymorphism", "let bad:[@a:*, _: a, a] ≔ +1"),
    ("function branches must agree", boolData ++ "let bad ≔ { yea ^ +1, nay ^ 'no' }"),
    ("function cases share arity", "let bad ≔ { x ^ x, x, y ^ x }"),
    ("inhabited empty function", "let bad:[ℤ, ℤ] ≔ {}"),
    ("unannotated empty function", "let bad ≔ {}"),
    ("a natural match needeth a successor row", "let bad:[n: ℕ, ℕ] ≔ match n { 0 ^ 0, 1 ^ 1 }"),
    ("overlapping wildcards can miss a product", boolData ++ "let bad:ℤ ≔ match yea, nay { yea, _ ^ +1, _, yea ^ +2 }"),
    ("nested match misses constructor", boolData ++ optionData ++ "let bad:ℤ ≔ match yea some { yea some ^ +1, none ^ +0 }"),
    ("constructor pattern arity", optionData ++ "let bad ≔ match +1 some { some ^ +1, none ^ +0 }"),
    ("ℤ pattern needeth ℤ input", "let bad ≔ match 'one' { +1 ^ +1, _ ^ +0 }"),
    ("finite ℤ patterns are not exhaustive", "let bad ≔ match +1 { +0 ^ +0, +1 ^ +1 }"),
    ("finite string patterns are not exhaustive", "let bad ≔ match 'one' { 'one' ^ +1 }"),
    ("missing function constraint", equalPrelude ++ "let hath_≍:[@a:*, x: a, y: a, 𝟚] ≔ x ≍ y"),
    ("insufficient constraint", equalPrelude ++ "class order_partial:[a:*, @:a hath_≍, *] { let ≤:[a, a, 𝟚] } let leq:[@a:*, @:a hath_≍, x: a, y: a, 𝟚] ≔ x ≤ y"),
    ("unknown bizen class", "bizen:ℤ missing { let missing: [x:] ≔ x }"),
    ("class law rejecteth an unbound value", "bring is.tung class bad:[a:*, *] { let rule:[x: a, x = missing] }"),
    ("class law needeth must be declared", equalPrelude ++ "bring is.tung class bad:[a:*, *] { let rule:[x: a, (x ≍ x) = (x ≍ x)] }"),
    ("class member constraint identity required at use", memberConstraint ++ "bizen:_box hath_traverse { let traverse: [x box:, f:] ≔ (x f) map box } let bad:(ℤ _box) _box ≔ (+1 box) traverse { x ^ x box }"),
    ("bizen arity followeth class", "class convert:[a:*, b:*, *] { let convert:[a, b] } bizen:ℤ convert { let convert: [x:] ≔ x }"),
    ("a slot pattern must name a constructor", "let bad:[some x:*, *] ≔ ℤ"),
    ("a slot cannot use a later slot's name", "let bad:[x:a, @a:*, a] ≔ x"),
    ("a nested slot cannot use a later slot's name", "let bad:[f:[a, @a:*, a], ℤ] ≔ +1"),
    ("a type header names its parameters", "type _box: [a, *] { box: [@a:*, a, a _box] }"),
    ("a class parent requirement is written @:parent", "class hath_+:[a, *] { let +:[@a:*, a, a, a] }"),
    ("a bizen type applieth its class", "class hath_≍:[a:*, *] {} bizen:hath_≍ {}"),
    ("a bizen type taketh only implicit parameters", "class hath_≍:[a:*, *] {} bizen:[a:*, a hath_≍] {}"),
    ("a class member is a type without a body", "class bad:[a:*, *] { let hath_≍:[x: a, a] x }")
  ]

importCases :: [Test]
importCases =
  [ typeOkWith "shown value and type cross a use" "bring file.tung let value:_box ≔ box" shown,
    typeErrWith "a local function shadoweth an imported one in application" "bring source.tung let foo:[x: string, string] ≔ x let bad:ℤ ≔ +1 foo" shadowedFunctionImport,
    typeOkWith "qualification still reacheth a shadowed import" "bring source.tung let foo:[x: string, string] ≔ x let good:ℤ ≔ +1 source~foo" shadowedFunctionImport,
    typeOkWith "default use namespace covereth terms, types, and classes" "bring type/item.tung let value:item~_item ≔ item~empty let hath_≍:item~_item ≔ value let outcome ≔ hath_≍ item~identity" aliased,
    typeOkWith "custom use alias surviveth resolved class inheritance" "bring dep.tung d class hath_child:[a:*, @:a d~hath_parent, *] { let child:[a, a] }" (Map.singleton "dep.tung" "show class hath_parent:[a:*, *] { let parent:[a, a] }"),
    expect "re-exported nominal mismatch nameth both outer aliases" $
      let message = checkSource False "bring middle_left.tung left bring middle_right.tung right let bad:left~_token ≔ right~value" reexportMismatchImports
       in "left~_token" `isInfixOf` message && "right~_token" `isInfixOf` message,
    expect "concrete aliases are not rendered as applied constructors" $
      let message = checkSource False "bring middle.tung outer let bad:string ≔ outer~value" concreteAliasProjection
       in "type error:" `isPrefixOf` message && not ("outer~boxed<ℤ>" `isInfixOf` message),
    let message = checkSource False "bring middle_left.tung left bring middle_right.tung right let bad:[@a:*, @:a left~hath_identity, x: a, a] ≔ x right~identity" reexportClassImports
     in expect ("re-exported constraint mismatch: " ++ message) ("left~hath_identity" `isInfixOf` message && "right~hath_identity" `isInfixOf` message),
    expect "imported class-member mismatch nameth both type aliases" $
      let message = checkSource False "bring left_data.tung left bring right_data.tung right bizen:ℤ left~hath_maker { let maker ≔ right~token }" fixedClassTypeImports
       in "left~_token" `isInfixOf` message && "right~_token" `isInfixOf` message,
    let message = checkSource False "bring dep.tung left let bad ≔ left~value left~identity" nestedInstanceImport
     in expect ("imported bizen constraint: " ++ message) ("left~_token" `isInfixOf` message && "left~hath_label" `isInfixOf` message),
    let message = checkSource False "bring base.tung first bring base.tung second let bad ≔ first~value first~child" duplicatedInstanceImport
     in expect ("duplicate imported bizen alias: " ++ message) ("first~_token" `isInfixOf` message && "first~hath_parent" `isInfixOf` message && not ("second~" `isInfixOf` message)),
    typeOkWith "two aliases of one module shareth data identity" "bring shared_data.tung first bring shared_data.tung second let left:first~_token ≔ second~token let right:second~_token ≔ first~token" sharedTypeAlias,
    typeErrWith "unknown qualified imported type is rejected" "bring shared_data.tung shared let bad:shared~missing ≔ shared~token" sharedTypeAlias,
    typeErrWith "private imported type spelling stayeth hidden" "bring opaque.tung opaque let bad:opaque~_secret ≔ opaque~value" opaqueTypeImport,
    typeOkWith "value with a private imported type remaineth inferable" "bring opaque.tung opaque let value ≔ opaque~value" opaqueTypeImport,
    typeOkWith "type identity surviveth a re-export" "bring base_data.tung original bring middle_data.tung reexport let from_original:reexport~_token ≔ original~value let from_reexport:original~_token ≔ reexport~value" reexportedTypeImport,
    typeOkWith "coverage separateth same-spelled imported data" "bring left_token.tung left bring right_token.tung right let outcome:ℤ ≔ match left~value { left~zero ^ +0, left~one ^ +1 }" nominalCoverageImports,
    typeErrWith "use aliases cannot collide" "bring left.tung common bring right.tung common" duplicateAliases,
    typeErrWith "default use aliases cannot collide" "bring type/item.tung bring syntax/item.tung" defaultAliasCollisionImports,
    typeOkWith "explicit use aliases override colliding defaults" "bring type/item.tung type_item bring syntax/item.tung syntax_item let left ≔ type_item~value let right ≔ syntax_item~value" defaultAliasCollisionImports,
    expect "ambiguous imports suggest surface namespaces" $
      let message = checkSource False "bring type/natural.tung bring class/algebra/total/semiring.tung let bad ≔ zero" ambiguousZeros
       in "natural~zero" `isInfixOf` message && "semiring~zero" `isInfixOf` message && not ("/" `isInfixOf` message),
    typeErrWith "a transit class requireth an explicit re-export" "bring middle.tung class child:[a:*, @:a hidden, *] { let child:[a, a] }" privateClassImports,
    typeErrWith "a transit class cannot be reached through its private namespace" "bring middle.tung class child:[a:*, @:a leaf~hidden, *] { let child:[a, a] }" privateClassImports,
    expectPrefix "bad imported source is rejected" "parse error:" (checkSource False "bring bad.tung" (Map.singleton "bad.tung" "let []")),
    typeErrWith "self use cycle is rejected" "bring self.tung" (Map.singleton "self.tung" "bring self.tung"),
    typeErrWith "mutual use cycle is rejected" "bring left.tung" cyclic,
    expectEq "a unit effect main is runnable" "type ok" (checkSource True (effectPrelude ++ "let main:𝟙 effect ≔ only sheer") unitModule),
    expectEq "main's effect type may be inferred" "type ok" (checkSource True (effectPrelude ++ "let main ≔ only sheer") unitModule),
    runnableErr "main is not a function" (effectPrelude ++ "let main:[_: 𝟙, 𝟙 effect] ≔ { _ ^ only sheer }"),
    expectEq "reporteth a source type" (Right "[@α: *, α, α]") (inspectType "show let identity: [@α: *, x: α, α] ≔ x" Map.empty "identity"),
    expectEq "type display showeth an effect result" (Right "[@α: *, α, α effect]") (inspectType (effectPrelude ++ "let wrap: [@α: *, x: α, α effect] ≔ x sheer") unitModule "wrap"),
    expectEq "reporteth an unknown inspected name" (Left "unknown name 'missing'") (inspectType "let answer ≔ +42" Map.empty "missing")
  ]
  where
    shown = Map.fromList [("file.tung", "show type _box: * { box: _box } let hidden ≔ +1")]
    unitModule = Map.singleton "type/one.tung" "show type 𝟙: * { only: 𝟙 }"
    shadowedFunctionImport = Map.singleton "source.tung" "show let foo:[x: ℤ, ℤ] ≔ x"
    aliased = Map.singleton "type/item.tung" "show type _item: * { item: _item } show class hath_identity:[a:*, *] { let identity:[a, a] } bizen:_item hath_identity { let identity: [x:] ≔ x } show let empty:_item ≔ item"
    reexportMismatchImports =
      Map.fromList
        [ ("base_left.tung", "show type _token: * { token: _token } show let value:_token ≔ token"),
          ("base_right.tung", "show type _token: * { token: _token } show let value:_token ≔ token"),
          ("middle_left.tung", "bring base_left.tung base show base~_token show base~value"),
          ("middle_right.tung", "bring base_right.tung base show base~_token show base~value")
        ]
    concreteAliasProjection =
      Map.fromList
        [ ("base.tung", "show type _box: [a:*, *] { box: [a, a _box] }"),
          ("middle.tung", "bring base.tung base show let boxed:* ≔ ℤ base~_box show let value:boxed ≔ +1 base~box")
        ]
    reexportClassImports =
      Map.fromList
        [ ("base_left.tung", "show class hath_identity:[a:*, *] { let identity:[a, a] }"),
          ("base_right.tung", "show class hath_identity:[a:*, *] { let identity:[a, a] }"),
          ("middle_left.tung", "bring base_left.tung base_left show base_left~hath_identity, base_left~identity"),
          ("middle_right.tung", "bring base_right.tung base_right show base_right~hath_identity, base_right~identity")
        ]
    fixedClassTypeImports =
      Map.fromList
        [ ("left_data.tung", "show type _token: * { token: _token } show class hath_maker:[a:*, *] { let maker:_token }"),
          ("right_data.tung", "show type _token: * { token: _token }")
        ]
    nestedInstanceImport =
      Map.singleton
        "dep.tung"
        "show type _token: * { token: _token } show class hath_identity:[a:*, *] { let identity:[a, a] } show class hath_label:[a:*, *] { let label:[a, a] } bizen:[@:_token hath_label, _token hath_identity] { let identity: [x:] ≔ x label } show let value:_token ≔ token"
    duplicatedInstanceImport =
      Map.singleton
        "base.tung"
        "show type _token: * { token: _token } show class hath_parent:[a:*, *] { let parent:[a, ℤ] } show class hath_child:[a:*, *] { let child:[a, ℤ] } bizen:[@:_token hath_parent, _token hath_child] { let child: [x:] ≔ x parent } show let value:_token ≔ token"
    sharedTypeAlias = Map.singleton "shared_data.tung" "show type _token: * { token: _token }"
    opaqueTypeImport = Map.singleton "opaque.tung" "type _secret: * { secret: _secret } show let value:_secret ≔ secret"
    reexportedTypeImport =
      Map.fromList
        [ ("base_data.tung", "show type _token: * { token: _token } show let value:_token ≔ token"),
          ("middle_data.tung", "bring base_data.tung base show base~_token show base~value")
        ]
    nominalCoverageImports =
      Map.fromList
        [ ("left_token.tung", "show type token: * { zero: token, one: token } show let value:token ≔ zero"),
          ("right_token.tung", "show type token: * { only: token } show let value:token ≔ only")
        ]
    duplicateAliases = Map.fromList [("left.tung", "show let left ≔ +1"), ("right.tung", "show let right ≔ +2")]
    defaultAliasCollisionImports = Map.fromList [("type/item.tung", "show let value ≔ +1"), ("syntax/item.tung", "show let value ≔ +2")]
    ambiguousZeros = Map.fromList [("type/natural.tung", "show let zero ≔ +0"), ("class/algebra/total/semiring.tung", "show let zero ≔ +1")]
    privateClassImports = Map.fromList [("leaf.tung", "show class hidden:[a:*, *] { let hidden:[a, a] }"), ("middle.tung", "bring leaf.tung")]
    cyclic = Map.fromList [("left.tung", "bring right.tung"), ("right.tung", "bring left.tung")]

tableAndSetCases :: Map.Map String String -> [Test]
tableAndSetCases imports =
  [ typeOkWith "wordbook, set, and powerset may qualify shared names" (source ++ qualifiedValues) imports,
    typeErrWith "wordbook, set, powerset, and list empty values are ambiguous bare" (source ++ "let bad ≔ empty") imports,
    typeErrWith "wordbook and set from_list names are ambiguous bare" (source ++ "let values:ℤ list ≔ list~empty let bad ≔ values from_list") imports
  ]
  where
    source = "bring type/integer.tung bring type/list.tung bring type/wordbook.tung bring type/set.tung bring type/powerset.tung "
    qualifiedValues =
      "let wordbook_value:ℤ wordbook string ≔ wordbook~empty "
        ++ "let set_value:ℤ set ≔ set~empty "
        ++ "let powerset_value:ℤ powerset ≔ powerset~empty "
        ++ "let wordbook_built:ℤ wordbook string ≔ list~empty wordbook~from_list "
        ++ "let set_built:ℤ set ≔ list~empty set~from_list"

orderCases :: Map.Map String String -> [Test]
orderCases imports =
  [ typeOkWith "partial order supplieth strict comparison" (partialPrefix ++ "let good ≔ lesser < greater") imports,
    typeErrWith "partial order doth not supply compare" (partialPrefix ++ "let bad ≔ lesser compare greater") imports,
    typeOkWith "total order inherits half operations" (totalPrefix ++ "let before ≔ lesser < greater let compared ≔ lesser compare greater let bounded ≔ lesser clamp greater greater") imports,
    typeErrWith "total order bizen requireth its half parent" (rankPrefix ++ "bizen:rank order_total {}") imports,
    typeOkWith "a bizen member seeth its parent compute in an impossible case" (rankPrefix ++ "bizen:rank order_partial { let ≤ ≔ { lesser, _ ^ yea, greater, greater ^ yea, greater, lesser ^ nay } let ≤_reflect ≔ sorry let ≤_antisymmetry ≔ sorry let ≤_transit ≔ sorry let ≤_=: [a:, b:, below:, above:] ≔ match a, b, below, above { lesser, lesser, _, _ ^ reflect, greater, greater, _, _ ^ reflect, greater, lesser, k, _ ^ match k {}, lesser, greater, _, k ^ match k {} } }") imports,
    typeOkWith "finite set supplieth partial order" (setPrefix ++ "let beneath ≔ smaller ≤ larger") imports,
    typeErrWith "finite set doth not claim total order" (setPrefix ++ "let bad ≔ smaller compare larger") imports
  ]
  where
    rankPrefix =
      "bring is.tung bring type/two.tung bring class/hath_equal.tung bring class/order/hath_at_most.tung bring class/order/order_partial.tung bring class/order/order_total.tung "
        ++ "type rank: * { lesser: rank, greater: rank } "
        ++ "bizen:rank hath_≍ { let ≍ ≔ { lesser, lesser ^ yea, greater, greater ^ yea, _, _ ^ nay } } "
    partialPrefix =
      rankPrefix
        ++ "bizen:rank order_partial { let ≤ ≔ { lesser, _ ^ yea, greater, greater ^ yea, greater, lesser ^ nay } let ≤_reflect ≔ sorry let ≤_antisymmetry ≔ sorry let ≤_transit ≔ sorry let ≤_= ≔ sorry } "
    totalPrefix = partialPrefix ++ "bizen:rank order_total { let ≤_total ≔ sorry } "
    setPrefix =
      "bring often.tung bring type/set.tung "
        ++ "let smaller:ℤ set ≔ empty put +1 "
        ++ "let larger:ℤ set ≔ smaller put +2 "

boundCases :: Map.Map String String -> [Test]
boundCases imports =
  [ typeOkWith "finite orders provide both endpoints" (prefix ++ "let low:𝟚 ≔ ⟂ let high:𝟛 ≔ ⊤") imports,
    typeOkWith "natural supporteth the lower-bound fold" (prefix ++ "let value:ℕ ≔ (0 ‥ list~empty) …⋎") imports,
    typeErrWith "natural doth not claim an upper bound" (prefix ++ "let value:ℕ ≔ (natural~zero ‥ list~empty) …⋏") imports,
    typeOkWith "powerset is a bounded lattice without total order" (powersetPrefix ++ "let joined:ℤ powerset ≔ (empty_set ‥ (full_set ‥ list~empty)) …⋎") imports,
    typeErrWith "lattice doth not imply total order" (powersetPrefix ++ "let bad ≔ empty_set ≤ full_set") imports,
    typeErrWith "float doth not claim a lawful lattice" "bring often.tung let bad:float ≔ 1.0 ⋏ 2.0" imports,
    typeOkWith "infimum semilattice stands without supremum" (semilatticePrefix ++ "let good ≔ item ⋏ item") imports,
    typeErrWith "infimum semilattice doth not supply supremum" (semilatticePrefix ++ "let bad ≔ item ⋎ item") imports,
    typeOkWith "supremum semilattice stands without infimum" (supremumPrefix ++ "let good ≔ item ⋎ item") imports,
    typeErrWith "supremum semilattice doth not supply infimum" (supremumPrefix ++ "let bad ≔ item ⋏ item") imports
  ]
  where
    prefix = "bring often.tung bring type/list.tung bring type/natural.tung bring class/functor/catamorphism.tung "
    powersetPrefix = "bring often.tung bring type/list.tung bring type/powerset.tung bring class/functor/catamorphism.tung let empty_set:ℤ powerset ≔ powerset~empty let full_set:ℤ powerset ≔ all "
    semilatticePrefix = "bring class/order/semilattice_lower.tung type one_sided: * { item: one_sided } bizen:one_sided semilattice_lower { let ⋏: [_:, _:] ≔ item let ⋏_swallow ≔ sorry let ⋏_swap ≔ sorry let ⋏_⋏ ≔ sorry } "
    supremumPrefix = "bring class/order/semilattice_upper.tung type one_sided: * { item: one_sided } bizen:one_sided semilattice_upper { let ⋎: [_:, _:] ≔ item let ⋎_swallow ≔ sorry let ⋎_swap ≔ sorry let ⋎_⋎ ≔ sorry } "

numericHierarchyCases :: Map.Map String String -> [Test]
numericHierarchyCases imports =
  [ typeOkWith "ℤ supplieth euclidean division" "bring often.tung bring type/optional.tung bring type/and.tung let divide_with_leftover:[@a:*, @:a euclidean, x: a, y: a, (a ∧ a) optional] ≔ x % y let value:(ℤ ∧ ℤ) optional ≔ -5 divide_with_leftover +3" imports,
    typeOkWith "float retaineth raw numeric and comparison operations" "bring often.tung let sum:float ≔ 1.0 + 2.0 let quotient:float ≔ 1.0 ÷ 2.0 let compared:𝟚 ≔ 1.0 ≤ 2.0" imports,
    typeErrWith "float doth not claim exact semiring laws" "bring often.tung let twice:[@a:*, @:a semiring, x: a, a] ≔ x + x let bad:float ≔ 1.0 twice" imports,
    typeErrWith "float doth not claim partial-order laws" "bring often.tung let reflect:[@a:*, @:a order_partial, x: a, 𝟚] ≔ x ≤ x let bad:𝟚 ≔ 1.0 reflect" imports
  ]

redundantCoverageCases :: [Test]
redundantCoverageCases =
  [ typeErrContaining "duplicate ℤ pattern is reported" "case 2 is redundant" "let bad ≔ match +1 { +0 ^ +0, +0 ^ +1, _ ^ +2 }",
    typeErrContaining "duplicate string pattern is reported" "case 2 is redundant" "let bad ≔ match 'hath_≍' { 'hath_≍' ^ +0, 'hath_≍' ^ +1, _ ^ +2 }",
    typeErrContaining "wildcard hideth constructor pattern" "case 2 is redundant" (boolData ++ "let bad ≔ match yea { _ ^ +0, yea ^ +1 }"),
    typeErrContaining "constructor pattern hidden inside product" "case 3 is redundant" (boolData ++ "let bad ≔ match yea, nay { yea, _ ^ +1, nay, _ ^ +2, _, yea ^ +3 }"),
    typeErrContaining "nested constructor pattern is reported" "case 2 is redundant" (boolData ++ optionData ++ "let bad ≔ match yea some { _ some ^ +1, yea some ^ +2, none ^ +0 }")
  ]

memberConstraint :: String
memberConstraint =
  "type optional: [a:*, *] { none: a optional, some: [a, a optional] } type _box: [a:*, *] { box: [a, a _box] } "
    ++ "class functor:[f:[*, *], *] { let map:[@a:*, @b:*, a f, [a, b], b f] } "
    ++ "class applicative:[f:[*, *], @:f functor, *] { let sheer:[@a:*, a, a f] let apply:[@a:*, @b:*, a f, [a, b] f, b f] } "
    ++ "class hath_traverse:[f:[*, *], *] { let traverse:[@m:[*, *], @:m applicative, @a:*, @b:*, a f, [a, b m], (b f) m] } "

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

-- these finite cases check every primitive pairing without repeated samples.
primitiveCases :: [Test]
primitiveCases =
  typeOk
    "polymorphic identity instantiateth at every primitive type"
    ( "let identity:[@α:*, x:α, α] ≔ x "
        ++ concat
          [ "let value" ++ show index ++ ":" ++ ty ++ " ≔ " ++ literal ++ " identity "
          | (index, (ty, literal)) <- zip [0 :: Int ..] primitiveValues
          ]
    )
    : [ typeErr
          ("a " ++ actual ++ " literal cannot inhabit " ++ claimed)
          ("let value:" ++ claimed ++ " ≔ " ++ literal)
      | (actual, literal) <- primitiveValues,
        (claimed, _) <- primitiveValues,
        actual /= claimed
      ]

primitiveValues :: [(String, String)]
primitiveValues =
  [ ("ℕ", "42"),
    ("ℤ", "+42"),
    ("float", "1.5"),
    ("string", "'word'"),
    ("unicode", "`x")
  ]

evidenceCases :: [Test]
evidenceCases =
  [ expectEq
      ("unrelated bizen order keepeth checked evidence: " ++ intercalate ", " (map fst cases))
      (Right True)
      (evidenceResolved source)
  | cases <- permutations [("ℤ", "+1"), ("float", "1.5"), ("string", "'word'"), ("unicode", "`x")],
    let source = equalPrelude ++ concatMap instanceSource cases ++ concatMap useSource cases
  ]
  where
    instanceSource (ty, _) = "bizen:" ++ ty ++ " hath_≍ { let ≍:[x:, y:] ≔ yea }"
    useSource (ty, literal) = "let " ++ ty ++ "-evidence:𝟚 ≔ " ++ literal ++ " ≍ " ++ literal ++ " "

-- the kernel independently validateth dictionary terms; normalisation must
-- select the registered member for every evidence use.
evidenceResolved :: String -> Either String Bool
evidenceResolved source = do
  program <- compileSource (SourceModule "main.tung") source
  mapM_ (Kernel.validate (sourceEnvironment program) . snd) (sourceDefinitions program)
  normal <-
    traverse
      (normaliseSourceExpression program)
      [symbolName symbol | (symbol, _) <- sourceDefinitions program, "-evidence" `isSuffixOf` symbolName symbol]
  pure (all isYea normal)
  where
    -- universe arguments may differ; the constant is what matters.
    isYea = \case
      Kernel.Global symbol _ -> symbolName symbol == "yea"
      _ -> False

inspectType :: String -> Map.Map String String -> String -> Either String String
inspectType source imports name = compileProject (SourceModule "main.tung") source imports >>= (`typeOfName` name)

coverageCases :: [Test]
coverageCases =
  [ typeOk ("exhaustive product match of arity " ++ show arity) (matchSource arity Nothing)
  | arity <- [1 .. 4]
  ]
    ++ [ typeErr
           ("product match of arity " ++ show arity ++ " misses " ++ intercalate "," missing)
           (matchSource arity (Just missing))
       | arity <- [1 .. 4],
         missing <- booleanRows arity
       ]

polymorphicPrelude :: String
polymorphicPrelude = "type pair: * { pair_of: [tale: ℤ, word: string, pair] } let both:[f:[@a:*, a, a], pair] ≔ (+1 f) pair_of ('x' f) "

boolData, optionData, boxData, equalPrelude, classHierarchy, inheritedMethodHierarchy, parentDictionaryConstraint, effectPrelude :: String
boolData = "type 𝟚: * { yea: 𝟚, nay: 𝟚 } "
optionData = "type optional: [a:*, *] { none: a optional, some: [a, a optional] } "
boxData = "type _box: [a:*, *] { box: [a, a _box] } "
equalPrelude = boolData ++ "class hath_≍:[a:*, *] { let ≍:[a, a, 𝟚] } "
classHierarchy = "class hath_parent:[a:*, *] { let parent:[a, a] } class hath_child:[a:*, @:a hath_parent, *] { let child:[a, a] } "
inheritedMethodHierarchy =
  "class magma:[a:*, *] { let combine:[a, a, a] } "
    ++ "class semigroup:[a:*, @:a magma, *] {} "
    ++ "type optional: [a:*, *] { none: a optional, some: [a, a optional] } "
    ++ "bizen:[@a:*, @:a semigroup, (a optional) semigroup] { "
    ++ "let combine ≔ { none, b ^ b, a, none ^ a, a some, b some ^ a combine b $ some } "
    ++ "}"
parentDictionaryConstraint =
  "class hath_parent:[a:*, *] { let parent:[a, a] } "
    ++ "class child:[a:*, @:a hath_parent, *] {} "
    ++ boxData
    ++ "bizen:[@a:*, @:a hath_parent, (a _box) hath_parent] { let parent: [x box:] ≔ (x parent) box } "
    ++ "bizen:[@a:*, @:a hath_parent, (a _box) child] {}"
effectPrelude = "bring type/one.tung let sheer:[@a:*, a, a effect] ≔ 'effect_sheer' foreign "
