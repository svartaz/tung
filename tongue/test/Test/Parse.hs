-- declaration and expression syntax, application order, and malformed separators.
module Test.Parse (group) where

import Test.Harness (Group, Test, expectEq, integerSource, parseErr, parseOk)
import Test.Harness qualified as Harness
import Test.QuickCheck qualified as QuickCheck
import Tung.Dependent.Source (Declaration (..), parseExpression, parseSource, sketch)

group :: IO Group
group =
  Harness.group "parse" $
    map (uncurry parseOk) accepted
      ++ map (uncurry parseErr) rejected
      ++ importCases
      ++ map expressionCase expressions
      ++ generatedDefinitionForms
      ++ parserProperties

accepted :: [(String, String)]
accepted =
  [ ("inferred value", "let answer ≔ +42"),
    ("value annotation", "let answer:ℤ ≔ +42"),
    ("declaration endeþ at the next declaration", "let answer:ℤ ≔ +42 let other ≔ +1"),
    ("value annotation may be a quantified function type", "let identity:[@a:*, [a, a]] ≔ { x ^ x }"),
    ("an inferred slot type", "let identity: [x:] ≔ x"),
    ("bare slots describe a function value", "let identity:[@a:*, a, a] ≔ { x ^ x }"),
    ("named slot with inferred result", "let identity:[@a:*, x: a] ≔ x"),
    ("type parameters before value arguments", "let constant:[@a:*, @b:*, x:a, _:b, a] ≔ x"),
    ("constraints, then type parameters, then values", "let keep:[@a:*, @:a equal, @b:*, x:a, y:b, a] ≔ x"),
    ("quantified parameter kind may be a type constructor", "let choose:[f:[@a:[*, *], ℤ a, ℤ], ℤ] ≔ +1"),
    ("named prefix and nested bare argument", "let f: [@b:*, @c:*, @d:*, x:, y: b, [c, d], d] ≔ { z ^ z }"),
    ("infix slot pattern with or without grouping", "ilk ∏: [a:*, b:*, *] { boþ: [a, b, a ∏ b] } let f:[(a boþ b): a ∏ b, ℤ] ≔ +1 let g:[a boþ b: a ∏ b, ℤ] ≔ +1"),
    ("term type ascription", "let answer ≔ (+1 + +2: ℤ)"),
    ("sorry is an expression", "let answer:ℤ ≔ sorry"),
    ("text-keyed fremmed let", "let plus:[ℤ, ℤ, ℤ] ≔ 'add_integer' fremmed"),
    ("adjacent declarations and final yield", "let x ≔ +1 let y ≔ +2 yield x + y"),
    ("type aliases", "let count:* ≔ ℤ let answer:count ≔ +42 let powerset:[a:*, *] ≔ a → 𝟚"),
    ("type composition aliases", "let paired:* ≔ >{pair, ℤ, text, unicode} let nested:* ≔ >{pair, >{pair, ℤ, text}, text}"),
    ("algebraic data", "ilk option: [a:*, *] { none: a option, some: [a, a option] }"),
    ("adjacent constructor signatures", "ilk list: [a:*, *] { empty: a list, ‥: [a, a list, a list] }"),
    ("higher-kinded data parameter", "ilk free: [f:[*, *], a:*, *] { done: [a, f free a], more: [(f free a) f, f free a] }"),
    ("nullary signatures and empty data", "ilk ℕ: * { zero: ℕ, suc: [ℕ, ℕ] } ilk 𝟘: * {}"),
    ("a function type may start a constructor header", "ilk _request: [a:*, *] { ask: [[ℤ, a], a _request], stop: a _request }"),
    ("deed is an ordinary type constructor", "let echo:[text, 𝟙 deed] ≔ write let main:𝟙 deed ≔ 'x' echo"),
    ("flock members and laws need no separators", "flock identity:[a:*, *] { let identity:[a, a] let same:[a, a] let rule:[x: a, (x identity) = x] }"),
    ("flock member with local type parameters", "flock owner:[a:*, *] { let member:[@b:*, b, a] }"),
    ("higher-order flock members", "flock cata:[f:[*, *], *] { let fold₀:[@a:*, @b:*, a f, b, [a, b, b], b] }"),
    ("flock constraints precede parameters", "flock convert:[a:*, @:a equal, b:*, *] { let convert:[a, b] }"),
    ("flock member requirement", "flock haþ_traverse:[f:[*, *], *] { let traverse:[@m:[*, *], @:m applicative, @a:*, @b:*, a f, [a, b m], (b f) m] }"),
    ("flock without parameters", "flock marker:* { let mark:ℤ }"),
    ("flock with a binary type constructor", "flock category:[⇨:[*, *, *], *] { let same:[@a:*, a ⇨ a] }"),
    ("law sides may contain local blocks", "flock identity:[a:*, *] { let rule:[x: a, (let y ≔ x yield y) = (let z ≔ x yield z)] }"),
    ("bizen methods use let", "bizen:[@a:*, @:a equal, (a box) equal] { let ≍: [x box:, y box:] ≔ x ≍ y }"),
    ("bizen uses second-is-function order", "flock convert:[a:*, b:*, *] { let convert:[a, b] } bizen:ℤ convert text { let convert: [x:] ≔ 'x' }"),
    ("bizen heads may be function types", "bizen:[@a:*, a, a] marker {} bizen:ℤ marker [@a:*, a, a] (ℤ list) {}"),
    ("adjacent bizen members", "bizen:ℤ linked { let first: [@a:*, @:a equal, x:] ≔ x let second: [x:] ≔ x first }"),
    ("show prefixeþ declarations", "show let answer ≔ +42 show let count:* ≔ ℤ show ilk option: [a:*, *] { none: a option, some: [a, a option] } show flock equal:[a:*, *] { let ≍:[a, a, 𝟚] }"),
    ("re-exports", "use file.tung show file~value show file~first, file~second"),
    ("use accepteþ an optional alias", "use ilk/list.tung list yield list~empty"),
    ("records", "let person ≔ r{name ≔ 'n', age ≔ +1} yield r{≔ person, age ≔ +2, - name}"),
    ("matches", "yield match +1, 'yes' { +0, 'yes' ^ +1, _, _ ^ +0 }"),
    ("anonymous curried function", "yield {x, y, z ^ z}"),
    ("empty consuming match", "yield match x {}"),
    ("local blocks", "yield (let x ≔ +1 let y ≔ +2 yield x + y)")
  ]

rejected :: [(String, String)]
rejected =
  [ ("bare final expression requireþ yield", "42"),
    ("type composition requireþ a function", "let bad:* ≔ >{}"),
    ("type composition requireþ two operands", "let bad:* ≔ >{pair, ℤ}"),
    ("type composition requireþ a closing brace", "let bad:* ≔ >{pair, ℤ, text"),
    ("declaration requireþ a body", "let answer ≔"),
    ("value annotation requireþ equals", "let answer:ℤ +42"),
    ("function annotation requireþ equals", "let identity:[x:ℤ, ℤ] x"),
    ("value annotation requireþ a type", "let answer: ≔ +42"),
    ("omitted argument types require positional binders", "let bad:[x:[], ℤ] ≔ x"),
    ("duplicate type parameters", "let bad:[@a:*, @a:*, x:a, a] ≔ x"),
    ("nested quantifiers have distinct names", "let bad:[f:[@a:*, @a:*, a, a], ℤ] ≔ +1"),
    ("polymorphic type parameter requireþ a kind", "let bad:[@a, x:a, a] ≔ x"),
    ("type parameter requireþ a name", "let bad:[@a:*, @, x:a, a] ≔ x"),
    ("named arguments precede bare types", "let bad:[@a:*, @b:*, @c:*, a, x: b, c] ≔ x"),
    ("named slots precede bare slots", "let bad: [@a:*, @b:*, @c:*, x:, a, y: b, c] ≔ x"),
    ("flock member requireþ a bracketed type", "flock bad:[a:*, *] { let member a }"),
    ("a flock signature endeþ in a kind", "flock bad:[a:*] {}"),
    ("a member annotation wiþ binders endeþ in an equation", "flock bad:[a:*, *] { let rule:[x:a] }"),
    ("law brackets require typed names", "flock bad:[a:*, *] { let rule:[x:, x = x] }"),
    ("use requireþ a path", "use"),
    ("bizen evidence cannot be shown", "show bizen:ℤ missing {}"),
    ("fremmed let requireþ an annotation", "let plus ≔ 'add_integer' fremmed"),
    ("pattern binders are linear", "let bad ≔ { x, x ^ x }"),
    ("fremmed marker cannot be nested", "let bad:r{value: ℤ} ≔ r{value ≔ 'add_integer' fremmed}"),
    ("fremmed let must be file-level", "let outer: [_:] ≔ (let plus:[ℤ, ℤ, ℤ] ≔ 'add_integer' fremmed yield +1)"),
    ("use alias must be unqualified", "use ilk/list.tung list~short"),
    ("use alias must be slash-free", "use ilk/list.tung sequence/list"),
    ("qualified namespace must be slash-free", "use ilk/list.tung yield ilk/list~empty"),
    ("show requireþ a name", "show"),
    ("show cannot prefix use", "show use ground.tung"),
    ("show cannot prefix an expression", "show +42"),
    ("local block requireþ yield", "yield (let x ≔ +1 x)"),
    ("ilk requireþ a body", "ilk option"),
    ("data header requireþ a result kind", "ilk box: [a:*] { box: [a, a box] }"),
    ("constructor signature requireþ a result", "ilk box: [a:*, *] { box: [] }"),
    ("required flock member needeþ let", "flock bad:[a:*, *] { a bad: a }"),
    ("match arm requireþ ^", "yield match +1 { _ +1 }"),
    ("dollar requireþ a left expression", "yield $ + +1 +2"),
    ("dollar requireþ a function", "yield a f $"),
    ("record removal without space is a name", "yield r{≔ person, -age}"),
    ("record update requireþ a base", "yield r{≔ , value ≔ +1}"),
    ("record marker must touch its body", "yield r {value ≔ +1}"),
    ("record type marker must touch its body", "let value:r {field: ℤ} ≔ r{field ≔ +1}"),
    ("association markers must touch their bodies", "yield < {+, +1, +2}"),
    ("association requireþ a combining function", "yield >{}"),
    ("association requireþ values", "yield <{f}"),
    ("association requireþ at least two values", "yield >{f, a}"),
    ("bizen members reject commas", "bizen:ℤ equal { let ≍: [x:, y:] ≔ x, let ≭: [x:, y:] ≔ y }")
  ]

importCases :: [Test]
importCases =
  [ expectEq ("complete use " ++ source) (Right [ImportDeclaration path alias]) (parseSource source)
  | path <- ["ground.tung", "ilk/list.tung", "a.extra.tung", "pkg.one/query.tung"],
    alias <- [Nothing, Just "chosen"],
    let source = "use " ++ path ++ maybe "" (" " ++) alias
  ]

-- each expression and its location-free sketch, function first.
expressions :: [(String, String, String)]
expressions =
  [ ("term type ascription", "(+1: ℤ)", "(+1: ℤ)"),
    ("record expression", "r{left ≔ 1, right ≔ +2}", "r{left ≔ 1, right ≔ +2}"),
    ("record access expression", "person.age", "person.age"),
    ("chained record access expression", "person.address.city", "person.address.city"),
    ("record update expression", "r{≔ value, right ≔ +3, - left}", "r{≔ value, right ≔ +3, - left}"),
    ("left-associated sequence", "<{+, a, b, c, d}", "(+ (+ (+ a b) c) d)"),
    ("right-associated sequence", ">{‥, a, b, c, d}", "(‥ a (‥ b (‥ c d)))"),
    ("separated left marker remaineþ an ordinary name", "+1 < (+2)", "(< +1 +2)"),
    ("separated right marker remaineþ an ordinary name", "+1 > (+2)", "(> +1 +2)"),
    ("ℤ match pattern", "match +1 { +0 ^ +2, _ ^ +3 }", "match +1 {+0 ^ +2, _ ^ +3}"),
    ("';' joineþ rows sharing a result", "match +1 { +0; +1 ^ +2, _ ^ +3 }", "match +1 {+0 ^ +2, +1 ^ +2, _ ^ +3}"),
    ("multi-pattern match preserves order", "match +1, +2, +3 { +0, +1, +2 ^ +4 }", "match +1, +2, +3 {+0, +1, +2 ^ +4}"),
    ("text match pattern", "match 'yes' { 'yes' ^ +1, _ ^ +0 }", "match 'yes' {'yes' ^ +1, _ ^ +0}"),
    ("second term is function", "+1 + +2", "(+ +1 +2)"),
    ("an unsigned literal is a natural", "match 1 { 0 ^ 2 }", "match 1 {0 ^ 2}"),
    ("explicit types are separate from value argument order", "a f @text @(text list) b", "(f a @text @(list text) b)"),
    ("explicit type application alone", "f @ℤ", "(f @ℤ)"),
    ("dollar application accepteth type inputs", "a $f @text b", "(f a @text b)"),
    ("unmarked sequence sendeþ every argument", "a f b g", "(f a b g)"),
    ("dollar bare segment", "a f $h b g", "(h (f a) b g)"),
    ("dollar accepteþ space before function", "a f $ h b g", "(h (f a) b g)"),
    ("dollar chain", "a f $g b $h c", "(h (g (f a) b) c)"),
    ("dollar bare tail is function first", "a f $g b c $h d", "(h (g (f a) b c) d)"),
    ("dollar parens are function first", "a f $(g b c) $h d", "(h (g (f a) b c) d)"),
    ("dollar keepeþ multiple parenthesised arguments separate", "a f $ if (a some) none", "(if (f a) (some a) none)"),
    ("anonymous function argument", "l fold₁ natural~zero {n, _ ^ n suc}", "(fold₁ l natural~zero {n, _ ^ (suc n)})")
  ]

expressionCase :: (String, String, String) -> Test
expressionCase (name, source, expected) = expectEq name (Right expected) (sketch <$> parseExpression source)

generatedDefinitionForms :: [Test]
generatedDefinitionForms =
  [ parseOk (owner ++ " form " ++ show n) (wrap source)
  | (owner, wrap) <-
      [ ("let", id),
        ("bizen method", \source -> "bizen:thing klass { " ++ source ++ " }")
      ],
    (n, source) <- zip [(1 :: Int) ..] definitionForms
  ]

definitionForms :: [String]
definitionForms =
  [ "let foo: [@d:*, a:, b:, c:, d] ≔ c",
    "let foo: [a:, b:, c:] ≔ c",
    "let foo:[@α:*, @β:*, @γ:*, @δ:*, a: α, b: β, c: γ, δ] ≔ c",
    "let foo:[@α:*, @β:*, @γ:*, a: α, b: β, c: γ] ≔ c",
    "let foo:[@α:*, @t1:*, @γ:*, @δ:*, a: α, b: t1, c: γ, δ] ≔ c",
    "let foo:[@α:*, @t1:*, @γ:*, a: α, b: t1, c: γ] ≔ c",
    "let foo: [@α:[*, *], @:α functor, @β:*, @:β monoid, @δ:*, a:, b:, c:, δ] ≔ c",
    "let foo:[@α:*, @:α equal, @β:*, @:β monoid, @γ:*, @δ:*, a: α, b: β, c: γ, δ] ≔ c"
  ]

parserProperties :: [Test]
parserProperties =
  [ Harness.propertyTest ("property: top-level let boundary " ++ show separator) $
      QuickCheck.forAll (QuickCheck.chooseInteger (-999, 999)) \first ->
        QuickCheck.forAll (QuickCheck.chooseInteger (-999, 999)) \second ->
          let source = "let first ≔ " ++ integerSource first ++ separator ++ "let second ≔ " ++ integerSource second
              summary declarations = [(declarationName, sketch declarationBody) | Declaration {..} <- declarations]
           in QuickCheck.counterexample source (fmap summary (parseSource source) QuickCheck.=== Right [("first", integerSource first), ("second", integerSource second)])
  | separator <- [" ", "\n", "\t", " # boundary\n", " /* boundary */ "]
  ]
