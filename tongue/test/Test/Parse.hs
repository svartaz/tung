-- declaration and expression syntax, application order, and malformed separators.
module Test.Parse (group) where

import Control.Monad (filterM)
import Data.List (sortOn)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath (takeExtension, (</>))
import Test.Harness (Group, Test, expectEq, integerSource, parseErr, parseOk)
import Test.Harness qualified as Harness
import Test.QuickCheck qualified as QuickCheck
import Tung (Leaf (..), NodeKind (..), Piece (..), PieceKind (..), SourceFailure (..), SourceSpan (..), SourceSyntax (..), Token (..), Tree (..), sourceSyntaxSummary, sourceTree, treeText)
import Tung.Dependent.Source (Declaration (..), parseExpression, parseProgram, parseSource, recoverSnapshot, sketch, sourceSnapshot)

group :: IO Group
group =
  Harness.group "parse" $
    map (uncurry parseOk) accepted
      ++ map (uncurry parseErr) rejected
      ++ importCases
      ++ map expressionCase expressions
      ++ generatedDefinitionForms
      ++ parserProperties
      ++ recoveryCases
      ++ [treeCorpus, brokenTree, localScopes]

accepted :: [(String, String)]
accepted =
  [ ("inferred worth", "let answer ≔ +42"),
    ("worth annotation", "let answer:ℤ ≔ +42"),
    ("declaration endeth at the next declaration", "let answer:ℤ ≔ +42 let other ≔ +1"),
    ("worth annotation may be a quantified function type", "let sameness:[@a:*, [a, a]] ≔ { x ^ x }"),
    ("an inferred slot type", "let sameness: [x:] ≔ x"),
    ("bare slots describe a function worth", "let sameness:[@a:*, a, a] ≔ { x ^ x }"),
    ("named slot with inferred result", "let sameness:[@a:*, x: a] ≔ x"),
    ("type parameters before worth arguments", "let constant:[@a:*, @b:*, x:a, _:b, a] ≔ x"),
    ("constraints, then type parameters, then values", "let keep:[@a:*, @:a hath_≍, @b:*, x:a, y:b, a] ≔ x"),
    ("quantified parameter kind may be a type constructor", "let choose:[f:[@a:[*, *], ℤ a, ℤ], ℤ] ≔ +1"),
    ("named prefix and nested bare argument", "let f: [@b:*, @c:*, @d:*, x:, y: b, [c, d], d] ≔ { z ^ z }"),
    ("infix slot pattern with or without grouping", "ilk ∏: [a:*, b:*, *] { both: [a, b, a ∏ b] } let f:[(a both b): a ∏ b, ℤ] ≔ +1 let g:[a both b: a ∏ b, ℤ] ≔ +1"),
    ("sorry is an expression", "let answer:ℤ ≔ sorry"),
    ("string-keyed fremmed let", "let plus:[ℤ, ℤ, ℤ] ≔ 'eke_wholetale' fremmed"),
    ("adjacent declarations and final yield", "let x ≔ +1 let y ≔ +2 yield x + y"),
    ("type aliases", "let rime:* ≔ ℤ let answer:rime ≔ +42 let powerset:[a:*, *] ≔ a → 𝟚"),
    ("type composition aliases", "let paired:* ≔ >{pair, ℤ, string, unicode} let nested:* ≔ >{pair, >{pair, ℤ, string}, string}"),
    ("algebraic data", "ilk maybe: [a:*, *] { none: a maybe, some: [a, a maybe] }"),
    ("adjacent constructor signatures", "ilk list: [a:*, *] { empty: a list, ‥: [a, a list, a list] }"),
    ("higher-kinded data parameter", "ilk free: [f:[*, *], a:*, *] { done: [a, f free a], more: [(f free a) f, f free a] }"),
    ("nullary signatures and empty data", "ilk ℕ: * { naught: ℕ, suc: [ℕ, ℕ] } ilk 𝟘: * {}"),
    ("a function type may start a constructor header", "ilk _request: [a:*, *] { ask: [[ℤ, a], a _request], stop: a _request }"),
    ("deed is an ordinary type constructor", "let echo:[string, 𝟙 deed] ≔ write let main:𝟙 deed ≔ 'x' echo"),
    ("fast declarations take a let header and may be shown", "fast echo:𝟙 deed ≔ echo show fast count:[n:ℕ, 𝟙 deed] ≔ (n heir) count"),
    ("flock members and laws need no separators", "flock sameness:[a:*, *] { let sameness:[a, a] let hath_≍:[a, a] let rule:[x: a, (x sameness) = x] }"),
    ("flock member with local type parameters", "flock owner:[a:*, *] { let member:[@b:*, b, a] }"),
    ("higher-order flock members", "flock downshaper:[f:[*, *], *] { let gather₀:[@a:*, @b:*, a f, b, [a, b, b], b] }"),
    ("flock constraints precede parameters", "flock convert:[a:*, @:a hath_≍, b:*, *] { let convert:[a, b] }"),
    ("flock member requirement", "flock hath_throughwend:[f:[*, *], *] { let throughwend:[@m:[*, *], @:m atfoldsome, @a:*, @b:*, a f, [a, b m], (b f) m] }"),
    ("flock without parameters", "flock marker:* { let mark:ℤ }"),
    ("flock with a binary type constructor", "flock category:[⇨:[*, *, *], *] { let hath_≍:[@a:*, a ⇨ a] }"),
    ("law sides may inhold local blocks", "flock sameness:[a:*, *] { let rule:[x: a, (let y ≔ x yield y) = (let z ≔ x yield z)] }"),
    ("law parameters use ordinary bracket parsing", "flock sameness:[a:*, *] { let rule:[x:, x = x] }"),
    ("bizen methods use let", "bizen:[@a:*, @:a hath_≍, (a box) hath_≍] { let ≍: [x box:, y box:] ≔ x ≍ y }"),
    ("bizen uses second-is-function order", "flock convert:[a:*, b:*, *] { let convert:[a, b] } bizen:ℤ convert string { let convert: [x:] ≔ 'x' }"),
    ("bizen heads may be function types", "bizen:[@a:*, a, a] marker {} bizen:ℤ marker [@a:*, a, a] (ℤ list) {}"),
    ("adjacent bizen members", "bizen:ℤ linked { let first: [@a:*, @:a hath_≍, x:] ≔ x let second: [x:] ≔ x first }"),
    ("show prefixeth declarations", "show let answer ≔ +42 show let rime:* ≔ ℤ show ilk maybe: [a:*, *] { none: a maybe, some: [a, a maybe] } show flock hath_≍:[a:*, *] { let ≍:[a, a, 𝟚] }"),
    ("re-exports", "bring file.tung show file~worth show file~first, file~second"),
    ("matches", "yield match +1, 'yes' { +0, 'yes' ^ +1, _, _ ^ +0 }"),
    ("anonymous curried function", "yield {x, y, z ^ z}"),
    ("empty consuming match", "yield match x {}"),
    ("local blocks", "yield (let x ≔ +1 let y ≔ +2 yield x + y)")
  ]

rejected :: [(String, String)]
rejected =
  [ ("bare final expression requireth yield", "42"),
    ("orsetting requireth a type annotation", "orsetting bad"),
    ("type composition requireth a closing brace", "let bad:* ≔ >{pair, ℤ, string"),
    ("declaration requireth a body", "let answer ≔"),
    ("fast requireth a name", "fast : 𝟙 deed ≔ x"),
    ("worth annotation requireth equals", "let answer:ℤ +42"),
    ("function annotation requireth equals", "let sameness:[x:ℤ, ℤ] x"),
    ("worth annotation requireth a type", "let answer: ≔ +42"),
    ("omitted argument types require positional binders", "let bad:[x:[], ℤ] ≔ x"),
    ("duplicate type parameters", "let bad:[@a:*, @a:*, x:a, a] ≔ x"),
    ("nested quantifiers have distinct names", "let bad:[f:[@a:*, @a:*, a, a], ℤ] ≔ +1"),
    ("polymorphic type parameter requireth a kind", "let bad:[@a, x:a, a] ≔ x"),
    ("type parameter requireth a name", "let bad:[@a:*, @, x:a, a] ≔ x"),
    ("named slots precede bare slots", "let bad: [@a:*, @b:*, @c:*, x:, a, y: b, c] ≔ x"),
    ("flock member requireth a bracketed type", "flock bad:[a:*, *] { let member a }"),
    ("a flock signature endeth in a kind", "flock bad:[a:*] {}"),
    ("member brackets require a final result expression", "flock bad:[a:*, *] { let rule:[x:a] }"),
    ("bring requireth a path", "bring"),
    ("bizen evidence cannot be shown", "show bizen:ℤ missing {}"),
    ("fremmed let requireth an annotation", "let plus ≔ 'eke_wholetale' fremmed"),
    ("fremmed marker cannot be nested", "let bad:ℤ ≔ ('eke_wholetale' fremmed)"),
    ("fremmed let must be file-level", "let outer: [_:] ≔ (let plus:[ℤ, ℤ, ℤ] ≔ 'eke_wholetale' fremmed yield +1)"),
    ("use alias must be unqualified", "bring ilk/list.tung list~short"),
    ("use alias must be slash-free", "bring ilk/list.tung sequence/list"),
    ("qualified namespace must be slash-free", "bring ilk/list.tung yield ilk/list~empty"),
    ("show requireth a name", "show"),
    ("show cannot prefix use", "show bring often.tung"),
    ("show cannot prefix an expression", "show +42"),
    ("local block requireth yield", "yield (let x ≔ +1 x)"),
    ("ilk requireth a body", "ilk maybe"),
    ("data header requireth a result kind", "ilk box: [a:*] { box: [a, a box] }"),
    ("constructor signature requireth a result", "ilk box: [a:*, *] { box: [] }"),
    ("required flock member needeth let", "flock bad:[a:*, *] { a bad: a }"),
    ("match arm requireth ^", "yield match +1 { _ +1 }"),
    ("dollar requireth a left expression", "yield $ + +1 +2"),
    ("dollar requireth a function", "yield a f $"),
    ("association markers must touch their bodies", "yield < {+, +1, +2}"),
    ("association requireth a combining function", "yield >{}"),
    ("association requireth values", "yield <{f}"),
    ("association requireth at least two values", "yield >{f, a}"),
    ("bizen members reject commas", "bizen:ℤ hath_≍ { let ≍: [x:, y:] ≔ x, let ≭: [x:, y:] ≔ y }"),
    ("bizen requireth named members", "bizen:ℤ hath_≍ ≔ same")
  ]

importCases :: [Test]
importCases =
  [ expectEq ("complete use " ++ source) (Right [ImportDeclaration path alias]) (parseSource source)
  | path <- ["often.tung", "ilk/list.tung", "a.extra.tung", "pkg.one/query.tung"],
    alias <- [Nothing, Just "chosen"],
    let source = "bring " ++ path ++ maybe "" (" " ++) alias
  ]

-- each expression and its location-free sketch, function first.
expressions :: [(String, String, String)]
expressions =
  [ ("term type ascription", "(+1: ℤ)", "(+1: ℤ)"),
    ("field access expression", "person.age", "person.age"),
    ("chained record access expression", "person.address.city", "person.address.city"),
    ("left-associated sequence", "<{+, a, b, c, d}", "(+ (+ (+ a b) c) d)"),
    ("right-associated sequence", ">{‥, a, b, c, d}", "(‥ a (‥ b (‥ c d)))"),
    ("separated left marker remaineth an ordinary name", "+1 < (+2)", "(< +1 +2)"),
    ("separated right marker remaineth an ordinary name", "+1 > (+2)", "(> +1 +2)"),
    ("ℤ match pattern", "match +1 { +0 ^ +2, _ ^ +3 }", "match +1 {+0 ^ +2, _ ^ +3}"),
    ("'for' is an ordinary name in a scrutinee", "match b for known { _ ^ b }", "match (for b known) {_ ^ b}"),
    ("';' yoketh rows sharing a result", "match +1 { +0; +1 ^ +2, _ ^ +3 }", "match +1 {+0 ^ +2, +1 ^ +2, _ ^ +3}"),
    ("multi-pattern match preserves order", "match +1, +2, +3 { +0, +1, +2 ^ +4 }", "match +1, +2, +3 {+0, +1, +2 ^ +4}"),
    ("string match pattern", "match 'yes' { 'yes' ^ +1, _ ^ +0 }", "match 'yes' {'yes' ^ +1, _ ^ +0}"),
    ("second term is function", "+1 + +2", "(+ +1 +2)"),
    ("an unsigned literal is a natural", "match 1 { 0 ^ 2 }", "match 1 {0 ^ 2}"),
    ("explicit types are separate from worth argument order", "a f @string @(string list) b", "(f a @string @(list string) b)"),
    ("explicit type application alone", "f @ℤ", "(f @ℤ)"),
    ("dollar application accepteth type inputs", "a $f @string b", "(f a @string b)"),
    ("unmarked sequence sendeth every argument", "a f b g", "(f a b g)"),
    ("dollar bare segment", "a f $h b g", "(h (f a) b g)"),
    ("dollar accepteth space before function", "a f $ h b g", "(h (f a) b g)"),
    ("dollar chain", "a f $g b $h c", "(h (g (f a) b) c)"),
    ("dollar bare tail is function first", "a f $g b c $h d", "(h (g (f a) b c) d)"),
    ("dollar parens are function first", "a f $(g b c) $h d", "(h (g (f a) b c) d)"),
    ("dollar keepeth multiple parenthesised arguments separate", "a f $ if (a some) none", "(if (f a) (some a) none)"),
    ("anonymous function argument", "l gather₁ natural~naught {n, _ ^ n suc}", "(gather₁ l natural~naught {n, _ ^ (suc n)})")
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
    "let foo: [@α:[*, *], @:α functor, @β:*, @:β monoid, @δ:*, a:, b:, c:, δ] ≔ c",
    "let foo:[@α:*, @:α hath_≍, @β:*, @:β monoid, @γ:*, @δ:*, a: α, b: β, c: γ, δ] ≔ c"
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

-- recovery collecteth complete syntax without weakening the strict parser.
recoveryCases :: [Test]
recoveryCases =
  [ expectEq "recovery reuseth complete declarations and yield" (parseProgram complete, []) $
      let (declarations, yielded, failures) = recoverSnapshot (sourceSnapshot complete)
       in (Right (map snd declarations, yielded), failures),
    expectEq "recovery retaineth UTF-16 spans and the final yield" ([Just (SourceSpan 9 15), Just (SourceSpan 45 50)], ["before", "after"], Just "sorry", [Just (SourceSpan 39 40)]) $
      let (declarations, yielded, failures) = recoverSnapshot (sourceSnapshot broken)
       in (map fst declarations, names declarations, sketch <$> yielded, map failureSpan failures),
    parseErr "recovered syntax remaineth a strict parse failure" broken
  ]
    ++ [ expectEq label (expected, Nothing, 1) (summary source)
       | (label, source, expected) <-
           [ ("recovery doth not promote members from a malformed flock", "flock broken:* {\nlet nested:ℤ ≔ sorry\n}\nlet after:ℤ ≔ sorry", ["after"]),
             ("an unclosed delimiter preventeth suffix recovery", "let before:ℤ ≔ sorry\nflock broken:* {\nlet nested:ℤ ≔ sorry\nlet after:ℤ ≔ sorry", ["before"]),
             ("a lexical error retaineth only complete prefix declarations", "let before:ℤ ≔ sorry\nlet broken ≔ '\nlet after:ℤ ≔ sorry", ["before"])
           ]
       ]
  where
    complete = "let before:ℤ ≔ sorry\nyield sorry"
    broken = "# 😀\nlet before:ℤ ≔ sorry\nlet broken ≔ )\nlet after:ℤ ≔ sorry\nyield sorry"
    names declarations = [declarationName | (_, Declaration {declarationName}) <- declarations]
    summary source =
      let (declarations, yielded, failures) = recoverSnapshot (sourceSnapshot source)
       in (names declarations, sketch <$> yielded, length failures)

-- every source's tree joineth to its text; each top-level child is one parsed
-- declaration, and a bracket with marked children holdeth nothing else but
-- separators.
treeCorpus :: Test
treeCorpus = do
  files <- concat <$> traverse tungFiles ["../bookhoard", "../byspel"]
  problems <- concat <$> traverse check files
  pure (if null problems then Nothing else Just (unlines (take 8 problems)))
  where
    check file = do
      source <- readFile file
      let tree = sourceTree source
          children = case tree of
            TreeNode FileNode nodes -> nodes
            _ -> []
          declarations = length [() | TreeNode DeclarationNode _ <- children]
          expected = either (const (-1)) (\(found, yielded) -> length found + maybe 0 (const 1) yielded) (parseProgram source)
      pure $
        [file ++ ": the tree's text differeth from the source" | treeText tree /= source]
          ++ [file ++ ": " ++ show declarations ++ " declaration nodes for " ++ show expected ++ " declarations" | declarations /= expected]
          ++ [file ++ ": a top-level child is no declaration" | not (all topLevel children)]
          ++ [file ++ ": a bracket mixeth marked items with " ++ show (map treeText stray) | stray@(_ : _) <- map strayItems (brackets tree)]
    topLevel = \case
      TreeNode DeclarationNode _ -> True
      TreeLeaf Leaf {leafPiece = Nothing} -> True
      _ -> False
    brackets = \case
      node@(TreeNode BracketNode children) -> node : concatMap brackets children
      TreeNode _ children -> concatMap brackets children
      TreeLeaf _ -> []
    strayItems = \case
      TreeNode BracketNode children
        | inside@(_ : _) <- drop 1 (take (length children - 1) children),
          any marked inside ->
            [child | child <- inside, not (marked child), not (separator child)]
      _ -> []
    marked = \case
      TreeNode kind _ -> kind `elem` [DeclarationNode, ItemNode, RowNode]
      _ -> False
    separator = \case
      TreeLeaf Leaf {leafPiece = Just Piece {pieceKind = Lexeme token}} -> token `elem` [TComma, TSemicolon]
      _ -> False

tungFiles :: FilePath -> IO [FilePath]
tungFiles directory = do
  entries <- map (directory </>) <$> listDirectory directory
  nested <- filterM doesDirectoryExist entries
  deeper <- concat <$> traverse tungFiles nested
  pure ([entry | entry <- entries, takeExtension entry == ".tung"] ++ deeper)

brokenTree :: Test
brokenTree =
  expectEq
    "an unreadable region is one broken node between declarations"
    ([DeclarationNode, BrokenNode, DeclarationNode], source)
    ( case sourceTree source of
        tree@(TreeNode FileNode children) -> ([kind | TreeNode kind _ <- children], treeText tree)
        tree -> ([], treeText tree)
    )
  where
    source = "let a ≔ 1\nlet b ≔\nlet c ≔ 2\n"

-- each local binder is seen from itself to the end of what bindeth it: a
-- slot by the later slots and the body, a block's let by the rest of the
-- block, a row's pattern by its row, and a flock's parameter by its members.
localScopes :: Test
localScopes =
  expectEq
    "the parser scopeth each local binder"
    [ ("n", "n: ℕ, x: n fan, ℕ] ≔ (let k ≔ n yield {0 ^ k, m heir ^ m} x)"),
      ("x", "x: n fan, ℕ] ≔ (let k ≔ n yield {0 ^ k, m heir ^ m} x)"),
      ("k", "k ≔ n yield {0 ^ k, m heir ^ m} x)"),
      ("m", "m heir ^ m"),
      ("heir", "heir ^ m"),
      ("α", "α: *, *] { let get: α }")
    ]
    [(slice binder, slice scope) | (binderStart, binderEnd, scopeStart, scopeEnd) <- sortOn (\(start, _, _, _) -> start) (syntaxScopes (sourceSyntaxSummary source)), let binder = (binderStart, binderEnd), let scope = (scopeStart, scopeEnd)]
  where
    source = "let f: [n: ℕ, x: n fan, ℕ] ≔ (let k ≔ n yield {0 ^ k, m heir ^ m} x)\nflock got: [α: *, *] { let get: α }\n"
    slice (start, end) = take (end - start) (drop start source)
