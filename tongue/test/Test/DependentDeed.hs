-- deeds, trusted host bindings, text literals, and the dependent runner.
module Test.DependentDeed (group) where

import Data.List (isPrefixOf)
import Data.Map.Strict qualified as Map
import Test.Compile (compileProject)
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent
import Tung.Dependent.Run (ioHost, renderRuntime, runYield)
import Tung.Dependent.Source (inferSourceExpression, normaliseSourceExpression, parseSource, sourceEnvironment)

group :: IO Harness.Group
group = do
  example <- exampleSource "deed_loop.tung"
  library <- loadLibrary ["_fremmed.tung", "ilk/one.tung", "ilk/maybe.tung", "ilk/and.tung"]
  Harness.group "dependent_deed" (hostSchemaTests ++ yieldTests ++ tests library example)

-- public erasure requireth a complete, validated typing judgement.
yieldTests :: [Test]
yieldTests =
  [ do
      program <- either fail pure (compileAs "yield.tung" "")
      host <- ioHost []
      let integer = Global (SymbolId PrimitiveModule "ℤ") []
          literal = Literal (SymbolId PrimitiveModule "ℤ") (IntegerValue 7)
          wrong = Inferred 0 [] (Apply Explicit (Lambda Explicit (Sort LZero) (Local 0)) literal) integer
      checked <- either fail pure (infer (sourceEnvironment program) literal)
      actual <- traverse (runYield host program) [checked, wrong]
      first <- either fail pure (compileAs "yield.tung" "let worth ≔ +7")
      second <- either fail pure (compileAs "yield.tung" "let worth ≔ 'other'")
      borrowed <- either fail pure (inferSourceExpression first "worth")
      transferred <- traverse (\owner -> runYield host owner borrowed) [first, second]
      expectEq
        "yield validateth its judgement in the supplied environment before erasure"
        [Right "+7", Left "cannot unify ℤ with *", Right "+7", Left "cannot unify string with ℤ"]
        (map (fmap renderRuntime) (actual ++ transferred))
  ]

tests :: Library -> String -> [Test]
tests library example =
  [ expectEq "the deed example writeth, repeateth, and readeth through the host" (Right (Right 0, "tung tung \nwhat is thy name? hail, sumi!\n")) $
      run example ["sumi"],
    expectEq "a host deed reporteth an absent line as none" (Right (Right 0, "tung tung \nwhat is thy name? nobody\n")) $
      run example [],
    expectEq "a fast deed loopeth until input endeth" (Right (Right 0, "a\nb\n")) $
      run (withoutMain example ++ "let main:𝟙 deed ≔ echo\n") ["a", "b"],
    expectEq "building a deed performeth nothing; only main is executed" (Right (Right 0, "")) $
      run (prelude ++ "let unused:𝟙 deed ≔ 'never' write\nlet main:𝟙 deed ≔ only deed_sheer\n") [],
    expectEq "a bind continuation is inspected after the preceding host action" (Right (Left "reached sorry", "before")) $
      run (prelude ++ "let main:𝟙 deed ≔ ('before' write) deed_bind (sorry:[𝟙, 𝟙 deed])\n") [],
    expectEq "a performed deed computeth every result field before its continuation" (Right (Left "reached sorry", "")) $
      run
        ( prelude
            ++ """
               ilk box: * { box_of: [nested: ℤ maybe, box] }
               let main:𝟙 deed ≔
                 ((((sorry:ℤ) some) box_of) deed_sheer) deed_bind {_ ^ 'never' write}

               """
        )
        [],
    -- each call's inputs are evaluated when it is performed, so the count
    -- holdeth no chain of pending additions.
    expectEq "a fast function carrieth a worth between rounds" (Right (Right 0, "20000")) $
      run
        ( prelude
            ++ """
               let plus:[ℤ, ℤ, ℤ] ≔ 'eke_wholetale' fremmed
               fast count:[whole: ℤ, 𝟙 deed] ≔ read deed_bind {
                 none ^ (whole wholetale_to_string) write,
                 _ some ^ (whole plus +1) count
               }
               let main:𝟙 deed ≔ +0 count

               """
        )
        (replicate 20000 ""),
    expectEq "a fast main may name itself" (Right (Right 0, "a\n")) $
      run (prelude ++ "fast main:𝟙 deed ≔ read deed_bind {none ^ only deed_sheer, line some ^ (line write) deed_bind {_ ^ ('\\n' write) deed_bind {_ ^ main}}}\n") ["a"],
    expectEq "a fast declaration may be universe-polymorphic" (Right (Right 0, "xx")) $
      run
        ( prelude
            ++ """
               fast twice:[@α: *, n: 𝟙 maybe, step: α deed, α deed] ≔ match n {
                 none ^ step,
                 _ some ^ step deed_bind {_ ^ none twice step}
               }
               let main:𝟙 deed ≔ (only some) twice ('x' write)

               """
        )
        [],
    expectEq "a fast call doth not unfold during checking" (Right False) $ do
      program <- compile (prelude ++ "fast spin:𝟙 deed ≔ (only deed_sheer) deed_bind {_ ^ spin}\n")
      left <- normaliseSourceExpression program "spin"
      right <- normaliseSourceExpression program "(only deed_sheer) deed_bind {_ ^ spin}"
      pure (eraseLevels left == eraseLevels right),
    rejectContaining "a fast ilk endeth in a deed, so it cannot inhabit an empty ilk" "must end in a deed" $
      compile (prelude ++ "ilk none_at_all:* {}\nfast absurd:none_at_all ≔ absurd\n"),
    rejectContaining "a fast function's result is a deed" "must end in a deed" $
      compile (prelude ++ "fast forever:[𝟙, 𝟙] ≔ {x ^ x forever}\n"),
    rejectContaining "a looping deed let is pointed to fast" "'echo' needs a structurally decreasing input; a deed that loopeth without bound is a fast declaration" $
      compile (prelude ++ "let echo:𝟙 deed ≔ read deed_bind {none ^ only deed_sheer, _ some ^ echo}\n"),
    rejectContaining "a fast declaration nameth itself" "one that doth not is a let" $
      compile (prelude ++ "fast still:𝟙 deed ≔ only deed_sheer\n"),
    rejectContaining "a fast declaration requireth an annotation" "requireth an ilk annotation" $
      parseSource "fast echo ≔ echo\n",
    rejectContaining "a fast declaration cannot bind a host key" "a fremmed binding is a let, not fast" $
      parseSource "fast write:[string, 𝟙 deed] ≔ 'write' fremmed\n",
    rejectContaining "fast declarations cannot enter a let block" "must be top-level" $
      parseSource "let worth ≔ (fast again:𝟙 deed ≔ again yield *)\n",
    rejectContaining "a bizen member is not fast" "a bizen member is a let, not fast" $
      compile (prelude ++ "flock looping:[α:*, *] { let go:α }\nbizen:𝟙 deed looping { fast go:𝟙 deed ≔ go }\n"),
    expectEq "binding a sheer deed doth not reduce during checking" (Right False) $ do
      program <- compile prelude
      left <- normaliseSourceExpression program "(only deed_sheer) deed_bind {x ^ x deed_sheer}"
      right <- normaliseSourceExpression program "only deed_sheer"
      pure (eraseLevels left == eraseLevels right),
    expectEq "same string literals convert and different ones do not" (Right [True, False]) $ do
      program <- compile (prelude ++ "ilk same:[@α:*, x:α, [α, *]] { refl:(x same @α x) }\n")
      pure [either (const False) (const True) (inferSourceExpression program source) | source <- ["(refl : 'a' same 'a')", "(refl : 'a' same 'b')"]],
    expectEq "a string literal hath the primitive string type" (Right True) $ do
      program <- compile prelude
      literal <- inferSourceExpression program "'hello'"
      text <- normaliseSourceExpression program "string"
      pure (eraseLevels (inferredType literal) == eraseLevels text),
    rejectContaining "an unknown host key is rejected" "unknown host key 'launch'" $
      compile "let launch:* ≔ 'launch' fremmed\n",
    rejectContaining "a host type must match its catalogue signature" "requireth a different ilk" $
      compile "let sheer:[@α:*, α, α] ≔ 'deed_sheer' fremmed\n",
    rejectContaining "a deed operation cannot use a different deed type" "requireth a different ilk" $
      compile "ilk _box:[α:*, *] { box:[α, α _box] }\nlet sheer:[@α:*, α, α _box] ≔ 'deed_sheer' fremmed\n",
    rejectContaining "host data is identified by its declaration" "requireth a different ilk" $
      compile "ilk 𝟙:* { only:𝟙 }\nlet write:[string, 𝟙 deed] ≔ 'write' fremmed\n",
    rejectContaining "one host key cannot be bound twice" "already bound" $
      compile (prelude ++ "let other:[string, 𝟙 deed] ≔ 'write' fremmed\n"),
    -- a model is the binding's body: checked against its annotation, with
    -- calls of its own name as structural recursion, for a pure operation.
    rejectContaining "a model is checked against the binding's type" "cannot unify" $
      compile "let plus:[ℕ, ℕ, ℕ] ≔ 'eke_kindful' fremmed {a, b ^ +1}\n",
    -- the model shareth the binding's checked type, so its universe
    -- parameters agree even when the annotation nameth several families.
    expectEq "a model's annotation may name several universe-polymorphic families" (Right ()) $
      () <$ compile (prelude ++ "bring ilk/and.tung\nlet deal:[ℕ, ℕ, (ℕ ∧ ℕ) maybe] ≔ 'deal_leftover_kindful' fremmed {_, _ ^ none}\n"),
    rejectContaining "only a sheer operation hath a model" "cannot have a model" $
      compile "let wrap:[@α:*, a: α, α deed] ≔ 'deed_sheer' fremmed sorry\n",
    rejectContaining "without a model, a fremmed annotation cannot bind inputs" "cannot bind inputs" $
      parseSource "let plus:[m: ℕ, n: ℕ, ℕ] ≔ 'eke_kindful' fremmed\n",
    rejectContaining "a fremmed binding requireth an annotation" "requireth an ilk annotation" $
      parseSource "let deed ≔ 'deed' fremmed\n",
    rejectContaining "fremmed cannot appear inside an expression" "only an annotated top-level let" $
      parseSource "let worth:* ≔ ('deed' fremmed)\n",
    rejectContaining "fremmed bindings cannot enter a let block" "must be top-level" $
      parseSource "let worth ≔ (let write:[string, 𝟙 deed] ≔ 'write' fremmed yield *)\n",
    rejectContaining "a family cannot hide undernaught selfcalling inside a deed" "direct saturated family application" $
      compile (prelude ++ "ilk bad:* { make:[[bad, 𝟙] deed, bad] }\n"),
    rejectContaining "main requireth a unit deed type" "main requireth a unit deed ilk" $
      run (prelude ++ "let main:(string maybe) deed ≔ read\n") [],
    rejectContaining "a runnable forewrit requireth main" "requireth a top-level main" $
      run prelude []
  ]
  where
    compile = compileWith library "deed_example.tung"
    -- a simulated host readeth queued lines and recordeth written text.
    run source inputs = compile source >>= (`runSimulated` inputs)

-- the expected identities alone cannot establish a host data representation.
hostSchemaTests :: [Test]
hostSchemaTests =
  [ malformed
      "an empty canonical truth type cannot receive a host result"
      truthBinding
      [("ilk/two.tung", "show ilk 𝟚:* {}\n")],
    rejectContaining "a data family cannot counterfeit an opaque task handle" "requireth a different ilk" $
      compileProject
        (SourceModule "host_schema.tung")
        "bring ilk/task.tung let fork:[@α:*, α deed, (α task) deed] ≔ 'fork' fremmed"
        (Map.singleton "ilk/task.tung" "show ilk task:[α:*, *] { done:[α, α task] }"),
    malformed
      "a canonical maybe requireth its named constructors"
      """
      bring ilk/maybe.tung
      let read:(string maybe) deed ≔ 'read' fremmed

      """
      [("ilk/maybe.tung", "show ilk maybe:[α:*, *] { absent:α maybe, present:[α, α maybe] }\n")],
    malformed
      "a canonical list requireth its element field type"
      """
      bring ilk/list.tung
      let to_string:[unicode list, string] ≔ 'list_to_string' fremmed

      """
      [("ilk/list.tung", wrongList)],
    malformed
      "nested host schemas validate their stored data"
      """
      bring web/request.tung
      bring web/response.tung
      let serve:[ℕ, [_request, _response deed], string deed] ≔ 'serve' fremmed

      """
      [ ( "web/request.tung",
          """
          bring ilk/wordbook.tung
          show ilk _request:* { request:[string, string, string wordbook string, string, _request] }

          """
        ),
        ( "web/response.tung",
          """
          bring ilk/wordbook.tung
          show ilk _response:* { response:[ℕ, string wordbook string, string, _response] }

          """
        ),
        ( "ilk/wordbook.tung",
          """
          bring ilk/list.tung
          bring ilk/and.tung
          show ilk wordbook:[α:*, β:*, *] { from_list:[(α ∧ β) list, α wordbook β] }

          """
        ),
        ("ilk/and.tung", "show ilk ∧:[α:*, β:*, *] { ⸴:[α, β, α ∧ β] }\n"),
        ("ilk/list.tung", wrongList)
      ],
    expectEq "canonical host constructors may be reordered" (Right True) do
      program <- compileProject (SourceModule "host_schema.tung") truthBinding (Map.singleton "ilk/two.tung" "show ilk 𝟚:* { nay:𝟚, yea:𝟚 }\n")
      sameNormalIn program "+0 same +0" "yea"
  ]
  where
    truthBinding =
      """
      bring ilk/two.tung
      let same:[ℤ, ℤ, 𝟚] ≔ 'same_wholetale' fremmed

      """
    wrongList = "show ilk list:[α:*, *] { empty:α list, ‥:[ℤ, α list, α list] }\n"
    malformed label source modules = rejectContaining label "requireth its catalogued constructors" (compileProject (SourceModule "host_schema.tung") source (Map.fromList modules))

-- main is the example's final declaration.
withoutMain :: String -> String
withoutMain = unlines . takeWhile (not . isPrefixOf "let main:") . lines

-- bookhoard's host bindings, unit, and option.
prelude :: String
prelude = "bring _fremmed.tung\nbring ilk/one.tung\nbring ilk/maybe.tung\n"
