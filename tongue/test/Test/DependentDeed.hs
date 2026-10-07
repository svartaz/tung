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
  example <- exampleSource "dependent_deed.tung"
  library <- loadLibrary ["_foreign.tung", "ilk/one.tung", "ilk/maybe.tung"]
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
        [Right "+7", Left "cannot unify ℤ with *", Right "+7", Left "cannot unify text with ℤ"]
        (map (fmap renderRuntime) (actual ++ transferred))
  ]

tests :: Library -> String -> [Test]
tests library example =
  [ expectEq "the deed example writeth, repeateth, and readeth through the host" (Right (Right 0, "tung tung \nwhat is thy name? hail, sumi!\n")) $
      run example ["sumi"],
    expectEq "a host deed reporteth an absent line as none" (Right (Right 0, "tung tung \nwhat is thy name? nobody\n")) $
      run example [],
    expectEq "the deed fixed point loopeth until input endeth" (Right (Right 0, "a\nb\n")) $
      run (withoutMain example ++ "let main:𝟙 deed ≔ echo\n") ["a", "b"],
    expectEq "building a deed performeth nothing; only main is executed" (Right (Right 0, "")) $
      run (prelude ++ "let unused:𝟙 deed ≔ 'never' write\nlet main:𝟙 deed ≔ only deed_sheer\n") [],
    expectEq "a bind continuation is inspected after the preceding host action" (Right (Left "reached sorry", "before")) $
      run (prelude ++ "let main:𝟙 deed ≔ ('before' write) deed_bind (sorry:[𝟙, 𝟙 deed])\n") [],
    expectEq "a performed deed computeth every result field before its continuation" (Right (Left "reached sorry", "")) $
      run
        ( prelude
            ++ """
               let main:𝟙 deed ≔
                 (r{nested ≔ (sorry:ℤ) some} deed_sheer) deed_bind {_ ^ 'never' write}

               """
        )
        [],
    expectEq "a deed fixed point accumulateth without printing intermediate results" (Right (Right 0, "2000")) $
      run
        ( prelude
            ++ """
               let plus:[ℤ, ℤ, ℤ] ≔ 'eke_integer' fremmed
               let collect:[ℤ, 𝟙 deed] deed ≔ {again ^
                 {whole ^ read deed_bind {
                   none ^ (whole integer_to_text) write,
                   _ some ^ (whole plus +1) deed_sheer $ deed_bind {next ^
                     again deed_bind {loop ^ next loop}
                   }
                 }} deed_sheer
               } deed_fix
               let main:𝟙 deed ≔ collect deed_bind {loop ^ +0 loop}

               """
        )
        (replicate 2000 ""),
    expectEq "binding a sheer deed doth not reduce during checking" (Right False) $ do
      program <- compile prelude
      left <- normaliseSourceExpression program "(only deed_sheer) deed_bind {x ^ x deed_sheer}"
      right <- normaliseSourceExpression program "only deed_sheer"
      pure (eraseLevels left == eraseLevels right),
    expectEq "same text literals convert and different ones do not" (Right [True, False]) $ do
      program <- compile (prelude ++ "ilk same:[@α:*, x:α, [α, *]] { refl:(x same @α x) }\n")
      pure [either (const False) (const True) (inferSourceExpression program source) | source <- ["(refl : 'a' same 'a')", "(refl : 'a' same 'b')"]],
    expectEq "a text literal hath the primitive text type" (Right True) $ do
      program <- compile prelude
      literal <- inferSourceExpression program "'hello'"
      text <- normaliseSourceExpression program "text"
      pure (eraseLevels (inferredType literal) == eraseLevels text),
    rejectContaining "a text literal cannot inhabit another type" "cannot unify" $
      compile (prelude ++ "let wrong:𝟙 ≔ 'hello'\n"),
    rejectContaining "an unknown host key is rejected" "unknown host key 'launch'" $
      compile "let launch:* ≔ 'launch' fremmed\n",
    rejectContaining "a host type must match its catalogue signature" "requireth a different type" $
      compile "let sheer:[@α:*, α, α] ≔ 'deed_sheer' fremmed\n",
    rejectContaining "a deed operation cannot use a different deed type" "requireth a different type" $
      compile "ilk _box:[α:*, *] { box:[α, α _box] }\nlet sheer:[@α:*, α, α _box] ≔ 'deed_sheer' fremmed\n",
    rejectContaining "host data is identified by its declaration" "requireth a different type" $
      compile "ilk 𝟙:* { only:𝟙 }\nlet write:[text, 𝟙 deed] ≔ 'write' fremmed\n",
    rejectContaining "one host key cannot be bound twice" "already bound" $
      compile (prelude ++ "let other:[text, 𝟙 deed] ≔ 'write' fremmed\n"),
    -- a model is the binding's body: checked against its annotation, with
    -- calls of its own name as structural recursion, for a pure operation.
    rejectContaining "a model is checked against the binding's type" "cannot unify" $
      compile "let plus:[ℕ, ℕ, ℕ] ≔ 'eke_natural' fremmed {a, b ^ +1}\n",
    rejectContaining "only a sheer operation hath a model" "cannot have a model" $
      compile "let wrap:[@α:*, a: α, α deed] ≔ 'deed_sheer' fremmed sorry\n",
    rejectContaining "without a model, a fremmed annotation cannot bind inputs" "cannot bind inputs" $
      parseSource "let plus:[m: ℕ, n: ℕ, ℕ] ≔ 'eke_natural' fremmed\n",
    rejectContaining "a fremmed binding requireth an annotation" "requireth a type annotation" $
      parseSource "let deed ≔ 'deed' fremmed\n",
    rejectContaining "fremmed cannot appear inside an expression" "only an annotated top-level let" $
      parseSource "let worth:* ≔ ('deed' fremmed)\n",
    rejectContaining "fremmed bindings cannot enter a let block" "must be top-level" $
      parseSource "let worth ≔ (let write:[text, 𝟙 deed] ≔ 'write' fremmed yield *)\n",
    rejectContaining "a family cannot hide undernaught selfcalling inside a deed" "direct saturated family application" $
      compile (prelude ++ "ilk bad:* { make:[[bad, 𝟙] deed, bad] }\n"),
    rejectContaining "main requireth a unit deed type" "main requireth a unit deed type" $
      run (prelude ++ "let main:(text maybe) deed ≔ read\n") [],
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
    rejectContaining "a data family cannot counterfeit an opaque task handle" "requireth a different type" $
      compileProject
        (SourceModule "host_schema.tung")
        "use ilk/task.tung let fork:[@α:*, α deed, (α task) deed] ≔ 'fork' fremmed"
        (Map.singleton "ilk/task.tung" "show ilk task:[α:*, *] { done:[α, α task] }"),
    malformed
      "a canonical maybe requireth its named constructors"
      """
      use ilk/maybe.tung
      let read:(text maybe) deed ≔ 'read' fremmed

      """
      [("ilk/maybe.tung", "show ilk maybe:[α:*, *] { absent:α maybe, present:[α, α maybe] }\n")],
    malformed
      "a canonical list requireth its element field type"
      """
      use ilk/list.tung
      let to_text:[unicode list, text] ≔ 'list_to_text' fremmed

      """
      [("ilk/list.tung", wrongList)],
    malformed
      "nested host schemas validate their stored data"
      """
      use web/request.tung
      use web/response.tung
      let serve:[ℕ, [_request, _response deed], text deed] ≔ 'serve' fremmed

      """
      [ ( "web/request.tung",
          """
          use ilk/table.tung
          show ilk _request:* { request:[text, text, text table text, text, _request] }

          """
        ),
        ( "web/response.tung",
          """
          use ilk/table.tung
          show ilk _response:* { response:[ℕ, text table text, text, _response] }

          """
        ),
        ( "ilk/table.tung",
          """
          use ilk/list.tung
          use ilk/product.tung
          show ilk table:[α:*, β:*, *] { from_list:[(α ∏ β) list, α table β] }

          """
        ),
        ("ilk/product.tung", "show ilk ∏:[α:*, β:*, *] { both:[α, β, α ∏ β] }\n"),
        ("ilk/list.tung", wrongList)
      ],
    expectEq "canonical host constructors may be reordered" (Right True) do
      program <- compileProject (SourceModule "host_schema.tung") truthBinding (Map.singleton "ilk/two.tung" "show ilk 𝟚:* { nay:𝟚, yea:𝟚 }\n")
      sameNormalIn program "+0 same +0" "yea"
  ]
  where
    truthBinding =
      """
      use ilk/two.tung
      let same:[ℤ, ℤ, 𝟚] ≔ 'same_integer' fremmed

      """
    wrongList = "show ilk list:[α:*, *] { empty:α list, ‥:[ℤ, α list, α list] }\n"
    malformed label source modules = rejectContaining label "requireth its catalogued constructors" (compileProject (SourceModule "host_schema.tung") source (Map.fromList modules))

-- main is the example's final declaration.
withoutMain :: String -> String
withoutMain = unlines . takeWhile (not . isPrefixOf "let main:") . lines

-- bookhoard's host bindings, unit, and option.
prelude :: String
prelude = "use _foreign.tung\nuse ilk/one.tung\nuse ilk/maybe.tung\n"
