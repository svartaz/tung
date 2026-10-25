-- effects, trusted host bindings, text literals, and the dependent runner.
module Test.DependentEffect (group) where

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
  example <- exampleSource "effect_loop.tung"
  library <- loadLibrary ["_foreign.tung", "type/one.tung", "type/optional.tung", "type/and.tung"]
  Harness.group "dependent_effect" (hostSchemaTests ++ yieldTests ++ tests library example)

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
      first <- either fail pure (compileAs "yield.tung" "let value ≔ +7")
      second <- either fail pure (compileAs "yield.tung" "let value ≔ 'other'")
      borrowed <- either fail pure (inferSourceExpression first "value")
      transferred <- traverse (\owner -> runYield host owner borrowed) [first, second]
      expectEq
        "yield validateth its judgement in the supplied environment before erasure"
        [Right "+7", Left "cannot unify ℤ with *", Right "+7", Left "cannot unify string with ℤ"]
        (map (fmap renderRuntime) (actual ++ transferred))
  ]

tests :: Library -> String -> [Test]
tests library example =
  [ expectEq "the effect example writeth, repeateth, and readeth through the host" (Right (Right 0, "tung tung \nwhat is thy name? hail, sumi!\n")) $
      run example ["sumi"],
    expectEq "a host effect reporteth an absent line as none" (Right (Right 0, "tung tung \nwhat is thy name? nobody\n")) $
      run example [],
    expectEq "a fast effect loopeth until input endeth" (Right (Right 0, "a\nb\n")) $
      run (withoutMain example ++ "let main:𝟙 effect ≔ echo\n") ["a", "b"],
    expectEq "building an effect performeth nothing; only main is executed" (Right (Right 0, "")) $
      run (prelude ++ "let unused:𝟙 effect ≔ 'never' write\nlet main:𝟙 effect ≔ only effect_sheer\n") [],
    expectEq "a bind continuation is inspected after the preceding host action" (Right (Left "reached sorry", "before")) $
      run (prelude ++ "let main:𝟙 effect ≔ ('before' write) effect_bind (sorry:[𝟙, 𝟙 effect])\n") [],
    expectEq "a performed effect computeth every result field before its continuation" (Right (Left "reached sorry", "")) $
      run
        ( prelude
            ++ """
               type box: * { box_of: [nested: ℤ optional, box] }
               let main:𝟙 effect ≔
                 ((((sorry:ℤ) some) box_of) effect_sheer) effect_bind {_ ^ 'never' write}

               """
        )
        [],
    -- each call's inputs are evaluated when it is performed, so the count
    -- holdeth no chain of pending additions.
    expectEq "a fast function carrieth a value between rounds" (Right (Right 0, "20000")) $
      run
        ( prelude
            ++ """
               let plus:[ℤ, ℤ, ℤ] ≔ 'add_integer' foreign
               fast count:[whole: ℤ, 𝟙 effect] ≔ read effect_bind {
                 none ^ (whole integer_to_string) write,
                 _ some ^ (whole plus +1) count
               }
               let main:𝟙 effect ≔ +0 count

               """
        )
        (replicate 20000 ""),
    expectEq "a fast main may name itself" (Right (Right 0, "a\n")) $
      run (prelude ++ "fast main:𝟙 effect ≔ read effect_bind {none ^ only effect_sheer, line some ^ (line write) effect_bind {_ ^ ('\\n' write) effect_bind {_ ^ main}}}\n") ["a"],
    expectEq "a fast declaration may be universe-polymorphic" (Right (Right 0, "xx")) $
      run
        ( prelude
            ++ """
               fast twice:[@α: *, n: 𝟙 optional, step: α effect, α effect] ≔ match n {
                 none ^ step,
                 _ some ^ step effect_bind {_ ^ none twice step}
               }
               let main:𝟙 effect ≔ (only some) twice ('x' write)

               """
        )
        [],
    expectEq "a fast call doth not unfold during checking" (Right False) $ do
      program <- compile (prelude ++ "fast turn:𝟙 effect ≔ (only effect_sheer) effect_bind {_ ^ turn}\n")
      left <- normaliseSourceExpression program "turn"
      right <- normaliseSourceExpression program "(only effect_sheer) effect_bind {_ ^ turn}"
      pure (eraseLevels left == eraseLevels right),
    rejectContaining "a fast type endeth in an effect, so it cannot inhabit an empty type" "must end in an effect" $
      compile (prelude ++ "type none_at_all:* {}\nfast absurd:none_at_all ≔ absurd\n"),
    rejectContaining "a fast function's result is an effect" "must end in an effect" $
      compile (prelude ++ "fast forever:[𝟙, 𝟙] ≔ {x ^ x forever}\n"),
    rejectContaining "a looping effect let is pointed to fast" "'echo' needs a structurally decreasing input; an effect that loopeth without bound is a fast declaration" $
      compile (prelude ++ "let echo:𝟙 effect ≔ read effect_bind {none ^ only effect_sheer, _ some ^ echo}\n"),
    rejectContaining "a fast declaration nameth itself" "one that doth not is a let" $
      compile (prelude ++ "fast still:𝟙 effect ≔ only effect_sheer\n"),
    rejectContaining "a fast declaration requireth an annotation" "requireth a type annotation" $
      parseSource "fast echo ≔ echo\n",
    rejectContaining "a fast declaration cannot bind a host key" "a foreign binding is a let, not fast" $
      parseSource "fast write:[string, 𝟙 effect] ≔ 'write' foreign\n",
    rejectContaining "fast declarations cannot enter a let block" "must be top-level" $
      parseSource "let value ≔ (fast again:𝟙 effect ≔ again yield *)\n",
    rejectContaining "a bizen member is not fast" "a bizen member is a let, not fast" $
      compile (prelude ++ "class looping:[α:*, *] { let go:α }\nbizen:𝟙 effect looping { fast go:𝟙 effect ≔ go }\n"),
    expectEq "binding a sheer effect doth not reduce during checking" (Right False) $ do
      program <- compile prelude
      left <- normaliseSourceExpression program "(only effect_sheer) effect_bind {x ^ x effect_sheer}"
      right <- normaliseSourceExpression program "only effect_sheer"
      pure (eraseLevels left == eraseLevels right),
    expectEq "same string literals convert and different ones do not" (Right [True, False]) $ do
      program <- compile (prelude ++ "type same:[@α:*, x:α, [α, *]] { refl:(x same @α x) }\n")
      pure [either (const False) (const True) (inferSourceExpression program source) | source <- ["(refl : 'a' same 'a')", "(refl : 'a' same 'b')"]],
    expectEq "a string literal hath the primitive string type" (Right True) $ do
      program <- compile prelude
      literal <- inferSourceExpression program "'hello'"
      text <- normaliseSourceExpression program "string"
      pure (eraseLevels (inferredType literal) == eraseLevels text),
    rejectContaining "an unknown host key is rejected" "unknown host key 'launch'" $
      compile "let launch:* ≔ 'launch' foreign\n",
    rejectContaining "a host type must match its catalogue signature" "requireth a different type" $
      compile "let sheer:[@α:*, α, α] ≔ 'effect_sheer' foreign\n",
    rejectContaining "an effect operation cannot use a different effect type" "requireth a different type" $
      compile "type _box:[α:*, *] { box:[α, α _box] }\nlet sheer:[@α:*, α, α _box] ≔ 'effect_sheer' foreign\n",
    rejectContaining "host data is identified by its declaration" "requireth a different type" $
      compile "type 𝟙:* { only:𝟙 }\nlet write:[string, 𝟙 effect] ≔ 'write' foreign\n",
    rejectContaining "one host key cannot be bound twice" "already bound" $
      compile (prelude ++ "let other:[string, 𝟙 effect] ≔ 'write' foreign\n"),
    -- a model is the binding's body: checked against its annotation, with
    -- calls of its own name as structural recursion, for a pure operation.
    rejectContaining "a model is checked against the binding's type" "cannot unify" $
      compile "let plus:[ℕ, ℕ, ℕ] ≔ 'add_natural' foreign {a, b ^ +1}\n",
    -- the model shareth the binding's checked type, so its universe
    -- parameters agree even when the annotation nameth several families.
    expectEq "a model's annotation may name several universe-polymorphic families" (Right ()) $
      () <$ compileWith library "type/natural.tung" (prelude ++ "bring type/and.tung\nlet divide:[ℕ, ℕ, (ℕ ∧ ℕ) optional] ≔ 'divide_leftover_natural' foreign {_, _ ^ none}\n"),
    -- only the library file whose model is tested may give one, so a wrong
    -- model elsewhere cannot make a proof contradict a computation.
    rejectContaining "a model belongeth to its catalogued library file" "belongeth to type/natural.tung" $
      compile (prelude ++ "let plus:[ℕ, ℕ, ℕ] ≔ 'add_natural' foreign {a, _ ^ a}\n"),
    expectEq "a catalogued file checked by its full path may give its model" (Right ()) $
      () <$ compileWith library "/checked/library/type/natural.tung" (prelude ++ "let plus:[ℕ, ℕ, ℕ] ≔ 'add_natural' foreign {a, _ ^ a}\n"),
    rejectContaining "only a sheer operation hath a model" "cannot have a model" $
      compile "let wrap:[@α:*, a: α, α effect] ≔ 'effect_sheer' foreign sorry\n",
    rejectContaining "without a model, a foreign annotation cannot bind inputs" "cannot bind inputs" $
      parseSource "let plus:[m: ℕ, n: ℕ, ℕ] ≔ 'add_natural' foreign\n",
    rejectContaining "a foreign binding requireth an annotation" "requireth a type annotation" $
      parseSource "let effect ≔ 'effect' foreign\n",
    rejectContaining "foreign cannot appear inside an expression" "only an annotated top-level let" $
      parseSource "let value:* ≔ ('effect' foreign)\n",
    rejectContaining "foreign bindings cannot enter a let block" "must be top-level" $
      parseSource "let value ≔ (let write:[string, 𝟙 effect] ≔ 'write' foreign yield *)\n",
    rejectContaining "a family cannot hide negative recursion inside an effect" "direct saturated family application" $
      compile (prelude ++ "type bad:* { make:[[bad, 𝟙] effect, bad] }\n"),
    rejectContaining "main requireth a unit effect type" "main requireth a unit effect type" $
      run (prelude ++ "let main:(string optional) effect ≔ read\n") [],
    rejectContaining "a runnable program requireth main" "requireth a top-level main" $
      run prelude []
  ]
  where
    compile = compileWith library "effect_example.tung"
    -- a simulated host readeth queued lines and recordeth written text.
    run source inputs = compile source >>= (`runSimulated` inputs)

-- the expected identities alone cannot establish a host data representation.
hostSchemaTests :: [Test]
hostSchemaTests =
  [ malformed
      "an empty canonical truth type cannot receive a host result"
      truthBinding
      [("type/two.tung", "show type 𝟚:* {}\n")],
    rejectContaining "a data family cannot counterfeit an opaque task handle" "requireth a different type" $
      compileProject
        (SourceModule "host_schema.tung")
        "bring type/task.tung let fork:[@α:*, α effect, (α task) effect] ≔ 'fork' foreign"
        (Map.singleton "type/task.tung" "show type task:[α:*, *] { done:[α, α task] }"),
    malformed
      "a canonical optional requireth its named constructors"
      """
      bring type/optional.tung
      let read:(string optional) effect ≔ 'read' foreign

      """
      [("type/optional.tung", "show type optional:[α:*, *] { absent:α optional, present:[α, α optional] }\n")],
    malformed
      "a canonical list requireth its element field type"
      """
      bring type/list.tung
      let to_string:[unicode list, string] ≔ 'list_to_string' foreign

      """
      [("type/list.tung", wrongList)],
    malformed
      "nested host schemas validate their stored data"
      """
      bring web/request.tung
      bring web/response.tung
      let serve:[ℕ, [_request, _response effect], string effect] ≔ 'serve' foreign

      """
      [ ( "web/request.tung",
          """
          bring type/wordbook.tung
          show type _request:* { request:[string, string, string wordbook string, string, _request] }

          """
        ),
        ( "web/response.tung",
          """
          bring type/wordbook.tung
          show type _response:* { response:[ℕ, string wordbook string, string, _response] }

          """
        ),
        ( "type/wordbook.tung",
          """
          bring type/list.tung
          bring type/and.tung
          show type wordbook:[α:*, β:*, *] { from_list:[(α ∧ β) list, α wordbook β] }

          """
        ),
        ("type/and.tung", "show type ∧:[α:*, β:*, *] { ⸴:[α, β, α ∧ β] }\n"),
        ("type/list.tung", wrongList)
      ],
    expectEq "canonical host constructors may be reordered" (Right True) do
      program <- compileProject (SourceModule "host_schema.tung") truthBinding (Map.singleton "type/two.tung" "show type 𝟚:* { nay:𝟚, yea:𝟚 }\n")
      sameNormalIn program "+0 same +0" "yea"
  ]
  where
    truthBinding =
      """
      bring type/two.tung
      let same:[ℤ, ℤ, 𝟚] ≔ 'equal_integer' foreign

      """
    wrongList = "show type list:[α:*, *] { empty:α list, ‥:[ℤ, α list, α list] }\n"
    malformed label source modules = rejectContaining label "requireth its catalogued constructors" (compileProject (SourceModule "host_schema.tung") source (Map.fromList modules))

-- main is the example's final declaration.
withoutMain :: String -> String
withoutMain = unlines . takeWhile (not . isPrefixOf "let main:") . lines

-- the library's host bindings, unit, and option.
prelude :: String
prelude = "bring _foreign.tung\nbring type/one.tung\nbring type/optional.tung\n"
