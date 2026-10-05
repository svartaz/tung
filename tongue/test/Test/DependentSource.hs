-- source examples are checked again by the independent dependent kernel.
module Test.DependentSource (group) where

import Control.Monad (forM_)
import Test.DependentSupport
import Test.Harness (Group, Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent
import Tung.Dependent.Source (Hole (..), SourceProgram, compileSource, inferSourceExpression, normaliseSourceExpression, parseSource, sourceDefinitions, sourceEnvironment, sourceHoles, typeOfName)

group :: IO Group
group = Harness.group "dependent-source" (elaborationTests ++ shadowingTests ++ implicitInferenceTests ++ delayedComputationTests ++ rejectionTests)

shadowingTests :: [Test]
shadowingTests =
  [ expectEq label (Right True) do
      program <- compile source
      sameNormalIn program actual expected
  | (label, source, actual, expected) <-
      [ ("a header binder may share its declaration's name", "let identity:[identity:ℤ, ℤ] ≔ identity", "+1 identity", "+1"),
        ("an inferred lambda binder may share its declaration's name", "let identity ≔ {identity ^ identity}", "+1 identity", "+1"),
        ("a local binding hides its enclosing declaration's name", "let value ≔ (let value ≔ +1 yield value)", "value", "+1"),
        ("a case variable may share its declaration's name", "let predecessor:[ℕ, ℕ] ≔ {0 ^ 0, predecessor succeed ^ predecessor}", "2 predecessor", "1"),
        ("a local function's binder is not a recursive reference", "let outer:[ℤ, ℤ] ≔ {x ^ (let inner ≔ {inner ^ inner} yield x inner)}", "+1 outer", "+1"),
        ("a product parameter may share its alias's name", "let endo ≔ [endo:*, endo, endo]", "endo", "[α:*, α, α]")
      ]
  ]

elaborationTests :: [Test]
elaborationTests =
  [ expectEq "definitions retain their source identities" (Right [SymbolId sourceModule "alias", SymbolId sourceModule "identity"]) $ do
      program <- compileSource sourceModule (aliasSource ++ identitySource)
      pure (map fst (sourceDefinitions program)),
    expectEq "source definitions carry kernel-checked judgements" (Right ()) $ do
      program <- compile (aliasSource ++ identitySource)
      forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd),
    expectEq "a source universe inhabiteþ a larger universe" (Right True) $ do
      result <- inferIn "" "*"
      pure case (inferredTerm result, inferredType result) of
        (Sort lower, Sort upper) -> universeEntails (inferredConstraints result) (LevelEqual (LSucc lower) upper)
        _ -> False,
    normal "application substituteþ the supplied type" identitySource "* identity *" (Sort LZero),
    expectEq "each global use receiveþ fresh universe arguments" (Right ()) (checkedIn identitySource "[α:*, x:α, α] identity identity"),
    normal "type aliases use the same application syntax" aliasSource "* alias" (Sort LZero),
    normal "a named type may annotate an ordinary function" "let identity_type ≔ [α:*, x:α, α]\nlet identity:identity_type ≔ {α ^ {x ^ x}}" "identity" explicitIdentity,
    normal "an anonymous function is checked against its product" "let identity:[α:*, α, α] ≔ {x ^ x}" "identity" explicitIdentity,
    normal "fall is a lambda checked against its written product" "let identity ≔ fall α:*, x:α, α ^ x" "identity" explicitIdentity,
    normal "fall slots may be implicit" "let identity ≔ fall @α:*, x:α, α ^ x" "identity" (Lambda Implicit (Sort LZero) (Lambda Explicit (Local 0) (Local 0))),
    rejectContaining "fall requireþ an input before its result" "at least one input" (parseSource "let bad ≔ fall * ^ *"),
    normal "a local definition preserveþ the outer type binding" "let local:[α:*, x:α, α] ≔ (let y:α ≔ x yield y)" "local" explicitIdentity,
    normal "a local type alias preserveþ its surrounding implicit binder" "let identity:[@α:*, x:α, α] ≔ (let β ≔ α yield x)" "identity" (Lambda Implicit (Sort LZero) (Lambda Explicit (Local 0) (Local 0))),
    expectEq "lexical shadowing preserveþ local capture beneath a binder" (Right [nested 1, nested 0]) $ do
      program <- compile "let keep:[α:*, x:α, [α, α]] ≔ (let y:α ≔ x yield {x ^ y})\nlet shadow:[α:*, x:α, [α, α]] ≔ {x ^ x}"
      mapM (fmap eraseLevels . normaliseSourceExpression program) ["keep", "shadow"],
    normal "an anonymous slot still shifteþ surrounding binders" "let first:[α:*, x:α, _:α, α] ≔ x" "first" (Lambda Explicit (Sort LZero) (Lambda Explicit (Local 0) (Lambda Explicit (Local 1) (Local 1)))),
    normal "explicit implicit types may follow value arguments" "let identity:[@α:*, x:α, α] ≔ x" "* identity @*" (Sort LZero),
    normal "implicit arguments may be ordinary values" "let choose:[α:*, @x:α, α] ≔ x" "* choose @*" (Sort LZero),
    normal "implicit arguments select declaration order" (aliasSource ++ "let constant:[@α:*, @β:*, x:α, _:β, α] ≔ x") "* constant alias @* @([*, *])" (Sort LZero)
  ]
  where
    nested index = Lambda Explicit (Sort LZero) (Lambda Explicit (Local 0) (Lambda Explicit (Local 1) (Local index)))

implicitInferenceTests :: [Test]
implicitInferenceTests =
  [ normal "an explicit value determineþ its omitted type argument" implicitIdentitySource "* identity" (Sort LZero),
    normal "an expected type specialiseþ an omitted argument" (implicitIdentitySource ++ "let specialised:[*, *] ≔ identity") "specialised" (Lambda Explicit (Sort LZero) (Local 0)),
    expectEq "unspecialised functions retain their implicit product" (Right implicitIdentityType) $ do
      result <- inferIn implicitIdentitySource "identity"
      pure (eraseLevels (inferredType result)),
    normal "higher-rank arguments retain their polymorphism" (implicitIdentitySource ++ "let Id ≔ [@α:*, α, α]\nlet pass:[f:Id, Id] ≔ f") "identity pass" implicitIdentity,
    normal "a higher-rank lambda can be checked and passed" "let Id ≔ [@α:*, α, α]\nlet run:[f:Id, x:*, *] ≔ x f" "{@α ^ {x ^ x}} run *" (Sort LZero),
    normal "checking introduceþ an omitted implicit lambda binder" "let Id ≔ [@α:*, α, α]\nlet run:[f:Id, x:*, *] ≔ x f" "{x ^ x} run *" (Sort LZero),
    normal "a neutral family determineþ an omitted value" "let forward:[α:*, F:[α, *], @x:α, value:x F, x F] ≔ value\nlet recover:[α:*, F:[α, *], x:α, value:x F, x F] ≔ α forward F value" "recover" familyIdentity,
    normal "local aliases do not duplicate an inference spine" (implicitIdentitySource ++ "let through:[α:*, x:α, α] ≔ (let y ≔ x yield y identity)") "through" explicitIdentity,
    normal "family inference solveþ a pattern beneath a binder" "let family_id:[α:*, @F:[α, *], [x:α, x F, x F]] ≔ {x ^ {v ^ v}}\nlet recover:[α:*, G:[α, *], [x:α, x G, x G]] ≔ α family_id" "recover" familyIdentity,
    normal "a later pattern solution dischargeþ a delayed family equation" "let accept:[@F:[*, *], x:*, v:x F, w:[y:*, y F, y F], x F] ≔ v\nlet recover:[v:*, w:[y:*, *, *], *] ≔ * accept v w" "recover" (Lambda Explicit (Sort LZero) (Lambda Explicit (Pi Explicit (Sort LZero) (Pi Explicit (Sort LZero) (Sort LZero))) (Local 1))),
    reject "family agreement at one argument doth not determine the family" (compile "let use:[@F:[*, *], v:* F, * F] ≔ v\nlet bad:[G:[*, *], v:* G, * G] ≔ v use"),
    reject "a discarded implicit argument cannot be guessed" (inferIn "let erase:[@α:*, x:*, *] ≔ x" "* erase"),
    reject "one inferred type cannot equal distinct rigid types" (compile "let same:[@α:*, x:α, y:α, α] ≔ x\nlet bad:[α:*, β:*, x:α, y:β, α] ≔ x same y"),
    rejectContaining "self-application cannot infer a recursive argument type" "occurs check" (compile "let omega ≔ {x ^ x x}"),
    reject "inferred domains cannot capture later binders" (compile "let bad ≔ {y ^ ({x ^ y}:[x:*, x])}")
  ]

delayedComputationTests :: [Test]
delayedComputationTests =
  [ expectEq "conversion resumeþ after a dictionary is selected" (Right ()) $
      () <$ compile ("flock provided:[α:*, *] { let get:α } bizen:ℤ provided { let get ≔ +2 } let proof:(get @ℤ) = +2 ≔ reflect"),
    expectEq "a solution typed by an unselected dictionary waiteþ for instance search" (Right ()) $
      ()
        <$ compile
          """
          ilk box:[α:*, *] {boxed:[α, α box]}
          let same:[@α:*, a:α, α] ≔ a
          flock mapping:[φ:[*, *], *] { let over:[@α:*, @β:*, α φ, [α, β], β φ] }
          bizen:box mapping { let over:[a boxed:, f:] ≔ (a f) boxed }
          let proof:[@α:*, b:α box, (b over same) = b] ≔ match b {a boxed ^ reflect}
          """,
    expectEq "equal eliminator results do not equate their delayed inputs" (Right True) do
      program <- compile (choices ++ "let answer ≔ reflect accept right_evidence left_evidence")
      sameNormalIn program "answer" "right",
    expectEq "native computation resumeþ after its input is inferred" (Right True) do
      program <- compile (arithmetic "+3" ++ "let answer ≔ reflect accept two")
      sameNormalIn program "answer" "+2",
    rejectContaining "a postponed computed equation must still hold" "cannot unify" $
      compile (arithmetic "+4" ++ "let answer ≔ reflect accept two")
  ]
  where
    choices =
      """
      ilk choice:* {left:choice, right:choice}
      ilk evidence:[x:choice, *] {left_evidence:left evidence, right_evidence:right evidence}
      let erase:[x:choice, choice] ≔ match x {left ^ left, right ^ left}
      let accept:[@x:choice, @y:choice, _:(x erase) = (y erase), _:x evidence, _:y evidence, choice] ≔ x

      """
    arithmetic expected =
      """
      let add:[ℤ, ℤ, ℤ] ≔ 'add_integer' fremmed
      ilk amount:[n:ℤ, *] {two:+2 amount}

      """
        ++ "let accept:[@n:ℤ, _:(n add +1) = "
        ++ expected
        ++ ", _:n amount, ℤ] ≔ n\n"

rejectionTests :: [Test]
rejectionTests =
  [ reject "types and values cannot redeclare one name" (compile "let shared ≔ *\nlet shared:[α:*, *] ≔ α"),
    reject "unknown names are rejected" (compile "let unknown ≔ missing"),
    reject "source definitions cannot refer to themselves" (compile "let loop ≔ loop"),
    rejectContaining "a binder annotation cannot see its own binder" "needs a type annotation" (compile "let loop ≔ {loop:loop ^ loop}"),
    reject "self-application is rejected before normalisation" (compile "let omega ≔ {x:* ^ x x}"),
    reject "a product domain must itself be a type" (compile "let bad:[x:{y:* ^ y}, *] ≔ *"),
    reject "a type cannot inhabit itself" (compile "let bad:[u:*, u] ≔ u"),
    reject "anonymous slots create no accessible binding" (compile "let bad:[α:*, _:α, α] ≔ _"),
    reject "local names do not escape their scope" (compile "let local ≔ (let inside ≔ * yield inside)\nlet outside ≔ inside"),
    reject "a shadowing value cannot be resolved as the former type" (compile "let bad:[@α:*, x:α, α] ≔ (let α ≔ x let y:α ≔ x yield y)"),
    expectEq "an unknown lambda domain is generalised" (Right ()) (checkedIn "let unknown ≔ {x ^ x}" "* unknown"),
    -- `?f x` is pruned to `?f`, so þe type function generaliseþ.
    expectEq "a hole drops a local þat its solution cannot see" (Right "[@α: [*, *], @β: *, β α, β α]") $
      compile "let lift:[@a:*, @f:[*, *], x: a f, a f] ≔ x\nlet twice: [x:] ≔ (x lift) lift" >>= (`typeOfName` "twice"),
    expectEq "reflect proveþ an equation þat holdeþ by computation" (Right ()) $
      () <$ compile ("let one: ℕ ≔ 1\nlet checked: one = 1 ≔ reflect"),
    rejectContaining "reflect cannot prove unequal values" "cannot unify 1 wiþ 2" $
      compile ("let wrong: 1 = 2 ≔ reflect"),
    expectEq "goals keep definitions folded unless þey reach a constructor or variable" (Right ["(b app c) = (b app c)", "(first cons (rest app (b app c))) = (first cons ((rest app b) app c))"]) $
      map holeGoal . reverse . sourceHoles
        <$> compile
          """
          ilk lst:[α:*, *] { nil:α lst, cons:[α, α lst, α lst] }
          let app:[@α:*, l:α lst, r:α lst, α lst] ≔ match l { nil ^ r, x cons rest ^ x cons (rest app r) }
          let assoc:[@α:*, a:α lst, b:α lst, c:α lst, (a app (b app c)) = ((a app b) app c)] ≔
            match a { nil ^ sorry, first cons rest ^ sorry }
          """,
    expectEq "a sorry recordeþ its goal and named context" (Right [("α", [("α", "*"), ("b", "α box"), ("a", "α")])]) $
      map (\Hole {holeGoal, holeContext} -> (holeGoal, holeContext)) . sourceHoles
        <$> compile "ilk box:[α:*, *] {boxed:[α, α box]}\nlet unbox:[@α:*, b:α box, α] ≔ match b { a boxed ^ sorry }",
    expectEq "matching a proof rewriteþ its index" (Right "[@α: *, @x: α, @y: α, x = y, y = x]") $
      compile ("let symmetric: [@α: *, @x: α, @y: α, p: x = y, y = x] ≔ match p { reflect ^ reflect }") >>= (`typeOfName` "symmetric"),
    expectEq "a constructor slot after implicit slots matcheþ its input" (Right "[@α: *, @x: α, @y: α, x = y, y = x]") $
      compile ("let symmetric: [@α: *, @x: α, @y: α, reflect: x = y, y = x] ≔ reflect") >>= (`typeOfName` "symmetric")
  ]

identitySource, implicitIdentitySource, aliasSource :: String
identitySource = "let identity:[α:*, x:α, α] ≔ x\n"
implicitIdentitySource = "let identity:[@α:*, x:α, α] ≔ x\n"
aliasSource = "let alias:[α:*, *] ≔ α\n"

explicitIdentity, implicitIdentity, implicitIdentityType, familyIdentity :: Term
explicitIdentity = Lambda Explicit (Sort LZero) (Lambda Explicit (Local 0) (Local 0))
implicitIdentity = Lambda Implicit (Sort LZero) (Lambda Explicit (Local 0) (Local 0))
implicitIdentityType = Pi Implicit (Sort LZero) (Pi Explicit (Local 0) (Local 1))
familyIdentity = Lambda Explicit (Sort LZero) (Lambda Explicit (Pi Explicit (Local 0) (Sort LZero)) (Lambda Explicit (Local 1) (Lambda Explicit (Apply Explicit (Local 1) (Local 0)) (Local 0))))

sourceModule :: ModuleId
sourceModule = SourceModule "example.tung"

compile :: String -> Either String SourceProgram
compile = compileSource sourceModule

inferIn :: String -> String -> Either String Inferred
inferIn source expression = compile source >>= (`inferSourceExpression` expression)

checkedIn :: String -> String -> Either String ()
checkedIn source expression = do
  program <- compile source
  result <- inferSourceExpression program expression
  validate (sourceEnvironment program) result

normal :: String -> String -> String -> Term -> Test
normal label source expression expected = expectEq label (Right expected) $ do
  program <- compile source
  eraseLevels <$> normaliseSourceExpression program expression
