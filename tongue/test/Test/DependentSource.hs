-- source examples are checked again by the independent dependent kernel.
module Test.DependentSource (group) where

import Control.Monad (forM_)
import Test.Compile (compileSource)
import Test.DependentSupport
import Test.Harness (Group, Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent
import Tung.Dependent.Source (Hole (..), SourceProgram, inferSourceExpression, normaliseSourceExpression, orsendAssumptions, parseSource, sorryAssumptions, sourceDefinitions, sourceEnvironment, sourceHoles, typeOfName)

group :: IO Group
group = Harness.group "dependent-source" (elaborationTests ++ shadowingTests ++ implicitInferenceTests ++ delayedComputationTests ++ assumptionTests ++ rejectionTests)

shadowingTests :: [Test]
shadowingTests =
  [ expectEq label (Right True) do
      program <- compile source
      sameNormalIn program actual expected
  | (label, source, actual, expected) <-
      [ ("a header binder may share its declaration's name", "let selfness:[selfness:ℤ, ℤ] ≔ selfness", "+1 selfness", "+1"),
        ("a lambda binder may share its declaration's name", "let selfness: [@α: *, α, α] ≔ {selfness ^ selfness}", "+1 selfness", "+1"),
        ("a local binding hides its enclosing declaration's name", "let worth ≔ (let worth ≔ +1 yield worth)", "worth", "+1"),
        ("a case variable may share its declaration's name", "let predecessor:[ℕ, ℕ] ≔ {0 ^ 0, predecessor heir ^ predecessor}", "2 predecessor", "1"),
        ("a local function's binder is not a recursive reference", "let outer:[ℤ, ℤ] ≔ {x ^ (let inner ≔ {inner ^ inner} yield x inner)}", "+1 outer", "+1"),
        ("capture surviveth records and lets", "let keep: [ℤ, text, ℤ] ≔ {x ^ (let stored ≔ r{worth ≔ x} yield {y ^ stored.worth})}", "+1 keep 'ignored'", "+1"),
        ("a product parameter may share its alias's name", "let endo ≔ [endo:*, endo, endo]", "endo", "[α:*, α, α]")
      ]
  ]

elaborationTests :: [Test]
elaborationTests =
  [ expectEq "definitions retain their source identities" (Right [SymbolId sourceModule "alias", SymbolId sourceModule "selfness"]) $ do
      program <- compileSource sourceModule (aliasSource ++ identitySource)
      pure (map fst (sourceDefinitions program)),
    expectEq "source definitions carry kernel-checked judgements" (Right ()) $ do
      program <- compile (aliasSource ++ identitySource)
      forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd),
    expectEq "a source universe inhabiteth a larger universe" (Right True) $ do
      result <- inferIn "" "*"
      pure case (inferredTerm result, inferredType result) of
        (Sort lower, Sort upper) -> universeEntails (inferredConstraints result) (LevelEqual (LSucc lower) upper)
        _ -> False,
    normal "application substituteth the supplied type" identitySource "* selfness *" (Sort LZero),
    expectEq "each global use receiveth fresh universe arguments" (Right ()) (checkedIn identitySource "[α:*, x:α, α] selfness selfness"),
    normal "type aliases use the same application syntax" aliasSource "* alias" (Sort LZero),
    normal "a named type may annotate an ordinary function" "let selfness_type ≔ [α:*, x:α, α]\nlet selfness:selfness_type ≔ {α ^ {x ^ x}}" "selfness" explicitIdentity,
    normal "an anonymous function is checked against its product" "let selfness:[α:*, α, α] ≔ {x ^ x}" "selfness" explicitIdentity,
    normal "fall is a lambda checked against its written product" "let selfness ≔ fall α:*, x:α, α ^ x" "selfness" explicitIdentity,
    normal "fall slots may be implicit" "let selfness ≔ fall @α:*, x:α, α ^ x" "selfness" (Lambda Implicit (Sort LZero) (Lambda Explicit (Local 0) (Local 0))),
    rejectContaining "fall requireth an input before its result" "at least one input" (parseSource "let bad ≔ fall * ^ *"),
    normal "a local definition preserveth the outer type binding" "let local:[α:*, x:α, α] ≔ (let y:α ≔ x yield y)" "local" explicitIdentity,
    normal "a local type alias preserveth its surrounding implicit binder" "let selfness:[@α:*, x:α, α] ≔ (let β ≔ α yield x)" "selfness" (Lambda Implicit (Sort LZero) (Lambda Explicit (Local 0) (Local 0))),
    expectEq "lexical shadowing preserveth local capture beneath a binder" (Right [nested 1, nested 0]) $ do
      program <- compile "let keep:[α:*, x:α, [α, α]] ≔ (let y:α ≔ x yield {x ^ y})\nlet shadow:[α:*, x:α, [α, α]] ≔ {x ^ x}"
      mapM (fmap eraseLevels . normaliseSourceExpression program) ["keep", "shadow"],
    normal "an anonymous slot still shifteth surrounding binders" "let first:[α:*, x:α, _:α, α] ≔ x" "first" (Lambda Explicit (Sort LZero) (Lambda Explicit (Local 0) (Lambda Explicit (Local 1) (Local 1)))),
    normal "explicit implicit types may follow worth arguments" "let selfness:[@α:*, x:α, α] ≔ x" "* selfness @*" (Sort LZero),
    normal "implicit arguments may be ordinary values" "let choose:[α:*, @x:α, α] ≔ x" "* choose @*" (Sort LZero),
    normal "implicit arguments select declaration order" (aliasSource ++ "let constant:[@α:*, @β:*, x:α, _:β, α] ≔ x") "* constant alias @* @([*, *])" (Sort LZero)
  ]
  where
    nested index = Lambda Explicit (Sort LZero) (Lambda Explicit (Local 0) (Lambda Explicit (Local 1) (Local index)))

implicitInferenceTests :: [Test]
implicitInferenceTests =
  [ normal "an explicit worth determineth its omitted type argument" implicitIdentitySource "* selfness" (Sort LZero),
    normal "an expected type specialiseth an omitted argument" (implicitIdentitySource ++ "let specialised:[*, *] ≔ selfness") "specialised" (Lambda Explicit (Sort LZero) (Local 0)),
    expectEq "unspecialised functions retain their implicit product" (Right implicitIdentityType) $ do
      result <- inferIn implicitIdentitySource "selfness"
      pure (eraseLevels (inferredType result)),
    normal "higher-rank arguments retain their polymorphism" (implicitIdentitySource ++ "let Id ≔ [@α:*, α, α]\nlet pass:[f:Id, Id] ≔ f") "selfness pass" implicitIdentity,
    normal "a higher-rank lambda can be checked and passed" "let Id ≔ [@α:*, α, α]\nlet run:[f:Id, x:*, *] ≔ x f" "{@α ^ {x ^ x}} run *" (Sort LZero),
    normal "checking introduceth an omitted implicit lambda binder" "let Id ≔ [@α:*, α, α]\nlet run:[f:Id, x:*, *] ≔ x f" "{x ^ x} run *" (Sort LZero),
    normal "a neutral family determineth an omitted worth" "let forward:[α:*, F:[α, *], @x:α, worth:x F, x F] ≔ worth\nlet recover:[α:*, F:[α, *], x:α, worth:x F, x F] ≔ α forward F worth" "recover" familyIdentity,
    normal "local aliases do not duplicate an inference spine" (implicitIdentitySource ++ "let through:[α:*, x:α, α] ≔ (let y ≔ x yield y selfness)") "through" explicitIdentity,
    normal "family inference solveth a pattern beneath a binder" "let family_id:[α:*, @F:[α, *], [x:α, x F, x F]] ≔ {x ^ {v ^ v}}\nlet recover:[α:*, G:[α, *], [x:α, x G, x G]] ≔ α family_id" "recover" familyIdentity,
    normal "a later pattern solution dischargeth a delayed family equation" "let accept:[@F:[*, *], x:*, v:x F, w:[y:*, y F, y F], x F] ≔ v\nlet recover:[v:*, w:[y:*, *, *], *] ≔ * accept v w" "recover" (Lambda Explicit (Sort LZero) (Lambda Explicit (Pi Explicit (Sort LZero) (Pi Explicit (Sort LZero) (Sort LZero))) (Local 1))),
    reject "family agreement at one argument doth not determine the family" (compile "let use:[@F:[*, *], v:* F, * F] ≔ v\nlet bad:[G:[*, *], v:* G, * G] ≔ v use"),
    reject "a discarded implicit argument cannot be guessed" (inferIn "let erase:[@α:*, x:*, *] ≔ x" "* erase"),
    reject "one inferred type cannot same distinct rigid types" (compile "let hath_≍:[@α:*, x:α, y:α, α] ≔ x\nlet bad:[α:*, β:*, x:α, y:β, α] ≔ x hath_≍ y"),
    rejectContaining "self-application cannot infer a recursive argument type" "occurs check" (compile "let omega ≔ {x ^ x x}"),
    reject "inferred domains cannot capture later binders" (compile "let bad ≔ {y ^ ({x ^ y}:[x:*, x])}")
  ]

delayedComputationTests :: [Test]
delayedComputationTests =
  [ expectEq "conversion resumeth after a dictionary is selected" (Right ()) $
      () <$ compile ("flock provided:[α:*, *] { let get:α } bizen:ℤ provided { let get ≔ +2 } let proof:(get @ℤ) = +2 ≔ backbend"),
    expectEq "a solution typed by an unselected dictionary waiteth for instance search" (Right ()) $
      ()
        <$ compile
          """
          ilk box:[α:*, *] {boxed:[α, α box]}
          let hath_≍:[@α:*, a:α, α] ≔ a
          flock mapping:[φ:[*, *], *] { let over:[@α:*, @β:*, α φ, [α, β], β φ] }
          bizen:box mapping { let over:[a boxed:, f:] ≔ (a f) boxed }
          let proof:[@α:*, b:α box, (b over hath_≍) = b] ≔ match b {a boxed ^ backbend}
          """,
    expectEq "same eliminator results do not equate their delayed inputs" (Right True) do
      program <- compile (choices ++ "let answer ≔ backbend accept right_evidence left_evidence")
      sameNormalIn program "answer" "right",
    expectEq "native computation resumeth after its input is inferred" (Right True) do
      program <- compile (arithmetic "+3" ++ "let answer ≔ backbend accept two")
      sameNormalIn program "answer" "+2",
    rejectContaining "a postponed computed equation must still hold" "cannot unify" $
      compile (arithmetic "+4" ++ "let answer ≔ backbend accept two")
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
      let hath_+:[ℤ, ℤ, ℤ] ≔ 'eke_integer' fremmed
      ilk amount:[n:ℤ, *] {two:+2 amount}

      """
        ++ "let accept:[@n:ℤ, _:(n hath_+ +1) = "
        ++ expected
        ++ ", _:n amount, ℤ] ≔ n\n"

-- an `orsetting` is a listed constant without a body, distinct from `sorry`.
assumptionTests :: [Test]
assumptionTests =
  [ expectEq "an orsetting is listed and is not a sorry" (Right (["excluded: [two, two]"], [])) do
      program <- compile (twoSource ++ "orsetting excluded: [p: two, two]\nshow let uses: two ≔ yea excluded")
      pure (orsendAssumptions program, sorryAssumptions program),
    expectEq "an orsetting never unfoldeth" (Right True) do
      program <- compile (twoSource ++ "orsetting excluded: [p: two, two]\nlet uses: two ≔ yea excluded")
      sameNormalIn program "uses" "yea excluded",
    rejectContaining "an orsetting annotation must be a type" "annotation is not a type" (compile (twoSource ++ "orsetting wrong: yea")),
    rejectContaining "an orsetting cannot enter a let block" "orsetting assumptions must be top-level" (compile (twoSource ++ "let worth ≔ (let first ≔ yea orsetting inner: two yield first)")),
    rejectContaining "an orsetting name is declared once" "repeat" (compile (twoSource ++ "orsetting yea: two")),
    -- `for` giveth each branch the equation between the scrutinee and its pattern.
    expectEq "a match equation nameth the matched constructor" (Right True) do
      program <- compile (twoSource ++ flipSource ++ "let remembered: [b: two, two] ≔ match b flip for known { yea ^ (let k: (b flip) = yea ≔ known yield nay), nay ^ (let k: (b flip) = nay ≔ known yield yea) }")
      sameNormalIn program "yea remembered" "yea",
    rejectContaining "a match equation nameth only its own branch" "cannot unify yea with nay" (compile (twoSource ++ "let wrong: [b: two, two] ≔ match b for known { yea ^ (let k: b = nay ≔ known yield nay), nay ^ yea }")),
    expectEq "a match with an equation inferreth its result" (Right True) do
      program <- compile (twoSource ++ "let swap ≔ {b: two ^ match b for known { yea ^ nay, nay ^ yea }}")
      sameNormalIn program "yea swap" "nay"
  ]
  where
    twoSource = "ilk two: * { yea: two, nay: two }\n"
    flipSource = "let flip: [b: two, two] ≔ match b { yea ^ nay, nay ^ yea }\n"

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
    reject "a shadowing worth cannot be resolved as the former type" (compile "let bad:[@α:*, x:α, α] ≔ (let α ≔ x let y:α ≔ x yield y)"),
    -- a top-level let is never generalised over its holes.
    rejectContaining "a let whose type is undetermined is rejected" "write the polymorphic parameters" (compile "let unknown ≔ {x ^ x}"),
    rejectContaining "an inferred slot type without a use is rejected" "write the polymorphic parameters" (compile "let selfness: [x:] ≔ x"),
    -- `?f x` is pruned to `?f`, so the type function is solved.
    expectEq "a hole drops a local that its solution cannot see" (Right "[@α: *, @β: [*, *], α β, α β]") $
      compile "let lift:[@a:*, @f:[*, *], x: a f, a f] ≔ x\nlet twice:[@a:*, @f:[*, *], x: a f, a f] ≔ (x lift) lift" >>= (`typeOfName` "twice"),
    expectEq "backbend proveth an equation that holdeth by computation" (Right ()) $
      () <$ compile ("let one: ℕ ≔ 1\nlet checked: one = 1 ≔ backbend"),
    rejectContaining "backbend cannot prove unequal values" "cannot unify 1 with 2" $
      compile ("let wrong: 1 = 2 ≔ backbend"),
    expectEq "goals keep definitions folded unless they reach a constructor or variable" (Right ["(b app c) = (b app c)", "(first cons (rest app (b app c))) = (first cons ((rest app b) app c))"]) $
      map holeGoal . reverse . sourceHoles
        <$> compile
          """
          ilk lst:[α:*, *] { nil:α lst, cons:[α, α lst, α lst] }
          let app:[@α:*, l:α lst, r:α lst, α lst] ≔ match l { nil ^ r, x cons rest ^ x cons (rest app r) }
          let assoc:[@α:*, a:α lst, b:α lst, c:α lst, (a app (b app c)) = ((a app b) app c)] ≔
            match a { nil ^ sorry, first cons rest ^ sorry }
          """,
    expectEq "a sorry recordeth its goal and named context" (Right [("α", [("α", "*"), ("b", "α box"), ("a", "α")])]) $
      map (\Hole {holeGoal, holeContext} -> (holeGoal, holeContext)) . sourceHoles
        <$> compile "ilk box:[α:*, *] {boxed:[α, α box]}\nlet unbox:[@α:*, b:α box, α] ≔ match b { a boxed ^ sorry }",
    expectEq "matching a proof rewriteth its index" (Right "[@α: *, @x: α, @y: α, x = y, y = x]") $
      compile ("let evenmete: [@α: *, @x: α, @y: α, p: x = y, y = x] ≔ match p { backbend ^ backbend }") >>= (`typeOfName` "evenmete"),
    expectEq "a constructor slot after implicit slots matcheth its input" (Right "[@α: *, @x: α, @y: α, x = y, y = x]") $
      compile ("let evenmete: [@α: *, @x: α, @y: α, backbend: x = y, y = x] ≔ backbend") >>= (`typeOfName` "evenmete")
  ]

identitySource, implicitIdentitySource, aliasSource :: String
identitySource = "let selfness:[α:*, x:α, α] ≔ x\n"
implicitIdentitySource = "let selfness:[@α:*, x:α, α] ≔ x\n"
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
