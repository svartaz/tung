-- source examples are checked again by the independent dependent kernel.
module Test.DependentSource (group) where

import Control.Monad (forM_)
import Data.Either (isLeft)
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Test.Compile (compileProject, compileSource)
import Test.DependentSupport
import Test.Harness (Group, Test, expectEq)
import Test.Harness qualified as Harness
import Tung (SourceSpan (..))
import Tung.Dependent
import Tung.Dependent.Source (DependencyKind (..), Hole (..), ProofDependency (..), SourceProgram, auditDependencies, auditName, auditProof, auditType, inferSourceExpression, normaliseSourceExpression, orsendAssumptions, parseSource, recoverSnapshotHoles, sorryAssumptions, sourceDefinitions, sourceEnvironment, sourceHoles, sourceSnapshot, typeOfName, verifyProof)

group :: IO Group
group = do
  library <- loadLibrary ["is.tung"]
  Harness.group "dependent-source" (elaborationTests ++ shadowingTests ++ implicitInferenceTests ++ delayedComputationTests ++ assumptionTests ++ inspectTests library ++ proofAuditTests ++ recoveryTests ++ rejectionTests)

shadowingTests :: [Test]
shadowingTests =
  [ expectEq label (Right True) do
      program <- compile source
      sameNormalIn program actual expected
  | (label, source, actual, expected) <-
      [ ("a header binder may share its declaration's name", "let sameness:[sameness:ℤ, ℤ] ≔ sameness", "+1 sameness", "+1"),
        ("a lambda binder may share its declaration's name", "let sameness: [@α: *, α, α] ≔ {sameness ^ sameness}", "+1 sameness", "+1"),
        ("a local binding hides its enclosing declaration's name", "let worth ≔ (let worth ≔ +1 yield worth)", "worth", "+1"),
        ("a case variable may share its declaration's name", "let predecessor:[ℕ, ℕ] ≔ {0 ^ 0, predecessor heir ^ predecessor}", "2 predecessor", "1"),
        ("a local function's binder is not a recursive reference", "let outer:[ℤ, ℤ] ≔ {x ^ (let inner ≔ {inner ^ inner} yield x inner)}", "+1 outer", "+1"),
        ("capture surviveth fields and lets", "ilk box: * { box_of: [worth: ℤ, box] } let keep: [ℤ, string, ℤ] ≔ {x ^ (let stored ≔ x box_of yield {y ^ stored.worth})}", "+1 keep 'ignored'", "+1"),
        ("a product parameter may share its alias's name", "let endo ≔ [endo:*, endo, endo]", "endo", "[α:*, α, α]")
      ]
  ]

elaborationTests :: [Test]
elaborationTests =
  [ rejectContaining "identity requireth an explicit import" "unknown name '='" (compileSource sourceModule "let soothing:0 = 0 ≔ eftbend"),
    expectEq "definitions retain their source identities" (Right [SymbolId sourceModule "alias", SymbolId sourceModule "sameness"]) $ do
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
    normal "application substituteth the supplied type" identitySource "* sameness *" (Sort LZero),
    expectEq "each global use receiveth fresh universe arguments" (Right ()) (checkedIn identitySource "[α:*, x:α, α] sameness sameness"),
    normal "type aliases use the same application syntax" aliasSource "* alias" (Sort LZero),
    normal "a named type may annotate an ordinary function" "let sameness_type ≔ [α:*, x:α, α]\nlet sameness:sameness_type ≔ {α ^ {x ^ x}}" "sameness" explicitIdentity,
    normal "an anonymous function is checked against its product" "let sameness:[α:*, α, α] ≔ {x ^ x}" "sameness" explicitIdentity,
    normal "fall is a lambda checked against its written product" "let sameness ≔ fall α:*, x:α, α ^ x" "sameness" explicitIdentity,
    normal "fall slots may be implicit" "let sameness ≔ fall @α:*, x:α, α ^ x" "sameness" (Lambda Implicit (Sort LZero) (Lambda Explicit (Local 0) (Local 0))),
    rejectContaining "fall requireth an input before its result" "at least one input" (parseSource "let bad ≔ fall * ^ *"),
    normal "a local definition preserveth the outer type binding" "let local:[α:*, x:α, α] ≔ (let y:α ≔ x yield y)" "local" explicitIdentity,
    normal "a local type alias preserveth its surrounding implicit binder" "let sameness:[@α:*, x:α, α] ≔ (let β ≔ α yield x)" "sameness" (Lambda Implicit (Sort LZero) (Lambda Explicit (Local 0) (Local 0))),
    expectEq "lexical shadowing preserveth local capture beneath a binder" (Right [nested 1, nested 0]) $ do
      program <- compile "let keep:[α:*, x:α, [α, α]] ≔ (let y:α ≔ x yield {x ^ y})\nlet shadow:[α:*, x:α, [α, α]] ≔ {x ^ x}"
      mapM (fmap eraseLevels . normaliseSourceExpression program) ["keep", "shadow"],
    normal "an anonymous slot still shifteth surrounding binders" "let first:[α:*, x:α, _:α, α] ≔ x" "first" (Lambda Explicit (Sort LZero) (Lambda Explicit (Local 0) (Lambda Explicit (Local 1) (Local 1)))),
    normal "explicit implicit types may follow worth arguments" "let sameness:[@α:*, x:α, α] ≔ x" "* sameness @*" (Sort LZero),
    normal "implicit arguments may be ordinary values" "let choose:[α:*, @x:α, α] ≔ x" "* choose @*" (Sort LZero),
    normal "implicit arguments select declaration order" (aliasSource ++ "let constant:[@α:*, @β:*, x:α, _:β, α] ≔ x") "* constant alias @* @([*, *])" (Sort LZero)
  ]
  where
    nested index = Lambda Explicit (Sort LZero) (Lambda Explicit (Local 0) (Lambda Explicit (Local 1) (Local index)))

implicitInferenceTests :: [Test]
implicitInferenceTests =
  [ normal "an explicit worth determineth its omitted type argument" implicitIdentitySource "* sameness" (Sort LZero),
    normal "an expected type specialiseth an omitted argument" (implicitIdentitySource ++ "let specialised:[*, *] ≔ sameness") "specialised" (Lambda Explicit (Sort LZero) (Local 0)),
    expectEq "unspecialised functions retain their implicit product" (Right implicitIdentityType) $ do
      result <- inferIn implicitIdentitySource "sameness"
      pure (eraseLevels (inferredType result)),
    normal "higher-rank arguments retain their polymorphism" (implicitIdentitySource ++ "let Id ≔ [@α:*, α, α]\nlet pass:[f:Id, Id] ≔ f") "sameness pass" implicitIdentity,
    normal "a higher-rank lambda can be checked and passed" "let Id ≔ [@α:*, α, α]\nlet run:[f:Id, x:*, *] ≔ x f" "{@α ^ {x ^ x}} run *" (Sort LZero),
    normal "checking introduceth an omitted implicit lambda binder" "let Id ≔ [@α:*, α, α]\nlet run:[f:Id, x:*, *] ≔ x f" "{x ^ x} run *" (Sort LZero),
    normal "a neutral family determineth an omitted worth" "let forward:[α:*, F:[α, *], @x:α, worth:x F, x F] ≔ worth\nlet handler:[α:*, F:[α, *], x:α, worth:x F, x F] ≔ α forward F worth" "handler" familyIdentity,
    normal "local aliases do not duplicate an inference spine" (implicitIdentitySource ++ "let through:[α:*, x:α, α] ≔ (let y ≔ x yield y sameness)") "through" explicitIdentity,
    normal "family inference solveth a pattern beneath a binder" "let family_id:[α:*, @F:[α, *], [x:α, x F, x F]] ≔ {x ^ {v ^ v}}\nlet handler:[α:*, G:[α, *], [x:α, x G, x G]] ≔ α family_id" "handler" familyIdentity,
    normal "a later pattern solution dischargeth a delayed family equation" "let accept:[@F:[*, *], x:*, v:x F, w:[y:*, y F, y F], x F] ≔ v\nlet handler:[v:*, w:[y:*, *, *], *] ≔ * accept v w" "handler" (Lambda Explicit (Sort LZero) (Lambda Explicit (Pi Explicit (Sort LZero) (Pi Explicit (Sort LZero) (Sort LZero))) (Local 1))),
    -- with no other progress, `* ?F = * G` splitteth by first-order
    -- approximation into `?F = G`, as dependent.md specifieth.
    expectEq "first-order approximation determineth a family from agreement at one argument" (Right ()) (() <$ compile "let pass:[@F:[*, *], v:* F, * F] ≔ v\nlet good:[G:[*, *], v:* G, * G] ≔ v pass"),
    reject "a discarded implicit argument cannot be guessed" (inferIn "let erase:[@α:*, x:*, *] ≔ x" "* erase"),
    reject "one inferred type cannot same distinct rigid types" (compile "let hath_≍:[@α:*, x:α, y:α, α] ≔ x\nlet bad:[α:*, β:*, x:α, y:β, α] ≔ x hath_≍ y"),
    rejectContaining "self-application cannot infer a recursive argument type" "occurs check" (compile "let omega ≔ {x ^ x x}"),
    reject "inferred domains cannot capture later binders" (compile "let bad ≔ {y ^ ({x ^ y}:[x:*, x])}")
  ]

delayedComputationTests :: [Test]
delayedComputationTests =
  [ expectEq "conversion resumeth after a dictionary is selected" (Right ()) $
      () <$ compile ("flock provided:[α:*, *] { let get:α } bizen:ℤ provided { let get ≔ +2 } let soothing:(get @ℤ) = +2 ≔ eftbend"),
    expectEq "a solution typed by an unselected dictionary waiteth for instance search" (Right ()) $
      ()
        <$ compile
          """
          ilk box:[α:*, *] {boxed:[α, α box]}
          let hath_≍:[@α:*, a:α, α] ≔ a
          flock mapping:[φ:[*, *], *] { let over:[@α:*, @β:*, α φ, [α, β], β φ] }
          bizen:box mapping { let over:[a boxed:, f:] ≔ (a f) boxed }
          let soothing:[@α:*, b:α box, (b over hath_≍) = b] ≔ match b {a boxed ^ eftbend}
          """,
    expectEq "same eliminator results do not equate their delayed inputs" (Right True) do
      program <- compile (choices ++ "let answer ≔ eftbend accept right_evidence left_evidence")
      sameNormalIn program "answer" "right",
    expectEq "native computation resumeth after its input is inferred" (Right True) do
      program <- compile (arithmetic "+3" ++ "let answer ≔ eftbend accept two")
      sameNormalIn program "answer" "+2",
    rejectContaining "a postponed computed equation must still hold" "cannot unify" $
      compile (arithmetic "+4" ++ "let answer ≔ eftbend accept two")
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
      let hath_+:[ℤ, ℤ, ℤ] ≔ 'eke_wholetale' fremmed
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
    rejectContaining "an orsetting annotation must be a type" "annotation is not an ilk" (compile (twoSource ++ "orsetting wrong: yea")),
    rejectContaining "an orsetting cannot enter a let block" "orsetting assumptions must be top-level" (compile (twoSource ++ "let worth ≔ (let first ≔ yea orsetting inner: two yield first)")),
    rejectContaining "an orsetting name is declared once" "repeat" (compile (twoSource ++ "orsetting yea: two"))
  ]
  where
    twoSource = "ilk two: * { yea: two, nay: two }\n"

-- branch equations come from an ordinary dependent library function.
inspectTests :: Library -> [Test]
inspectTests library =
  [ expectEq "inlook retaineth computed branch equations and reduceth" (Right True) do
      program <- compile "let remembered:[b:two,two] ≔ (b flip) inlook @two @{_ ^ two} {yea, known ^ (let k:(b flip) = yea ≔ known yield nay), nay, known ^ (let k:(b flip) = nay ≔ known yield yea)}"
      forM_ (sourceDefinitions program) (validate (sourceEnvironment program) . snd)
      sameNormalIn program "yea remembered" "yea",
    rejectContaining "inlook's equation nameth only its own branch" "cannot unify yea with nay" (compile "let wrong:[b:two,two] ≔ b inlook @two @{_ ^ two} {yea,known ^ (let k:b = nay ≔ known yield nay), nay,_ ^ yea}"),
    expectEq "inlook inferreth a result with a written motive" (Right True) do
      program <- compile "let swap ≔ {b:two ^ b inlook @two @{_ ^ two} {yea,known ^ nay, nay,known ^ yea}}"
      sameNormalIn program "yea swap" "nay",
    expectEq "inlook supporteth dependent and outer-dependent results" (Right [True, True, True]) do
      program <-
        compile
          """
          let choice:[b:two,*] ≔ match b {yea ^ ℕ, nay ^ string}
          let dependent:[b:two,b choice] ≔ b inlook {yea,known ^ 0, nay,known ^ 'x'}
          let retained:[b:two,b = b] ≔ (b flip) inlook @two @{_ ^ b = b} {yea,known ^ eftbend, nay,known ^ eftbend}
          """
      traverse (uncurry (sameNormalIn program)) [("yea dependent", "0"), ("nay dependent", "'x'"), ("yea retained", "(eftbend:yea = yea)")]
  ]
  where
    compile source = compileWith library "inlook.tung" ("bring is.tung\nilk two:* {yea:two, nay:two}\nlet flip:[b:two,two] ≔ match b {yea ^ nay, nay ^ yea}\n" ++ source)

proofAuditTests :: [Test]
proofAuditTests =
  [ expectEq "a proved private declaration ignoreth unrelated assumptions" (Right ("soothed", "0 is~= 0", [], Right ())) do
      program <- compile "orsetting unused:ℕ\nlet unfinished:ℕ ≔ sorry\nlet soothed:0 = 0 ≔ eftbend"
      audited <- auditProof program "soothed"
      pure (auditName audited, auditType audited, auditDependencies audited, verifyProof program True (Just []) audited),
    expectEq "dictionary proofs retain their axiom and obey an exact policy" (Right ([(SymbolId sourceModule "assumed", AxiomDependency)], [Right (), Right (), Left "orsetting is not allowed: assumed"])) do
      program <- compile dictionaryProof
      audited <- auditProof program "soothed"
      pure (dependencies audited, [verifyProof program True policy audited | policy <- [Nothing, Just ["assumed"], Just []]]),
    rejectContaining "an axiom policy rejecteth an unknown name" "unknown name 'missing'" do
      program <- compile "let soothed:0 = 0 ≔ eftbend"
      auditProof program "soothed" >>= verifyProof program True (Just ["missing"]),
    rejectContaining "an axiom policy rejecteth a name that is no axiom" "is not an orsetting" do
      program <- compile "let soothed:0 = 0 ≔ eftbend"
      auditProof program "soothed" >>= verifyProof program True (Just ["soothed"]),
    expectEq "a sorry only in an assumption's type preventeth strict certification" (Right (expectedTypeDependencies, [Left "unfinished proof: sorry", Right ()])) do
      program <- compile "orsetting unfinished:(sorry:*)"
      audited <- auditProof program "unfinished"
      pure (dependencies audited, [verifyProof program strict Nothing audited | strict <- [True, False]]),
    expectEq "a host model's sorry preventeth certification and retaineth host trust" (Right (expectedHostDependencies, Left "unfinished proof: sorry")) do
      program <- compileProject kindfulModule ("bring is.tung\n" ++ hostModel) (Map.singleton "is.tung" equalitySource)
      audited <- auditProof program "selected"
      pure (dependencies audited, verifyProof program True Nothing audited),
    expectEq "an inductive field retaineth its private type assumption" (Right [(SymbolId sourceModule "hidden", AxiomDependency)]) do
      program <- compile "orsetting hidden:*\nilk box:* { pack:[hidden,box] }\nlet soothed:[x:box,x = x] ≔ eftbend"
      dependencies <$> auditProof program "soothed",
    expectEq "native computation in a proof type retaineth its trusted operation" (Right [(SymbolId sourceModule "add", HostDependency "eke_kindful")]) do
      program <- compile "let add:[ℕ,ℕ,ℕ] ≔ 'eke_kindful' fremmed\nlet soothed:(0 add 0) = 0 ≔ eftbend"
      dependencies <$> auditProof program "soothed",
    expectEq "a reduced named type alias retaineth its source assumption" (Right [(SymbolId sourceModule "hidden", AxiomDependency)]) do
      program <-
        compile
          """
          orsetting hidden:ℕ
          let ignore:[ℕ,*] ≔ {_ ^ ℕ}
          let annotation:* ≔ hidden ignore
          let soothed:annotation ≔ 0
          """
      dependencies <$> auditProof program "soothed"
  ]
  where
    dependencies = sortOn fst . map (\ProofDependency {dependencySymbol, dependencyKind} -> (dependencySymbol, dependencyKind)) . auditDependencies
    expectedTypeDependencies = sortOn fst [(SymbolId sourceModule "unfinished", AxiomDependency), (SymbolId PrimitiveModule "sorry", SorryDependency)]
    -- a model is trusted only in its catalogued bookhoard file.
    kindfulModule = SourceModule "ilk/kindful.tung"
    expectedHostDependencies = sortOn fst [(SymbolId kindfulModule "add", HostDependency "eke_kindful"), (SymbolId PrimitiveModule "sorry", SorryDependency)]
    dictionaryProof =
      """
      flock law:[α:*,*] { let rule:[x:α,x = x] }
      orsetting assumed:[n:ℕ,n = n]
      bizen:ℕ law { let rule ≔ assumed }
      let soothed:0 = 0 ≔ 0 rule
      """
    hostModel =
      """
      let add:[ℕ,ℕ,ℕ] ≔ 'eke_kindful' fremmed {_,_ ^ sorry}
      let selected:[ℕ,ℕ,ℕ] ≔ add
      """

recoveryTests :: [Test]
recoveryTests =
  [ expectEq
      "goals survive an unrelated type error while proof checking stayeth strict"
      (True, [("α", [("α", "*"), ("x", "α")]), ("string", [("t", "string")])])
      (isLeft (compile typeFailure >>= (`auditProof` "soothed")), goals typeFailure),
    expectEq
      "complete declarations retain goals on both sides of a parse error"
      (True, [("ℕ", [("n", "ℕ")]), ("string", [("t", "string")])])
      (isLeft (parseSource parseFailure), goals parseFailure),
    expectEq "a failed definition retaineth an earlier local goal without defining its name" [("ℕ", [("x", "ℕ")]), ("string", [])] $
      goals
        """
        let broken:[x:ℕ,ℕ] ≔ (let unfinished:ℕ ≔ sorry let invalid:ℕ ≔ 'wrong' yield unfinished)
        let blocked:0 broken = 0 ≔ sorry
        let independent:string ≔ sorry
        """,
    expectEq
      "failed shadowing cannot expose a primitive to direct or transitive dependants"
      (replicate 3 [("ℤ", [("n", "ℤ")])])
      [ goals (failed ++ "\nlet blocked:[n:ℕ,ℕ] ≔ sorry\nlet alias:* ≔ ℕ\nlet transitive:[n:alias,alias] ≔ sorry\nlet independent:[n:ℤ,ℤ] ≔ sorry")
      | failed <- ["let ℕ:* ≔ 'wrong'", "orsetting ℕ:+1", "let ℕ:* ≔ A\nlet A:* ≔ ℕ"]
      ],
    expectEq "a failed bizen retaineth an earlier member's goal without supplying a dictionary" [("ℕ", [("x", "ℕ")]), ("string", [])] $
      goals
        """
        flock pair:[α:*,*] { let first:[α,α] let second:α }
        bizen:ℕ pair { let first ≔ {x ^ sorry} let second ≔ 'wrong' }
        let blocked:(0 first) = 0 ≔ sorry
        let independent:string ≔ sorry
        """,
    expectEq "a final yield retaineth its goal beside a declaration error" [("ℕ", [])] $
      goals "let broken:ℕ ≔ 'wrong'\nyield (sorry:ℕ)",
    expectEq "a checked final yield retaineth its goal" (Right [("ℕ", [])]) $
      map (\Hole {holeGoal, holeContext} -> (holeGoal, holeContext)) . sourceHoles <$> compile "yield (sorry:ℕ)",
    expectEq "a rejected bizen candidate cannot poison a later recovered goal" [("ℕ", [("x", "ℕ"), ("selected", "ℕ")])] $
      goals
        """
        flock related:[α:*,β:*,*] { let choose:[α,α] }
        bizen:[@α:*,α related string] { let choose ≔ {x ^ x} }
        bizen:ℕ related ℕ { let choose ≔ {x ^ x} }
        let wanted:[ℕ,ℕ] ≔ choose @ℕ @string
        let soothing:[x:ℕ,ℕ] ≔ (let selected:ℕ ≔ x wanted yield sorry)
        let broken:ℕ ≔ 'wrong'
        """
  ]
  where
    goals = map (\Hole {holeGoal, holeContext} -> (holeGoal, holeContext)) . sortOn (fmap spanStart . holeSpan) . (\source -> recoverSnapshotHoles Map.empty RootModule (sourceSnapshot (equalitySource ++ source)) Map.empty)
    typeFailure =
      """
      let before:[@α:*,x:α,α] ≔ sorry
      let broken:ℕ ≔ 'wrong'
      let after:[t:string,string] ≔ sorry
      let soothed:0 = 0 ≔ eftbend
      """
    parseFailure =
      """
      let before:[n:ℕ,ℕ] ≔ sorry
      let broken:[ℕ,,ℕ] ≔ 0
      let after:[t:string,string] ≔ sorry
      """

rejectionTests :: [Test]
rejectionTests =
  [ reject "types and values cannot redeclare one name" (compile "let shared ≔ *\nlet shared:[α:*, *] ≔ α"),
    reject "unknown names are rejected" (compile "let unknown ≔ missing"),
    reject "source definitions cannot refer to themselves" (compile "let loop ≔ loop"),
    rejectContaining "a binder annotation cannot see its own binder" "needs an ilk annotation" (compile "let loop ≔ {loop:loop ^ loop}"),
    reject "self-application is rejected before normalisation" (compile "let omega ≔ {x:* ^ x x}"),
    reject "a product domain must itself be a type" (compile "let bad:[x:{y:* ^ y}, *] ≔ *"),
    reject "a type cannot inhabit itself" (compile "let bad:[u:*, u] ≔ u"),
    reject "anonymous slots create no accessible binding" (compile "let bad:[α:*, _:α, α] ≔ _"),
    reject "local names do not escape their scope" (compile "let local ≔ (let inside ≔ * yield inside)\nlet outside ≔ inside"),
    reject "a shadowing worth cannot be resolved as the former type" (compile "let bad:[@α:*, x:α, α] ≔ (let α ≔ x let y:α ≔ x yield y)"),
    -- a top-level let is never generalised over its holes.
    rejectContaining "a let whose type is undetermined is rejected" "write the polymorphic parameters" (compile "let unknown ≔ {x ^ x}"),
    rejectContaining "an inferred slot type without a use is rejected" "write the polymorphic parameters" (compile "let sameness: [x:] ≔ x"),
    -- `?f x` is pruned to `?f`, so the type function is solved.
    expectEq "a hole drops a local that its solution cannot see" (Right "[@α: *, @β: [*, *], α β, α β]") $
      compile "let lift:[@a:*, @f:[*, *], x: a f, a f] ≔ x\nlet twice:[@a:*, @f:[*, *], x: a f, a f] ≔ (x lift) lift" >>= (`typeOfName` "twice"),
    expectEq "eftbend proveth an equation that holdeth by computation" (Right ()) $
      () <$ compile ("let one: ℕ ≔ 1\nlet checked: one = 1 ≔ eftbend"),
    rejectContaining "eftbend cannot prove unequal values" "cannot unify 1 with 2" $
      compile ("let wrong: 1 = 2 ≔ eftbend"),
    expectEq "goals keep definitions folded unless they reach a constructor or variable" (Right ["(b app c) = (b app c)", "(first cons (leftover app (b app c))) = (first cons ((leftover app b) app c))"]) $
      map holeGoal . reverse . sourceHoles
        <$> compile
          """
          ilk lst:[α:*, *] { nil:α lst, cons:[α, α lst, α lst] }
          let app:[@α:*, l:α lst, r:α lst, α lst] ≔ match l { nil ^ r, x cons leftover ^ x cons (leftover app r) }
          let assoc:[@α:*, a:α lst, b:α lst, c:α lst, (a app (b app c)) = ((a app b) app c)] ≔
            match a { nil ^ sorry, first cons leftover ^ sorry }
          """,
    expectEq "goals show fields, chained fields, and calls through fields" (Right ["p.age = p.age", "h.child.age = h.child.age", "(x f).age = (x f).age", "(x h.run y) = (x h.run y)"]) $
      map holeGoal . reverse . sourceHoles
        <$> compile
          """
          ilk person:* { person_of:[age:ℤ, person] }
          ilk holder:* { holder_of:[child:person, run:[ℤ, ℤ, ℤ], holder] }
          let plain:[p:person, p.age = p.age] ≔ sorry
          let chained:[h:holder, h.child.age = h.child.age] ≔ sorry
          let applied:[f:[ℤ, person], x:ℤ, (x f).age = (x f).age] ≔ sorry
          let called:[h:holder, x:ℤ, y:ℤ, (x h.run y) = (x h.run y)] ≔ sorry
          """,
    expectEq "dependent field types and goal contexts retain their names" (Right ("[x: packed, x.value is~= x.value]", "[x: packed, x.value is~= x.value]", [("p.value = p.value", [("p", "packed"), ("q", "p.value = p.value")])])) do
      program <-
        compile
          """
          ilk packed:* { pack:[value:ℤ, sure:value = value, packed] }
          let inferred ≔ {p:packed ^ p.sure}
          let unfinished:[p:packed, q:p.value = p.value, p.value = p.value] ≔ sorry
          """
      ty <- typeOfName program "inferred"
      audited <- auditProof program "inferred"
      pure (ty, auditType audited, [(holeGoal, holeContext) | Hole {holeGoal, holeContext} <- sourceHoles program]),
    expectEq "field goals use receiver syntax for imported types" (Right ["p.age = p.age"]) $
      map holeGoal . sourceHoles
        <$> compileProject
          sourceModule
          (equalitySource ++ "bring people.tung other\nlet soothing:[p:other~person, p.age = p.age] ≔ sorry")
          (Map.singleton "people.tung" "show ilk person:* { person_of:[age:ℤ, person] }"),
    expectEq "a sorry recordeth its goal and named context" (Right [("α", [("α", "*"), ("b", "α box"), ("a", "α")])]) $
      map (\Hole {holeGoal, holeContext} -> (holeGoal, holeContext)) . sourceHoles
        <$> compile "ilk box:[α:*, *] {boxed:[α, α box]}\nlet unbox:[@α:*, b:α box, α] ≔ match b { a boxed ^ sorry }",
    expectEq "matching a proof rewriteth its index" (Right "[@α: *, @x: α, @y: α, x is~= y, y is~= x]") $
      compile ("let evenmete: [@α: *, @x: α, @y: α, p: x = y, y = x] ≔ match p { eftbend ^ eftbend }") >>= (`typeOfName` "evenmete"),
    expectEq "a constructor slot after implicit slots matcheth its input" (Right "[@α: *, @x: α, @y: α, x is~= y, y is~= x]") $
      compile ("let evenmete: [@α: *, @x: α, @y: α, eftbend: x = y, y = x] ≔ eftbend") >>= (`typeOfName` "evenmete")
  ]

identitySource, implicitIdentitySource, aliasSource :: String
identitySource = "let sameness:[α:*, x:α, α] ≔ x\n"
implicitIdentitySource = "let sameness:[@α:*, x:α, α] ≔ x\n"
aliasSource = "let alias:[α:*, *] ≔ α\n"

explicitIdentity, implicitIdentity, implicitIdentityType, familyIdentity :: Term
explicitIdentity = Lambda Explicit (Sort LZero) (Lambda Explicit (Local 0) (Local 0))
implicitIdentity = Lambda Implicit (Sort LZero) (Lambda Explicit (Local 0) (Local 0))
implicitIdentityType = Pi Implicit (Sort LZero) (Pi Explicit (Local 0) (Local 1))
familyIdentity = Lambda Explicit (Sort LZero) (Lambda Explicit (Pi Explicit (Local 0) (Sort LZero)) (Lambda Explicit (Local 1) (Lambda Explicit (Apply Explicit (Local 1) (Local 0)) (Local 0))))

sourceModule :: ModuleId
sourceModule = SourceModule "example.tung"

compile :: String -> Either String SourceProgram
compile source = compileProject sourceModule ("bring is.tung\n" ++ source) (Map.singleton "is.tung" equalitySource)

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
