-- closed examples exercise dependent typing independently of source elaboration.
module Test.Dependent (group) where

import Test.DependentSupport
import Test.Harness (Group, Test, expect, expectEq, propertyTest)
import Test.Harness qualified as Harness
import Test.QuickCheck qualified as QuickCheck
import Tung.Dependent

group :: IO Group
group = Harness.group "dependent" (typingTests ++ reductionTests ++ globalTests ++ kernelTests ++ universeTests)

typingTests :: [Test]
typingTests =
  [ expectEq "a type is a term" (Right (sort 1)) (inferredType <$> infer emptyEnvironment (sort 0)),
    expectEq "a universe annotation hole is inferred" (Right (0, sort 1, [])) $ do
      result <- check emptyEnvironment (sort 0) (Sort (LMeta 0))
      pure (inferredUniverses result, inferredType result, inferredConstraints result),
    expectEq "selfness retaineth its bound type" (Right identityType) (inferredType <$> infer emptyEnvironment identity),
    expectEq "application substituteth its result type" (Right (Pi Explicit (sort 0) (sort 0))) (inferredType <$> infer emptyEnvironment (Apply Explicit identity (sort 0))),
    reject "a universe cannot contain itself" (check emptyEnvironment (sort 0) (sort 0)),
    reject "inferred universes cannot contain themselves" (check emptyEnvironment (Sort (LMeta 0)) (Sort (LMeta 0))),
    reject "closed terms have no local variable" (infer emptyEnvironment (Local 0)),
    reject "undernaught local indices are invalid" (infer emptyEnvironment (Local (-1))),
    reject "a function domain must be a type" (infer emptyEnvironment (Lambda Explicit identity (Local 0))),
    reject "a product result must be a type" (infer emptyEnvironment (Pi Explicit (sort 0) (Lambda Explicit (Local 0) (Local 0)))),
    reject "application respecteth argument visibility" (infer emptyEnvironment (Apply Implicit identity (sort 0))),
    reject "checking respecteth binder visibility" (check emptyEnvironment identity (Pi Implicit (sort 1) (Pi Explicit (Local 0) (Local 1))))
  ]

reductionTests :: [Test]
reductionTests =
  [ expectEq "beta reduction avoideth capture beneath a binder" (Right nestedIdentity) (normalise emptyEnvironment betaUnderBinder),
    expectEq "let reduction avoideth capture beneath a binder" (Right nestedIdentity) (normalise emptyEnvironment letUnderBinder),
    expectEq "a let preserveth its outer type binding" (Right (Pi Implicit (sort 1) (Pi Explicit (Local 0) (Local 1)), Lambda Implicit (sort 1) (Lambda Explicit (Local 0) (Local 0)))) $ do
      result <- infer emptyEnvironment dependentLet
      normal <- normalise emptyEnvironment dependentLet
      pure (inferredType result, normal),
    expectEq "a type reduceth its argument" (Right (Lambda Explicit (sort 0) (Local 0))) (normalise emptyEnvironment (Apply Explicit identity (sort 0))),
    reject "normalisation rejecteth an ill-typed term" (normalise emptyEnvironment (Apply Explicit (sort 0) (sort 0))),
    reject "omega is rejected before evaluation" (normalise emptyEnvironment (Apply Explicit omega omega))
  ]
  where
    nestedIdentity = Lambda Explicit (sort 1) (Lambda Explicit (sort 1) (Local 1))
    betaUnderBinder = Lambda Explicit (sort 1) (Apply Explicit nestedIdentity (Local 0))
    letUnderBinder = Lambda Explicit (sort 1) (Let (sort 1) (Local 0) (Lambda Explicit (sort 1) (Local 1)))
    dependentLet = Lambda Implicit (sort 1) (Let (sort 1) (Local 0) (Lambda Explicit (Local 0) (Local 0)))
    omega = Lambda Explicit (sort 0) (Apply Explicit (Local 0) (Local 0))

globalTests :: [Test]
globalTests =
  [ expectEq "global aliases reduce transitively" (Right (sort 0)) $ do
      first <- define emptyEnvironment (name "first") Nothing (sort 0)
      second <- define first (name "second") (Just (sort 1)) (Global (name "first") [])
      normalise second (Global (name "second") []),
    expectEq "one polymorphic definition supporteth different universes" (Right (Lambda Explicit (sort 0) (Local 0), sort 0)) $ do
      environment <- polymorphicEnvironment
      lower <- normalise environment (Apply Implicit (Global (name "selfness") [level 1]) (sort 0))
      higher <- normalise environment (Apply Explicit (Apply Implicit (Global (name "selfness") [level 2]) (sort 1)) (sort 0))
      pure (lower, higher),
    expectEq "products retain the maximum of inuniverses" (Right (sort 3)) $ do
      environment <- define emptyEnvironment (name "arrow") Nothing (Pi Explicit (Sort (LMeta 0)) (Sort (LMeta 1)))
      inferredType <$> infer environment (Global (name "arrow") [level 0, level 2]),
    expectEq "constrained globals accept universe inference holes" (Right 3) $ do
      environment <- define emptyEnvironment (name "maximum") (Just maximumAnnotation) (Sort (LMeta 0))
      inferredUniverses <$> infer environment (Global (name "maximum") [LMeta 0, LMeta 1, LMeta 2]),
    reject "unknown definitions are rejected" (infer emptyEnvironment (Global (name "unknown") [])),
    reject "self-reference cannot define a recursive global" (define emptyEnvironment (name "loop") Nothing (Global (name "loop") [])),
    reject "definitions cannot replace an existing selfness" $ do
      environment <- define emptyEnvironment (name "fixed") Nothing (sort 0)
      define environment (name "fixed") Nothing (Global (name "fixed") []),
    reject "global universe arity is checked" $ do
      environment <- polymorphicEnvironment
      infer environment (Global (name "selfness") [])
  ]

kernelTests :: [Test]
kernelTests =
  [ expectEq "inference generaliseth universe holes" (Right 1) (inferredUniverses <$> infer emptyEnvironment (Sort (LMeta 0))),
    expectEq "maximum inference doth not guess an is branch" (Right (3, False, False)) $ do
      result <- check emptyEnvironment (Sort (LMeta 0)) maximumAnnotation
      let assumptions = inferredConstraints result
      pure (inferredUniverses result, universeEntails assumptions (LevelEqual (LParam 0) (LParam 1)), universeEntails assumptions (LevelEqual (LParam 0) (LParam 2))),
    expectEq "the kernel independently accepteth a constrained universe judgement" (Right ()) (validate emptyEnvironment constrained),
    reject "the kernel requireth evidence for universe is" (validate emptyEnvironment constrained {inferredConstraints = []}),
    reject "the kernel rejecteth unresolved holes" (validate emptyEnvironment constrained {inferredTerm = Sort (LMeta 0)}),
    reject "the kernel rejecteth unresolved term inference holes" (validate emptyEnvironment (Inferred 0 [] (Meta 0 []) (sort 0))),
    reject "the kernel rejecteth out-of-scope universe parameters" (validate emptyEnvironment constrained {inferredUniverses = 1}),
    reject "inconsistent assumptions cannot justify a judgement" (validate emptyEnvironment constrained {inferredConstraints = [LevelEqual (LParam 0) (LSucc (LParam 0))]}),
    reject "the kernel checketh the claimed type" (validate emptyEnvironment (Inferred 0 [] (sort 0) (sort 0)))
  ]
  where
    constrained = Inferred 2 [LevelEqual (LSucc (LParam 0)) (LParam 1)] (Sort (LParam 0)) (Sort (LParam 1))

universeTests :: [Test]
universeTests =
  [ expect "strict heir constraints have no solution" (not (universeSatisfiable [LevelBelow (LSucc (LParam 0)) (LParam 0)])),
    expect "universe maxima preserve each lower bound" (universeEntails [] (LevelBelow (LParam 0) (LMax (LParam 0) (LParam 1)))),
    expect "unrelated universe parameters are not same" (not (universeEntails [] (LevelEqual (LParam 0) (LParam 1)))),
    propertyTest "universe generalisation discardeth exactly tautological constraints" $ QuickCheck.forAll singleConstraintGenerator $ \constraint ->
      let generalised = do
            environment <- inferInductive emptyEnvironment (name "constraint") (name "constraint_induction") 0 (Sort (LMax (LParam 0) (LParam 1))) [] [constraint]
            inferredConstraints <$> infer environment (Global (name "constraint") [LParam 0, LParam 1])
          expected = if universeSatisfiable [constraint] then Right (universeEntails [] constraint) else Left "inconsistent universe constraints"
       in fmap null generalised QuickCheck.=== expected,
    propertyTest "universe normalisation preserveth arithmetic meaning" $ QuickCheck.forAll levelGenerator $ \expression ->
      all (\assignment -> evalLevel assignment expression == evalLevel assignment (universeNormalise expression)) assignments,
    propertyTest "bounded witnesses prevent false universe rejection" $ QuickCheck.forAll constraintGenerator $ \constraints ->
      not (any (\assignment -> all (satisfies assignment) constraints) assignments) || universeSatisfiable constraints,
    propertyTest "entailed universe constraints hold in every bounded model" $
      QuickCheck.forAll constraintGenerator $ \constraints ->
        QuickCheck.forAll singleConstraintGenerator $ \conclusion ->
          not (universeEntails constraints conclusion)
            || all (\assignment -> not (all (satisfies assignment) constraints) || satisfies assignment conclusion) assignments
  ]

identity, identityType :: Term
identity = Lambda Explicit (sort 1) (Lambda Explicit (Local 0) (Local 0))
identityType = Pi Explicit (sort 1) (Pi Explicit (Local 0) (Local 1))

maximumAnnotation :: Term
maximumAnnotation = Sort (LMax (LSucc (LMeta 1)) (LSucc (LMeta 2)))

polymorphicEnvironment :: Either String Environment
polymorphicEnvironment = define emptyEnvironment (name "selfness") Nothing (Lambda Implicit (Sort (LMeta 0)) (Lambda Explicit (Local 0) (Local 0)))

name :: String -> SymbolId
name = SymbolId RootModule

-- bounded assignments can prove satisfiability; their absence doth not prove failure.
assignments :: [[Int]]
assignments = [[a, b] | a <- [0 .. 6], b <- [0 .. 6]]

evalLevel :: [Int] -> Level -> Int
evalLevel assignment = \case
  LZero -> 0
  LParam index -> assignment !! index
  LSucc expression -> evalLevel assignment expression + 1
  LMax left right -> max (evalLevel assignment left) (evalLevel assignment right)
  LMeta _ -> error "the universe model generator doth not produce inference holes"

satisfies :: [Int] -> Constraint -> Bool
satisfies assignment = \case
  LevelEqual left right -> evalLevel assignment left == evalLevel assignment right
  LevelBelow left right -> evalLevel assignment left <= evalLevel assignment right

levelGenerator :: QuickCheck.Gen Level
levelGenerator = QuickCheck.sized (generate . min 3)
  where
    generate 0 = QuickCheck.elements [LZero, LParam 0, LParam 1]
    generate depth =
      QuickCheck.frequency
        [ (3, generate 0),
          (1, LSucc <$> generate (depth - 1)),
          (2, LMax <$> generate (depth - 1) <*> generate (depth - 1))
        ]

singleConstraintGenerator :: QuickCheck.Gen Constraint
singleConstraintGenerator = QuickCheck.oneof [LevelEqual <$> levelGenerator <*> levelGenerator, LevelBelow <$> levelGenerator <*> levelGenerator]

constraintGenerator :: QuickCheck.Gen [Constraint]
constraintGenerator = QuickCheck.chooseInt (0, 3) >>= (`QuickCheck.vectorOf` singleConstraintGenerator)
