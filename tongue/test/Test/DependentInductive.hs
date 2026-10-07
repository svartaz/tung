-- induction exerciseth computation, indexed motives, and the kernel boundary.
module Test.DependentInductive (group) where

import Data.Either (isLeft)
import Test.DependentSupport
import Test.Harness (Test, expectEq)
import Test.Harness qualified as Harness
import Tung.Dependent

group :: IO Harness.Group
group = Harness.group "dependent-inductive" tests

tests :: [Test]
tests =
  [ expectEq "natural induction computeth recursive hypotheses" (Right two) $ do
      environment <- naturalEnvironment
      normalise environment (naturalInduction naturalMotive zero successorMethod two),
    expectEq "neutral induction surviveth quotation and rechecking" (Right ()) $ do
      environment <- naturalEnvironment
      let term = Lambda Explicit natural (naturalInduction naturalMotive zero successorMethod (Local 0))
      normal <- normalise environment term
      infer environment normal >>= validate environment,
    expectEq "small inductives allow large elimination" (Right (sort 0)) $ do
      environment <- naturalEnvironment
      let motive = Lambda Explicit natural (sort 1)
          method = Lambda Explicit natural (Lambda Explicit (sort 1) (sort 0))
      normalise environment (apply Explicit (global "natural_induction" [level 2]) [motive, sort 0, method, zero]),
    expectEq "indexed induction retaineth the constructor result index" (Right vectorOne) $ do
      environment <- vectorEnvironment
      normalise environment vectorReconstruction,
    reject "an indexed constructor cannot inhabit another index" $ do
      environment <- vectorEnvironment
      check environment vectorEmpty (vector natural (successor zero)),
    expectEq "selfness transport along reflexivity computeth" (Right transportedIdentity) $ do
      environment <- identityEnvironment
      normalise environment transport,
    reject "reflexivity cannot identify distinct constructors" $ do
      environment <- identityEnvironment
      check environment reflexivity (identity natural zero (successor zero)),
    reject "elimination requireth every constructor method" $ do
      environment <- naturalEnvironment
      check environment (apply Explicit (global "natural_induction" [level 0]) [naturalMotive, zero]) natural,
    expectEq "partly supplied eliminators remain ordinary functions" (Right ()) $ do
      environment <- naturalEnvironment
      infer environment (apply Explicit (global "natural_induction" [level 0]) [naturalMotive, zero]) >>= validate environment,
    reject "elimination rejecteth an extra constructor method" $ do
      environment <- naturalEnvironment
      infer environment (Apply Explicit (naturalInduction naturalMotive zero successorMethod two) zero),
    reject "elimination checketh the motive universe" $ do
      environment <- naturalEnvironment
      infer environment (naturalInduction zero zero successorMethod two),
    reject "elimination checketh recursive hypothesis types" $ do
      environment <- naturalEnvironment
      let method = Lambda Explicit natural (Lambda Explicit (sort 0) zero)
      infer environment (naturalInduction naturalMotive zero method two),
    reject "unselected methods cannot hide term inference holes" $ do
      environment <- naturalEnvironment
      normalise environment (naturalInduction naturalMotive zero (Meta 0 []) zero),
    reject "inductive metadata rejecteth inference holes before evaluation" $ do
      environment <- naturalEnvironment
      defineInductive environment (badDeclaration (Meta 0 [])),
    reject "undernaught recursive fields are rejected" $ do
      environment <- naturalEnvironment
      defineInductive environment (badDeclaration (Pi Explicit bad natural)),
    reject "double-negative recursive fields are rejected" $ do
      environment <- naturalEnvironment
      defineInductive environment (badDeclaration (Pi Explicit (Pi Explicit bad natural) natural)),
    reject "transparent aliases cannot hide undernaught recursive fields" $ do
      environment <- naturalEnvironment
      aliased <- define environment (symbol "undernaught") Nothing (Lambda Explicit (sort 0) (Pi Explicit (Local 0) natural))
      defineInductive aliased (badDeclaration (Apply Explicit (global "undernaught" []) bad)),
    reject "a family cannot occur in a field's input" $ do
      environment <- naturalEnvironment
      defineInductive environment (badDeclaration (Pi Explicit bad natural)),
    reject "stored fields cannot exceed the inductive universe" $ do
      environment <- naturalEnvironment
      defineInductive environment (badDeclaration (sort 0)),
    reject "constructor results must name their declared family" $ do
      environment <- naturalEnvironment
      defineInductive environment vectorDeclaration {inductiveConstructors = [(symbol "vector_empty", Pi Implicit (Sort (LParam 0)) natural)]},
    reject "constructor results require all family indices" $ do
      environment <- naturalEnvironment
      defineInductive environment vectorDeclaration {inductiveConstructors = [(symbol "vector_empty", Pi Implicit (Sort (LParam 0)) (Apply Implicit (global "vector" [LParam 0]) (Local 0)))]},
    reject "uniform parameters cannot change in constructor results" $ do
      environment <- naturalEnvironment
      defineInductive environment vectorDeclaration {inductiveUniverses = 0, inductiveType = Pi Implicit (sort 0) (Pi Explicit natural (sort 0)), inductiveConstructors = [(symbol "vector_empty", Pi Implicit (sort 0) (apply Explicit (Apply Implicit (global "vector" []) natural) [zero]))]},
    reject "recursive family arguments cannot contain that family" $ do
      environment <- naturalEnvironment
      let family argument = Apply Explicit (global "nested" []) argument
          declaration = InductiveDeclaration (symbol "nested") (symbol "nested_induction") 0 0 [] (Pi Explicit (sort 0) (sort 0)) [(symbol "nested_make", Pi Explicit (family (family natural)) (family natural))]
      defineInductive environment declaration,
    reject "inductive names cannot replace checked globals" $ do
      environment <- naturalEnvironment
      defineInductive environment naturalDeclaration,
    expectEq "inductive inference generaliseth universe holes" (Right ()) $ do
      environment <- naturalEnvironment
      inferred <- inferInductive environment (symbol "inferred_box") (symbol "inferred_box_induction") 1 (Pi Implicit (Sort (LMeta 0)) (Sort (LMeta 0))) [(symbol "inferred_box_make", Pi Implicit (Sort (LMeta 0)) (Pi Explicit (Local 0) (Apply Implicit (global "inferred_box" [LMeta 0]) (Local 1))))] []
      result <- infer inferred (global "inferred_box" [level 0])
      validate inferred result,
    expectEq
      "inferred field constraints reach the family, constructor, and eliminator"
      (Right [(name, True, True) | name <- ["universe_field", "universe_field_make", "universe_field_induction"]])
      $ do
        environment <-
          inferInductive
            emptyEnvironment
            (symbol "universe_field")
            (symbol "universe_field_induction")
            0
            (Sort (LMeta 0))
            [(symbol "universe_field_make", Pi Explicit (Sort (LMeta 1)) (global "universe_field" [LMeta 0, LMeta 1]))]
            []
        traverse
          ( \(name, extra) -> do
              inferred <- infer environment (global name ([LMeta 0, LMeta 1] ++ extra))
              infer environment (global name ([level 2, level 1] ++ extra)) >>= validate environment
              pure
                ( name,
                  universeEntails (inferredConstraints inferred) (LevelBelow (LSucc (LParam 1)) (LParam 0)),
                  isLeft (infer environment (global name ([level 1, level 1] ++ extra)))
                )
          )
          [("universe_field", []), ("universe_field_make", []), ("universe_field_induction", [LZero])],
    rejectContaining "inductive inference cannot rewrite concrete self universes" "inference placeholders" $
      inferInductive emptyEnvironment (symbol "concrete") (symbol "concrete_induction") 0 (sort 0) [(symbol "concrete_make", global "concrete" [level 1])] []
  ]

naturalEnvironment :: Either String Environment
naturalEnvironment = defineInductive emptyEnvironment naturalDeclaration

naturalDeclaration :: InductiveDeclaration
naturalDeclaration = InductiveDeclaration (symbol "natural") (symbol "natural_induction") 0 0 [] (sort 0) [(symbol "zero", natural), (symbol "heir", Pi Explicit natural natural)]

natural, zero, two, naturalMotive, successorMethod :: Term
natural = global "natural" []
zero = global "zero" []
two = successor (successor zero)
naturalMotive = Lambda Explicit natural natural
successorMethod = Lambda Explicit natural (Lambda Explicit natural (successor (Local 0)))

successor :: Term -> Term
successor = Apply Explicit (global "heir" [])

naturalInduction :: Term -> Term -> Term -> Term -> Term
naturalInduction motive initial method value = apply Explicit (global "natural_induction" [level 0]) [motive, initial, method, value]

vectorEnvironment :: Either String Environment
vectorEnvironment = naturalEnvironment >>= (`defineInductive` vectorDeclaration)

vectorDeclaration :: InductiveDeclaration
vectorDeclaration =
  InductiveDeclaration
    (symbol "vector")
    (symbol "vector_induction")
    1
    1
    []
    (Pi Implicit (Sort (LParam 0)) (Pi Explicit natural (Sort (LParam 0))))
    [ (symbol "vector_empty", Pi Implicit (Sort (LParam 0)) (vectorAt (LParam 0) (Local 0) zero)),
      ( symbol "vector_cons",
        Pi Implicit (Sort (LParam 0)) $
          Pi Explicit natural $
            Pi Explicit (Local 1) $
              Pi Explicit (vectorAt (LParam 0) (Local 2) (Local 1)) $
                vectorAt (LParam 0) (Local 3) (successor (Local 2))
      )
    ]

vectorAt :: Level -> Term -> Term -> Term
vectorAt universe element index = Apply Explicit (Apply Implicit (global "vector" [universe]) element) index

vector :: Term -> Term -> Term
vector = vectorAt (level 0)

vectorEmpty, vectorOne, vectorReconstruction :: Term
vectorEmpty = Apply Implicit (global "vector_empty" [level 0]) natural
vectorOne = vectorCons zero zero vectorEmpty
vectorReconstruction =
  let motive = Lambda Explicit natural (Lambda Explicit (vector natural (Local 0)) (vector natural (Local 1)))
      method =
        Lambda Explicit natural $
          Lambda Explicit natural $
            Lambda Explicit (vector natural (Local 1)) $
              Lambda Explicit (vector natural (Local 2)) $
                vectorCons (Local 3) (Local 2) (Local 0)
   in apply Explicit (Apply Implicit (global "vector_induction" [level 0, level 0]) natural) [motive, vectorEmpty, method, successor zero, vectorOne]

vectorCons :: Term -> Term -> Term -> Term
vectorCons index first rest = apply Explicit (Apply Implicit (global "vector_cons" [level 0]) natural) [index, first, rest]

identityEnvironment :: Either String Environment
identityEnvironment = naturalEnvironment >>= (`defineInductive` identityDeclaration)

identityDeclaration :: InductiveDeclaration
identityDeclaration =
  InductiveDeclaration
    (symbol "selfness")
    (symbol "selfness_induction")
    2
    1
    []
    (Pi Implicit (Sort (LParam 0)) (Pi Explicit (Local 0) (Pi Explicit (Local 1) (Sort (LParam 0)))))
    [(symbol "reflexivity", Pi Implicit (Sort (LParam 0)) (Pi Implicit (Local 0) (identityAt (LParam 0) (Local 1) (Local 0) (Local 0))))]

identityAt :: Level -> Term -> Term -> Term -> Term
identityAt universe ty left right = apply Explicit (Apply Implicit (global "selfness" [universe]) ty) [left, right]

identity :: Term -> Term -> Term -> Term
identity = identityAt (level 0)

reflexivity, transport, transportedIdentity :: Term
reflexivity = apply Implicit (global "reflexivity" [level 0]) [natural, zero]
transport =
  Lambda Explicit (Pi Explicit natural (sort 0)) $
    Lambda Explicit (Apply Explicit (Local 0) zero) $
      let motive = Lambda Explicit natural (Lambda Explicit (identity natural zero (Local 0)) (Apply Explicit (Local 3) (Local 1)))
       in apply Explicit (apply Implicit (global "selfness_induction" [level 0, level 0]) [natural, zero]) [motive, Local 0, zero, reflexivity]
transportedIdentity = Lambda Explicit (Pi Explicit natural (sort 0)) (Lambda Explicit (Apply Explicit (Local 0) zero) (Local 0))

bad :: Term
bad = global "bad" []

badDeclaration :: Term -> InductiveDeclaration
badDeclaration field = InductiveDeclaration (symbol "bad") (symbol "bad_induction") 0 0 [] (sort 0) [(symbol "bad_make", Pi Explicit field bad)]

apply :: Plicity -> Term -> [Term] -> Term
apply plicity = foldl (Apply plicity)

global :: String -> [Level] -> Term
global name = Global (symbol name)

symbol :: String -> SymbolId
symbol = SymbolId RootModule
