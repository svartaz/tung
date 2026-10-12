{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}

-- | kernel checking and universe generalisation. source elaboration reuseth
-- these scoped operations; every completed term is independently rechecked.
module Tung.Dependent.Check
  ( Level (..),
    Constraint (..),
    Plicity (..),
    Term (..),
    SymbolId (..),
    ModuleId (..),
    Environment (..),
    emptyEnvironment,
    Inferred (..),
    infer,
    check,
    define,
    validate,
    normalise,
    universeNormalise,
    universeSatisfiable,
    universeEntails,
    Typing,
    Context (..),
    emptyContext,
    failure,
    evaluate,
    bind,
    inferTerm,
    checkType,
    checkTerm,
    convert,
    generalise,
    generaliseTerms,
    assume,
    defineInferred,
    openObligations,
    Checking (..),
    inferTermWith,
    checkTermWith,
    oblige,
    rejectMetas,
    validLevel,
  )
where

import Control.Monad (unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, get, put, runStateT)
import Data.Containers.ListUtils (nubOrd)
import Data.Foldable (foldlM, traverse_)
import Data.List (sort)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Tung.Dependent.Literal (literalType)
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Render (renderMismatch)
import Tung.Dependent.Syntax
import Tung.Dependent.Universe qualified as U
import Tung.Identity (ModuleId (..), SymbolId (..))

-- only independently checked definitions enter this environment. sequential
-- insertion and unique identities prevent recursive unfolding and postulates.
newtype Environment = Environment Globals
  deriving stock (Eq, Show)

emptyEnvironment :: Environment
emptyEnvironment = Environment Map.empty

data Inferred = Inferred
  { inferredUniverses :: Int,
    inferredConstraints :: [Constraint],
    inferredTerm :: Term,
    inferredType :: Term
  }
  deriving stock (Eq, Show)

type Typing = StateT U.Universes (Either String)

data Context = Context
  { contextValues :: [N.Value],
    contextTypes :: [N.Value]
  }

emptyContext :: Context
emptyContext = Context [] []

infer :: Environment -> Term -> Either String Inferred
infer environment@(Environment globals) term = do
  rejectMetas term
  traverse_ (validLevel Nothing True) (termLevels term)
  (ty, U.universeConstraints -> constraints) <- runStateT (inferTerm globals emptyContext term) (U.universes [])
  annotation <- N.quote globals 0 ty
  result <- generalise term annotation constraints
  validate environment result
  pure result

check :: Environment -> Term -> Term -> Either String Inferred
check environment@(Environment globals) term annotation = do
  rejectMetas term
  rejectMetas annotation
  traverse_ (validLevel Nothing True) (termLevels term ++ termLevels annotation)
  (_, U.universeConstraints -> constraints) <- runStateT (checkType globals emptyContext annotation >> checkTerm globals emptyContext term annotation) (U.universes [])
  result <- generalise term annotation constraints
  validate environment result
  pure result

define :: Environment -> SymbolId -> Maybe Term -> Term -> Either String Environment
define environment@(Environment globals) name annotation body = do
  when (Map.member name globals) (Left "duplicate definition")
  result <- maybe (infer environment body) (check environment body) annotation
  pure (insertChecked globals name result)

-- elaboration may infer under source scopes, but insertion always rechecketh a
-- closed generalised result. no source declaration can bypass the kernel.
-- an assumption is a constant whose checked type is all the kernel knoweth.
assume :: Environment -> SymbolId -> Inferred -> Either String Environment
assume environment@(Environment globals) name signature@Inferred {..} = do
  when (Map.member name globals) (Left "duplicate definition")
  validate environment signature
  N.normalise globals 0 inferredType >>= \case
    Sort _ -> pure ()
    _ -> Left "an orsetting annotation is not a type"
  pure (Environment (Map.insert name (Definition inferredUniverses inferredConstraints inferredTerm Assumption) globals))

defineInferred :: Environment -> SymbolId -> Inferred -> Either String Environment
defineInferred environment@(Environment globals) name result = do
  when (Map.member name globals) (Left "duplicate definition")
  validate environment result
  pure (insertChecked globals name result)

insertChecked :: Globals -> SymbolId -> Inferred -> Environment
insertChecked globals name Inferred {..} =
  Environment (Map.insert name (Definition inferredUniverses inferredConstraints inferredType (Transparent inferredTerm)) globals)

-- the kernel rechecketh final terms with rigid universe parameters. inference
-- constraints are accepted only when the exported assumptions entail them.
validate :: Environment -> Inferred -> Either String ()
validate (Environment globals) Inferred {..} = do
  rejectMetas inferredTerm
  rejectMetas inferredType
  when (inferredUniverses < 0) (Left "negative universe parameter count")
  let levels = termLevels inferredTerm ++ termLevels inferredType ++ concatMap constraintLevels inferredConstraints
  traverse_ (validLevel (Just inferredUniverses) False) levels
  universes <- maybe (Left "inconsistent universe constraints") Right (U.satisfy inferredConstraints)
  (_, U.universeConstraints -> obligations) <- runStateT (checkType globals emptyContext inferredType >> checkTerm globals emptyContext inferredTerm inferredType) universes
  unless (U.entailsAll inferredConstraints (openObligations inferredConstraints obligations)) (Left "unproved universe constraint in core")

-- the obligations a search must still prove. a repeated, trivially true, or
-- assumed constraint needeth no search.
openObligations :: [Constraint] -> [Constraint] -> [Constraint]
openObligations assumptions obligations = [obligation | obligation <- nubOrd obligations, not (U.trivial obligation), obligation `Set.notMember` assumed]
  where
    assumed = Set.fromList assumptions

-- unchecked evaluation is private: a caller cannot normalise omega or an
-- arbitrary cyclic environment by bypassing the kernel.
normalise :: Environment -> Term -> Either String Term
normalise environment@(Environment globals) term = do
  result <- infer environment term
  N.normalise globals 0 (inferredTerm result)

universeNormalise :: Level -> Level
universeNormalise = U.normaliseLevel

universeSatisfiable :: [Constraint] -> Bool
universeSatisfiable = U.satisfiable

universeEntails :: [Constraint] -> Constraint -> Bool
universeEntails = U.entails

failure :: String -> Typing a
failure = lift . Left

oblige :: Constraint -> Typing ()
oblige constraint = do
  current <- get
  -- conversion may evaluate types. reject inconsistent universes before NBE,
  -- rather than provisionally typing a non-normalising type-in-type calculus.
  -- a repeated or trivially true constraint cannot change satisfiability.
  unless (U.hasConstraint constraint current || U.trivial constraint) do
    maybe (failure "inconsistent universe constraints") put (U.constrain constraint current)

evaluate :: Globals -> Context -> Term -> Typing N.Value
evaluate globals Context {contextValues} = lift . N.evaluate globals contextValues

bind :: Context -> N.Value -> Context
bind Context {..} ty =
  Context (N.VNeutral (N.NLocal (length contextTypes)) : contextValues) (ty : contextTypes)

inferTerm :: Globals -> Context -> Term -> Typing N.Value
inferTerm globals = inferTermWith (kernelChecking globals)

-- inference rules are shared with typed metavariable checking. the kernel useth
-- fixed conversion and rejecteth holes; elaboration may only solve typed holes.
data Checking m = Checking
  { failCheck :: forall a. String -> m a,
    liftCheck :: forall a. Either String a -> m a,
    evaluateCheck :: Context -> Term -> m N.Value,
    -- an argument's worth only instantiateth a codomain, so its definitions
    -- stay folded until something forceth them.
    argumentCheck :: Context -> Term -> m N.Value,
    quoteCheck :: Int -> N.Value -> m Term,
    instantiateCheck :: N.Closure -> N.Value -> m N.Value,
    forceCheck :: N.Value -> m N.Value,
    convertCheck :: Context -> N.Value -> N.Value -> m (),
    constrainCheck :: Constraint -> m (),
    inferMetaCheck :: Context -> Int -> [Term] -> m N.Value,
    definitionCheck :: SymbolId -> m (Maybe Definition)
  }

kernelChecking :: Globals -> Checking Typing
kernelChecking globals =
  Checking
    { failCheck = failure,
      liftCheck = lift,
      evaluateCheck = evaluate globals,
      argumentCheck = \Context {contextValues} -> lift . N.evaluateGlued (N.closed globals) contextValues,
      quoteCheck = \depth -> lift . N.quote globals depth,
      instantiateCheck = \closure -> lift . N.instantiate globals closure,
      forceCheck = pure,
      convertCheck = convert globals,
      constrainCheck = oblige,
      inferMetaCheck = \_ _ _ -> failure "unresolved term inference hole in core",
      definitionCheck = pure . (`Map.lookup` globals)
    }

inferTermWith :: (Monad m) => Checking m -> Context -> Term -> m N.Value
inferTermWith operations@Checking {..} context@Context {..} = \case
  Local index
    | index >= 0, ty : _ <- drop index contextTypes -> pure ty
    | otherwise -> failCheck "unbound variable"
  Global name arguments ->
    definitionCheck name >>= \case
      Nothing -> failCheck "unknown definition"
      Just Definition {..} -> do
        unless (length arguments == definitionUniverses) (failCheck "wrong number of universe arguments")
        constraints <- liftCheck (traverse (U.instantiateConstraint arguments) definitionConstraints)
        traverse_ constrainCheck constraints
        annotation <- liftCheck (instantiateLevels arguments definitionType)
        evaluateCheck context annotation
  Sort level -> pure (N.VSort (LSucc level))
  Pi _ domain codomain -> do
    domainLevel <- checkTypeWith operations context domain
    domainValue <- evaluateCheck context domain
    codomainLevel <- checkTypeWith operations (bind context domainValue) codomain
    pure (N.VSort (U.normaliseLevel (LMax domainLevel codomainLevel)))
  Lambda plicity domain body -> do
    checkTypeWith operations context domain
    domainValue <- evaluateCheck context domain
    bodyType <- inferTermWith operations (bind context domainValue) body
    codomain <- quoteCheck (length contextTypes + 1) bodyType
    pure (N.VPi plicity domainValue (N.Closure contextValues codomain))
  Apply plicity function argument -> do
    functionType <- inferTermWith operations context function >>= forceCheck
    case functionType of
      N.VPi expected domain codomain -> do
        unless (plicity == expected) (failCheck "implicit and explicit arguments do not match")
        argumentType <- inferTermWith operations context argument
        convertCheck context argumentType domain
        argumentValue <- argumentCheck context argument
        instantiateCheck codomain argumentValue
      _ -> failCheck "application requireth a function"
  Let annotation value body -> do
    checkTypeWith operations context annotation
    checkTermWith operations context value annotation
    valueType <- evaluateCheck context annotation
    valueValue <- evaluateCheck context value
    inferTermWith operations (Context (valueValue : contextValues) (valueType : contextTypes)) body
  Meta identity arguments -> inferMetaCheck context identity arguments
  RecordType fields -> do
    unless (canonicalFields fields) (failCheck "record fields must be distinct and sorted")
    levels <- traverse (checkTypeWith operations context . snd) fields
    pure (N.VSort (U.normaliseLevel (foldr LMax LZero levels)))
  Record fields -> do
    unless (canonicalFields fields) (failCheck "record fields must be distinct and sorted")
    N.VRecordType <$> traverse (\(name, field) -> (name,) <$> inferTermWith operations context field) fields
  Project record name ->
    inferTermWith operations context record >>= forceCheck >>= \case
      N.VRecordType fields | Just ty <- lookup name fields -> pure ty
      N.VRecordType _ -> failCheck ("record hath no field '" ++ name ++ "'")
      _ -> failCheck "projection from a non-record"
  -- a field's type is the constructor's field type, with the family's
  -- parameters and each earlier field, projected from the same value.
  Field index value ->
    inferTermWith operations context value >>= forceCheck >>= \case
      N.VNeutral neutral
        | (N.NGlobal family levels, arguments) <- N.neutralSpine neutral ->
            definitionCheck family >>= \case
              Just Definition {definitionBody = TypeConstructor InductiveInfo {inductiveParameterCount, inductiveIndexPlicities = [], inductiveConstructorInfo = [(constructor, fields)]}}
                | index >= 0,
                  index < length fields,
                  length arguments == inductiveParameterCount ->
                    definitionCheck constructor >>= \case
                      Just Definition {definitionType} -> do
                        constructorType <- liftCheck (instantiateLevels levels definitionType) >>= evaluateCheck emptyContext
                        let parameter ty argument =
                              forceCheck ty >>= \case
                                N.VPi _ _ codomain -> instantiateCheck codomain argument
                                _ -> failCheck "invalid constructor type"
                            walk ty position =
                              forceCheck ty >>= \case
                                N.VPi _ domain codomain
                                  | position == index -> pure domain
                                  | otherwise -> evaluateCheck context (Field position value) >>= instantiateCheck codomain >>= (`walk` (position + 1))
                                _ -> failCheck "invalid constructor type"
                        afterParameters <- foldlM parameter constructorType (map snd arguments)
                        walk afterParameters 0
                      _ -> failCheck "missing constructor"
              _ -> failCheck "a field projection needeth a one-constructor family without indices"
      _ -> failCheck "a field projection needeth a one-constructor family without indices"
  Literal name value
    | name == literalType value -> evaluateCheck context (Global name [])
    | otherwise -> failCheck ("a literal requireth the primitive " ++ symbolName (literalType value) ++ " type")

checkType :: Globals -> Context -> Term -> Typing Level
checkType globals = checkTypeWith (kernelChecking globals)

checkTypeWith :: (Monad m) => Checking m -> Context -> Term -> m Level
checkTypeWith operations@Checking {..} context term =
  inferTermWith operations context term >>= forceCheck >>= \case
    N.VSort level -> pure level
    _ -> failCheck "annotation is not a type"

checkTerm :: Globals -> Context -> Term -> Term -> Typing ()
checkTerm globals = checkTermWith (kernelChecking globals)

checkTermWith :: (Monad m) => Checking m -> Context -> Term -> Term -> m ()
checkTermWith operations@Checking {..} context term annotation = do
  actual <- inferTermWith operations context term
  expected <- evaluateCheck context annotation
  convertCheck context actual expected

rejectMetas :: Term -> Either String ()
rejectMetas = \case
  Meta _ _ -> Left "unresolved term inference hole in core"
  term -> traverse_ (rejectMetas . snd) (children term)

convert :: Globals -> Context -> N.Value -> N.Value -> Typing ()
convert globals Context {contextTypes} actual expected = do
  let depth = length contextTypes
  -- identical folded terms are definitionally equal, including their levels.
  -- other comparisons use the complete normal forms below.
  leftFolded <- lift (N.quoteFoldedWith (N.closed globals) depth actual)
  rightFolded <- lift (N.quoteFoldedWith (N.closed globals) depth expected)
  unless (leftFolded == rightFolded) do
    left <- lift (N.quote globals depth actual)
    right <- lift (N.quote globals depth expected)
    compareTerms left right
  where
    compareTerms (Sort left) (Sort right) = oblige (LevelEqual left right)
    compareTerms (Local left) (Local right) | left == right = pure ()
    compareTerms (Global left ls) (Global right rs) | left == right, length ls == length rs = traverse_ oblige (zipWith LevelEqual ls rs)
    compareTerms (Pi lp ld lc) (Pi rp rd rc) | lp == rp = compareTerms ld rd >> compareTerms lc rc
    compareTerms (Lambda lp ld lb) (Lambda rp rd rb) | lp == rp = compareTerms ld rd >> compareTerms lb rb
    compareTerms (Apply lp lf la) (Apply rp rf ra) | lp == rp = compareTerms lf rf >> compareTerms la ra
    compareTerms (Literal ln lv) (Literal rn rv) | ln == rn, lv == rv = pure ()
    compareTerms (RecordType left) (RecordType right) | map fst left == map fst right = traverse_ (uncurry compareTerms) (zip (map snd left) (map snd right))
    compareTerms (Record left) (Record right) | map fst left == map fst right = traverse_ (uncurry compareTerms) (zip (map snd left) (map snd right))
    compareTerms (Project left ln) (Project right rn) | ln == rn = compareTerms left right
    compareTerms (Field li left) (Field ri right) | li == ri = compareTerms left right
    -- η: a function equaleth the lambda that applieth it.
    compareTerms (Lambda lp _ lb) right = compareTerms lb (Apply lp (shiftTerm 1 right) (Local 0))
    compareTerms left (Lambda rp _ rb) = compareTerms (Apply rp (shiftTerm 1 left) (Local 0)) rb
    compareTerms a b = failure (renderMismatch (length contextTypes) a b)

canonicalFields :: [(String, a)] -> Bool
canonicalFields fields = and (zipWith (<) names (drop 1 names))
  where
    names = map fst fields

mapConstraint :: (Level -> Level) -> Constraint -> Constraint
mapConstraint f (LevelEqual left right) = LevelEqual (f left) (f right)
mapConstraint f (LevelBelow left right) = LevelBelow (f left) (f right)

validLevel :: Maybe Int -> Bool -> Level -> Either String ()
validLevel bound holes = \case
  LParam index | index < 0 || maybe False (index >=) bound -> Left "unbound universe parameter"
  LMeta index | index < 0 || not holes -> Left "unresolved universe inference hole"
  LSucc level -> validLevel bound holes level
  LMax left right -> validLevel bound holes left >> validLevel bound holes right
  _ -> Right ()

-- direct hole equations are substituted; max constraints are retained rather
-- than choosing one of their branches. exported constraints qualify generalised
-- parameters and are rechecked at every global application.
generalise :: Term -> Term -> [Constraint] -> Either String Inferred
generalise term annotation constraints = do
  (universes, assumptions, terms) <- generaliseTerms [term, annotation] constraints
  case terms of
    [body, ty] -> pure (Inferred universes assumptions body ty)
    _ -> Left "invalid universe generalisation result"

-- a mutually scoped declaration group shareth one universe substitution. this
-- keepeth family signatures, constructor fields, and self references aligned.
generaliseTerms :: [Term] -> [Constraint] -> Either String (Int, [Constraint], [Term])
generaliseTerms terms constraints = do
  unless (U.satisfiable constraints) (Left "inconsistent universe constraints")
  let substitution = foldl solve Map.empty constraints
      resolve = U.normaliseLevel . replace substitution
      solved = nubOrd [constraint | original <- constraints, let constraint = mapConstraint resolve original, not (U.trivial constraint)]
      levels = map resolve (concatMap termLevels terms) ++ concatMap constraintLevels solved
      atoms = Set.unions (map levelAtoms levels)
      parameters = [index | LParam index <- Set.toList atoms]
      base = maximum (0 : map (+ 1) parameters)
      holes = sort [index | LMeta index <- Set.toList atoms]
      names = Map.fromList (zip holes [base ..])
      finish = U.normaliseLevel . rename names . resolve
  pure (base + length holes, map (mapConstraint finish) solved, map (mapLevels finish) terms)
  where
    -- one pass sufficeth: a substitution only replaceth holes, so an
    -- equation that is not a hole equation now never becometh one later.
    solve substitution constraint = case mapConstraint (U.normaliseLevel . replace substitution) constraint of
      LevelEqual left right
        | (index, level) : _ <- [(index, level) | (LMeta index, level) <- [(left, right), (right, left)], LMeta index `Set.notMember` levelAtoms level] ->
            Map.insert index level substitution
      _ -> substitution
    replace substitution = \case
      LMeta index | Just level <- Map.lookup index substitution -> replace substitution level
      LSucc level -> LSucc (replace substitution level)
      LMax left right -> LMax (replace substitution left) (replace substitution right)
      level -> level
    rename names = \case
      LMeta index -> LParam (names Map.! index)
      LSucc level -> LSucc (rename names level)
      LMax left right -> LMax (rename names left) (rename names right)
      level -> level

levelAtoms :: Level -> Set.Set Level
levelAtoms = \case
  LSucc level -> levelAtoms level
  LMax left right -> Set.union (levelAtoms left) (levelAtoms right)
  level -> Set.singleton level
