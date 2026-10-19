{-# LANGUAGE RankNTypes #-}

-- | typed contextual inference holes. solutions abstract a rigid telescope;
-- the independent kernel never accepteth these temporary terms.
module Tung.Dependent.Elaboration
  ( Elaboration,
    termHoles,
    metaSpine,
    runElaboration,
    recover,
    kernel,
    failure,
    raise,
    fromEither,
    freshLevel,
    freshLevels,
    freshUniverses,
    newMeta,
    newMetaWithout,
    evaluate,
    evaluateGlued,
    instantiate,
    quote,
    quoteFolded,
    resolver,
    force,
    ensurePi,
    unify,
    approximate,
    approximateFlexible,
    zonk,
    unsolved,
    infer,
    attempt,
    located,
    probe,
    speculate,
    trial,
    repeatProgress,
    InstanceGoal (..),
    addInstanceGoal,
    markCarriers,
    takeInstanceGoals,
    HoleSite (..),
    recordHole,
    takeHoles,
    takeReferences,
    recordName,
    takeNames,
  )
where

import Control.Applicative ((<|>))
import Control.Monad (filterM, foldM, forM, mfilter, replicateM, unless, when, zipWithM_)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.Except (ExceptT, catchE, runExceptT, throwE, withExceptT)
import Control.Monad.Trans.State.Strict (State, StateT, runState, runStateT)
import Control.Monad.Trans.State.Strict qualified as State
import Data.Either (isRight)
import Data.Functor.Const (Const (..))
import Data.List (find)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, isJust, isNothing)
import Data.Set qualified as Set
import Data.Traversable (mapAccumM)
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Render (renderMismatchWith)
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Syntax
import Tung.Dependent.Universe qualified as U
import Tung.Identity (SymbolId)
import Tung.Primitive (HostBinding (..), HostSignature (..), findForeignBinding, pureOperation)
import Tung.Token (SourceFailure (..), SourceSpan)

data MetaEntry = MetaEntry
  { metaDomains :: [Term],
    metaTarget :: Term,
    metaSolution :: Maybe Term
  }

-- the captured telescope is stored once; arity and the closed type cannot drift.
metaArity :: MetaEntry -> Int
metaArity = length . metaDomains

metaType :: MetaEntry -> Term
metaType MetaEntry {..} = foldr (Pi Explicit) metaTarget metaDomains

data Equation = Equation Int K.Context N.Value N.Value

data Inference = Inference
  { displaySymbol :: SymbolId -> String,
    -- the definitions in scope.
    inferenceGlobals :: Globals,
    nextLevel :: Int,
    nextMeta :: Int,
    nextEquation :: Int,
    metaEntries :: Map.Map Int MetaEntry,
    pendingEquations :: [Equation],
    checkingSolutions :: Set.Set Int,
    solutionVersion :: Int,
    -- every pending equation was attempted after this solution version.
    retriedVersion :: Int,
    -- a candidate that could not settle, and the unsolved holes it waiteth on.
    unsettled :: Map.Map Int (Term, Set.Set Int),
    retryingEquations :: Bool,
    instanceGoals :: [InstanceGoal],
    -- holes that an instance goal mentioned, such as a flock carrier `?φ`.
    -- instance search and approximation solve them, not abstraction.
    carriers :: Set.Set Int,
    -- each `sorry` checked so far, newest first, for goal display.
    holeSites :: [HoleSite],
    -- checked input references survive normalisation of annotations and
    -- local bindings. speculative trials roll them back with their solutions.
    checkedReferences :: Set.Set SymbolId,
    -- each written name resolved to a global, by its span, and whether that
    -- global nameth an ilk, newest first. speculative trials roll them back
    -- with their solutions.
    resolvedNames :: [(SourceSpan, SymbolId, Bool)]
  }

-- a `sorry` with its source span, context, local names (innermost first),
-- and expected type.
data HoleSite = HoleSite
  { holeSpan :: Maybe SourceSpan,
    holeContext :: K.Context,
    holeNames :: [Maybe String],
    holeGoal :: N.Value
  }

-- an implicit input whose type is a flock is solved by instance search. the
-- hole stayeth open until the caller's search assigneth it.
data InstanceGoal = InstanceGoal
  { goalHole :: N.Value,
    goalContext :: K.Context,
    goalType :: N.Value
  }

-- a failed declaration retaineth its goal sites for diagnostics. speculative
-- checking still restoreth both states explicitly in `trial`.
type Elaboration = ExceptT SourceFailure (StateT Inference (State U.Universes))

runElaboration :: (SymbolId -> String) -> Globals -> Elaboration a -> Either SourceFailure (a, [Constraint])
runElaboration display globals action =
  let ((result, _), constraints) = runState (runStateT (runExceptT action) initial) (U.universes [])
   in (,U.universeConstraints constraints) <$> result
  where
    initial = Inference display globals 0 0 0 Map.empty [] Set.empty 0 0 Map.empty False [] Set.empty [] Set.empty []

-- recover a diagnostic within the same inference state, without producing a
-- checked term. callers may render the goals already encountered.
recover :: Elaboration a -> Elaboration (Either SourceFailure a)
recover action = catchE (Right <$> action) (pure . Left)

get :: Elaboration Inference
get = lift State.get

put :: Inference -> Elaboration ()
put = lift . State.put

modify' :: (Inference -> Inference) -> Elaboration ()
modify' = lift . State.modify'

-- a global nameth an ilk when its type, after its inputs, is a sort; the
-- editor coloureth a name by it, which syntax alone cannot tell.
recordName :: SourceSpan -> SymbolId -> Elaboration ()
recordName span symbol = do
  globals <- currentGlobals
  let ilk = maybe False (sorted . definitionType) (Map.lookup symbol globals)
  modify' (\state -> state {resolvedNames = (span, symbol, ilk) : resolvedNames state})
  where
    sorted = \case
      Pi _ _ result -> sorted result
      Sort _ -> True
      _ -> False

-- the names resolved so far, oldest first.
takeNames :: Elaboration [(SourceSpan, SymbolId, Bool)]
takeNames = reverse . resolvedNames <$> get

takeReferences :: Elaboration (Set.Set SymbolId)
takeReferences = checkedReferences <$> get

recordReferences :: Term -> Elaboration ()
recordReferences term = modify' (\state -> state {checkedReferences = Set.union (checkedReferences state) (references term)})
  where
    references = \case
      Global symbol _ -> Set.singleton symbol
      Literal symbol _ -> Set.singleton symbol
      value -> Set.unions (map (references . snd) (children value))

kernel :: K.Typing a -> Elaboration a
kernel action = do
  constraints <- lift (lift State.get)
  (result, constraints') <- either raise pure (Error.fromString (runStateT action constraints))
  lift (lift (State.put constraints'))
  pure result

addInstanceGoal :: InstanceGoal -> Elaboration ()
addInstanceGoal goal = modify' (\state -> state {instanceGoals = goal : instanceGoals state})

-- the unsolved holes in a new instance goal's type are carriers.
markCarriers :: K.Context -> N.Value -> Elaboration ()
markCarriers context ty = do
  term <- quote (K.contextDepth context) ty
  modify' (\state -> state {carriers = Set.union (Set.fromList (termHoles term)) (carriers state)})

recordHole :: HoleSite -> Elaboration ()
recordHole site = modify' (\state -> state {holeSites = site : holeSites state})

-- the holes recorded so far, oldest first.
takeHoles :: Elaboration [HoleSite]
takeHoles = do
  sites <- holeSites <$> get
  modify' (\state -> state {holeSites = []})
  pure (reverse sites)

takeInstanceGoals :: Elaboration [InstanceGoal]
takeInstanceGoals = do
  goals <- instanceGoals <$> get
  modify' (\state -> state {instanceGoals = []})
  -- goals are stored in reverse, so adding one taketh constant time.
  pure (reverse goals)

-- retain the innermost failing expression's location through source context
-- and speculative checking. the kernel needeth no source-location dependency.
located :: SourceSpan -> Elaboration a -> Elaboration a
located span = withExceptT (\message -> message {failureSpan = failureSpan message <|> Just span})

-- run an action and keep its effects only if it succeedeth. instance search
-- useth this to try candidates without leaking a failed unification.
attempt :: Elaboration a -> Elaboration (Maybe a)
attempt action = speculate action >>= traverse (\(result, commit) -> result <$ commit)

-- run an action without keeping its effects. a success returneth the result and
-- an action that keepeth them, so a search runneth each candidate once.
speculate :: Elaboration a -> Elaboration (Maybe (a, Elaboration ()))
speculate = fmap (either (const Nothing) Just) . trial

-- retain a rejected candidate's reason for source diagnostics, without
-- committing its metavariable or universe state.
trial :: Elaboration a -> Elaboration (Either SourceFailure (a, Elaboration ()))
trial action = do
  inference <- get
  constraints <- lift (lift State.get)
  let ((result, inference'), constraints') = runState (runStateT (runExceptT action) inference) constraints
  pure ((,put inference' >> lift (lift (State.put constraints'))) <$> result)

-- shared fixed-point scheduling. each phase retaineth its own queue and
-- progress rule; no last-resort search is moved before ordinary constraints.
repeatProgress :: (Monad m) => m Bool -> m ()
repeatProgress step = step >>= \progressed -> when progressed (repeatProgress step)

-- report whether an action would succeed, without keeping its effects.
probe :: Elaboration a -> Elaboration Bool
probe = fmap isRight . trial

failure :: String -> Elaboration a
failure = either raise pure . Error.failure

-- rethrow a speculative failure without losing its source location.
raise :: SourceFailure -> Elaboration a
raise = throwE

fromEither :: Either String a -> Elaboration a
fromEither = either raise pure . Error.fromString

freshLevel :: Elaboration Level
freshLevel = do
  index <- nextLevel <$> get
  modify' (\state -> state {nextLevel = index + 1})
  pure (LMeta index)

freshLevels :: Int -> Elaboration [Level]
freshLevels count = replicateM count freshLevel

-- fresh universe levels for each of a global's universe parameters.
freshUniverses :: SymbolId -> Elaboration [Level]
freshUniverses symbol =
  currentGlobals >>= maybe (failure "missing global definition") (freshLevels . definitionUniverses) . Map.lookup symbol

entry :: Int -> Elaboration MetaEntry
entry identity = Map.lookup identity . metaEntries <$> get >>= maybe (failure "unknown term inference hole") pure

resolver :: Elaboration N.MetaResolver
resolver = do
  entries <- metaEntries <$> get
  pure (\identity -> maybe (Left "unknown term inference hole") (Right . metaSolution) (Map.lookup identity entries))

currentGlobals :: Elaboration Globals
currentGlobals = inferenceGlobals <$> get

-- the hole solutions and definitions that normalisation readeth.
normaliser :: Elaboration N.Normaliser
normaliser = N.Normaliser <$> resolver <*> currentGlobals

-- run a normalisation with the current hole solutions and definitions.
normalised :: (N.Normaliser -> Either String a) -> Elaboration a
normalised use = normaliser >>= fromEither . use

evaluate :: K.Context -> Term -> Elaboration N.Value
evaluate K.Context {contextValues} term = do
  recordReferences term
  normalised \normal -> N.evaluateWith normal contextValues term

-- a worth whose definitions stay folded until forced, for an argument that
-- only instantiateth a codomain.
evaluateGlued :: K.Context -> Term -> Elaboration N.Value
evaluateGlued K.Context {contextValues} term = do
  recordReferences term
  normalised \normal -> N.evaluateGlued normal contextValues term

instantiate :: N.Closure -> N.Value -> Elaboration N.Value
instantiate closure argument = normalised \normal -> N.instantiateWith normal closure argument

quote :: Int -> N.Value -> Elaboration Term
quote depth value = normalised \normal -> N.quoteWith normal depth value

-- the same value with definitions kept by name, for terms that are evaluated
-- again, such as motives.
quoteFolded :: Int -> N.Value -> Elaboration Term
quoteFolded depth value = normalised \normal -> N.quoteFoldedWith normal depth value

force :: N.Value -> Elaboration N.Value
force value = normalised (`N.forceWith` value)

operations :: K.Checking Elaboration
operations =
  K.Checking
    { K.failCheck = failure,
      K.liftCheck = fromEither,
      K.evaluateCheck = evaluate,
      K.argumentCheck = evaluateGlued,
      K.quoteCheck = quote,
      K.instantiateCheck = instantiate,
      K.forceCheck = force,
      K.convertCheck = unify,
      K.constrainCheck = kernel . K.oblige,
      K.inferMetaCheck = inferMeta,
      K.definitionCheck = \name -> Map.lookup name <$> currentGlobals
    }

infer :: K.Context -> Term -> Elaboration N.Value
infer context term = recordReferences term >> K.inferTermWith operations context term

-- definitions are already substituted in semantic contexts. only distinct
-- rigid levels are captured, so aliases neither duplicate nor invent binders.
newMeta :: K.Context -> N.Value -> Elaboration (Term, N.Value)
newMeta context = newMetaWithout context []

-- a hole that cannot depend on the given locals, such as a match's result
-- type, which must not mention the values it matcheth.
newMetaWithout :: K.Context -> [Int] -> N.Value -> Elaboration (Term, N.Value)
newMetaWithout K.Context {..} excluded expected = do
  captures <- forM (zip contextValues contextTypes) \(value, ty) -> do
    forced <- force value
    pure case forced of
      N.VNeutral (N.NLocal level) | level `notElem` excluded -> Just (level, (forced, ty))
      _ -> Nothing
  let telescope = Map.toAscList (Map.fromList (catMaybes captures))
      originalDepth = length contextTypes
      values = map (fst . snd) telescope
      mapping = Map.fromList (zip (map fst telescope) [0 ..])
  domains <- forM (zip [0 ..] telescope) \(position, (_, (_, ty))) ->
    quote originalDepth ty >>= fromEither . rename originalDepth position (Map.filter (< position) mapping)
  annotation <- quote originalDepth expected >>= fromEither . rename originalDepth (length telescope) mapping
  kind <- infer K.emptyContext (foldr (Pi Explicit) annotation domains) >>= force
  case kind of
    N.VSort _ -> pure ()
    _ -> failure "term inference hole requireth an ilk"
  identity <- nextMeta <$> get
  modify' (\state -> state {nextMeta = identity + 1, metaEntries = Map.insert identity (MetaEntry domains annotation Nothing) (metaEntries state)})
  arguments <- traverse (quote originalDepth) values
  pure (Meta identity arguments, N.VNeutral (N.NMeta identity values))

inferMeta :: K.Context -> Int -> [Term] -> Elaboration N.Value
inferMeta context identity arguments = do
  meta <- entry identity
  unless (length arguments == metaArity meta) (failure "wrong term inference telescope arity")
  ty <- evaluate K.emptyContext (metaType meta)
  foldM apply ty arguments
  where
    apply ty argument =
      force ty >>= \case
        N.VPi Explicit domain codomain -> do
          actual <- infer context argument
          unify context actual domain
          value <- evaluate context argument
          instantiate codomain value
        _ -> failure "invalid term inference telescope"

-- unknown function types are expanded in their own creation telescope. newer
-- caller binders must not enter the domains of these fresh component holes.
ensurePi :: Plicity -> N.Value -> Elaboration (N.Value, N.Closure)
ensurePi plicity value =
  force value >>= \case
    N.VPi expected domain codomain
      | plicity == expected -> pure (domain, codomain)
      | otherwise -> failure "implicit and explicit arguments do not match"
    N.VNeutral (N.NMeta identity arguments) -> do
      meta@MetaEntry {..} <- entry identity
      unless (length arguments == metaArity meta) (failure "wrong term inference telescope arity")
      pattern <- rigidLevels arguments
      when (isNothing pattern) (failure "nonpattern function ilk inference requireth an annotation")
      (context, domains) <- mapAccumM telescope K.emptyContext metaDomains
      kind <- evaluate context metaTarget
      force kind >>= \case
        N.VSort _ -> pure ()
        _ -> failure "unknown function ilk is not an ilk"
      domainLevel <- freshLevel
      (domain, domainValue) <- newMeta context (N.VSort domainLevel)
      codomainLevel <- freshLevel
      (codomain, _) <- newMeta (K.bind context domainValue) (N.VSort codomainLevel)
      commit identity (foldr (Lambda Explicit) (Pi plicity domain codomain) domains)
      retry
      force value >>= \case
        N.VPi _ actualDomain actualCodomain -> pure (actualDomain, actualCodomain)
        _ -> failure "function inference did not produce a product"
    _ -> failure "application requireth a function"
  where
    telescope context annotation = do
      domain <- evaluate context annotation
      domainTerm <- quote (K.contextDepth context) domain
      pure (K.bind context domain, domainTerm)

unify :: K.Context -> N.Value -> N.Value -> Elaboration ()
unify context left right = do
  solved <- unifyNow context left right
  unless solved (postpone context left right)
  retry

postpone :: K.Context -> N.Value -> N.Value -> Elaboration ()
postpone context left right = modify' (\state -> state {nextEquation = nextEquation state + 1, pendingEquations = Equation (nextEquation state) context left right : pendingEquations state})

unifyNow :: K.Context -> N.Value -> N.Value -> Elaboration Bool
unifyNow context left right = do
  -- two applications of one constant with the same folded arguments are
  -- equal without unfolding either, which mattereth for a host operation
  -- whose model unfoldeth deeply.
  same <- case (constantHead left, constantHead right) of
    (Just one, Just other) | one == other -> do
      let depth = K.contextDepth context
      (==) <$> quoteFolded depth left <*> quoteFolded depth right
    _ -> pure False
  if same then pure True else unifyForced context left right

-- the constant at the head of a folded definition or a neutral application.
constantHead :: N.Value -> Maybe (SymbolId, [Level])
constantHead = \case
  N.VGlued name levels _ _ -> Just (name, levels)
  N.VNeutral neutral | (N.NGlobal name levels, _) <- N.neutralSpine neutral -> Just (name, levels)
  _ -> Nothing

unifyForced :: K.Context -> N.Value -> N.Value -> Elaboration Bool
unifyForced context left right = do
  actual <- force left
  expected <- force right
  case (actual, expected) of
    (N.VSort u, N.VSort v) -> do
      unless (u == v) (kernel (K.oblige (LevelEqual u v)))
      pure True
    (N.VPi p domain body, N.VPi q otherDomain otherBody) | p == q -> binders domain body otherDomain otherBody
    (N.VLambda p domain body, N.VLambda q otherDomain otherBody) | p == q -> binders domain body otherDomain otherBody
    -- η: a lambda equaleth a rigid function applied to the same input.
    (N.VLambda p domain body, other) | rigid other -> eta p domain body other False
    (other, N.VLambda p domain body) | rigid other -> eta p domain body other True
    -- rigid neutrals are compared by congruence, which recurseth once per
    -- node; quoting both sides at every level would be quadratic. only
    -- applications of one hole are compared whole.
    (N.VNeutral _, N.VNeutral _)
      | Just (left, _) <- metaSpine actual,
        Just (right, _) <- metaSpine expected,
        left == right -> do
          same <- quotedEqual actual expected
          if same then pure True else flexible actual expected
      | otherwise -> flexible actual expected
    _ -> flexible actual expected
  where
    depth = K.contextDepth context
    variable = N.VNeutral (N.NLocal depth)
    quotedEqual one other = (==) <$> quote depth one <*> quote depth other
    rigid value = case value of
      N.VNeutral _ -> isNothing (metaSpine value)
      _ -> False
    eta plicity domain body other flipped = do
      blocked <- blockedComputation context other
      if blocked
        then pure False
        else do
          lambdaSide <- instantiate body variable
          otherSide <- normalised \normal -> N.applyValueWith normal plicity other variable
          let current = K.bind context domain
          if flipped then unify current otherSide lambdaSide else unify current lambdaSide otherSide
          pure True
    binders domain body otherDomain otherBody = do
      first <- unifyNow context domain otherDomain
      unless first (postpone context domain otherDomain)
      let current = K.bind context domain
      a <- instantiate body variable
      b <- instantiate otherBody variable
      second <- unifyNow current a b
      unless second (postpone current a b)
      pure True
    -- a hole is solved by the unforced other side, so the solution keepeth
    -- its definitions folded.
    flexible actual expected = case (metaSpine actual, metaSpine expected) of
      (Just (leftId, _), Just (rightId, _)) | leftId == rightId -> pure False
      (Just (identity, arguments), other) -> do
        solved <- solvePattern context identity arguments right
        if solved
          then pure True
          else case other of
            Just (otherIdentity, otherArguments) -> solvePattern context otherIdentity otherArguments left
            Nothing -> abstracted identity arguments expected actual expected
      (Nothing, Just (identity, arguments)) -> do
        solved <- solvePattern context identity arguments left
        if solved then pure True else abstracted identity arguments actual actual expected
      _ -> do
        blocked <- (||) <$> blockedComputation context actual <*> blockedComputation context expected
        if blocked then quotedEqual actual expected else structure actual expected
    -- η for a family with one constructor and no indices: its constructor
    -- applied to fields equaleth a rigid worth by those fields; two
    -- applications of the constructor are compared by congruence.
    structure actual expected = do
      globals <- currentGlobals
      let fields = \case
            N.VNeutral neutral -> N.etaFields globals neutral
            _ -> Nothing
          byFields constructed other flipped = do
            let project index value = do
                  projected <- force (N.VNeutral (N.NField index other))
                  if flipped then unify context projected value else unify context value projected
            zipWithM_ project [0 ..] constructed
            pure True
      case (fields actual, fields expected) of
        (Just constructed, Nothing) | rigid expected, N.VNeutral other <- expected -> byFields constructed other False
        (Nothing, Just constructed) | rigid actual, N.VNeutral other <- actual -> byFields constructed other True
        _ -> congruent actual expected
    -- occurrences are abstracted up to universe levels, so the solved sides
    -- are equated again.
    abstracted identity arguments rigidSide actual expected = do
      solved <- solveAbstraction context identity arguments rigidSide
      when solved (unify context actual expected)
      pure solved
    congruent (N.VNeutral (N.NLocal left)) (N.VNeutral (N.NLocal right)) | left == right = pure True
    congruent (N.VNeutral (N.NApply p function argument)) (N.VNeutral (N.NApply q otherFunction otherArgument)) | p == q = do
      unify context (N.VNeutral function) (N.VNeutral otherFunction)
      unify context argument otherArgument
      pure True
    congruent (N.VNeutral (N.NGlobal name levels)) (N.VNeutral (N.NGlobal otherName otherLevels))
      | name == otherName,
        length levels == length otherLevels = do
          mapM_ (kernel . K.oblige) (zipWith LevelEqual levels otherLevels)
          pure True
    congruent (N.VRecordType fields) (N.VRecordType others) | map fst fields == map fst others = sameFields fields others
    congruent (N.VRecord fields) (N.VRecord others) | map fst fields == map fst others = sameFields fields others
    congruent (N.VNeutral (N.NField index value)) (N.VNeutral (N.NField otherIndex otherValue)) | index == otherIndex = do
      unify context (N.VNeutral value) (N.VNeutral otherValue)
      pure True
    congruent (N.VNeutral (N.NProject record name)) (N.VNeutral (N.NProject otherRecord otherName)) | name == otherName = do
      unify context (N.VNeutral record) (N.VNeutral otherRecord)
      pure True
    congruent (N.VLiteral name value) (N.VLiteral otherName otherValue)
      | name == otherName,
        value == otherValue =
          pure True
    -- constructor-headed numeric indices expose holes in their fields;
    -- literal comparisons still take the constant-time case above.
    congruent literal@N.VLiteral {} neutral@N.VNeutral {}
      | N.VNeutral constructor <- N.constructorForm literal =
          congruent (N.VNeutral constructor) neutral
    congruent neutral@N.VNeutral {} literal@N.VLiteral {}
      | N.VNeutral constructor <- N.constructorForm literal =
          congruent neutral (N.VNeutral constructor)
    congruent left right = do
      a <- quote depth left
      b <- quote depth right
      display <- displaySymbol <$> get
      failure (renderMismatchWith display depth a b)
    sameFields fields others = True <$ zipWithM_ (unify context) (map snd fields) (map snd others)

metaSpine :: N.Value -> Maybe (Int, [(Plicity, N.Value)])
metaSpine (N.VNeutral neutral)
  | (N.NMeta identity arguments, rest) <- N.neutralSpine neutral =
      Just (identity, map (Explicit,) arguments ++ rest)
metaSpine _ = Nothing

-- eliminators, projections, and native computations are not injective. a
-- meta in their inspected input may change the whole head after solving;
-- postpone its equation instead of equating the computation's arguments.
blockedComputation :: K.Context -> N.Value -> Elaboration Bool
blockedComputation context value = do
  globals <- currentGlobals
  force value >>= \case
    N.VNeutral neutral -> case N.neutralSpine neutral of
      (N.NProject record _, _) -> changing (N.VNeutral record)
      (N.NField _ value, _) -> changing (N.VNeutral value)
      (N.NGlobal name _, arguments) -> case definitionBody <$> Map.lookup name globals of
        Just (Eliminator family)
          | Right info@InductiveInfo {..} <- inductiveInfo globals family -> do
              methods <- fromEither (inductiveMethods globals info)
              let arity = inductiveParameterCount + length inductiveFamilies + length methods + length inductiveIndexPlicities + 1
              case drop (arity - 1) arguments of
                (_, scrutinee) : _ -> changing scrutinee
                _ -> pure False
        Just (Host "literal_case" _) | length arguments >= 6 -> anyM containsMeta (map snd (take 2 (drop 2 arguments)))
        Just (Host key _)
          | Just _ <- pureOperation key,
            Just HostBinding {hostSignature = HostSignature {..}} <- findForeignBinding key,
            length arguments >= length hostVariables + length hostArguments ->
              anyM containsMeta (map snd (drop (length hostVariables) arguments))
        _ -> pure False
      _ -> pure False
    _ -> pure False
  where
    changing input = do
      actual <- force input
      case metaSpine actual of
        Just _ -> pure True
        _ -> blockedComputation context actual
    containsMeta = fmap (not . null . termHoles) . quote (K.contextDepth context)

-- a pattern solution abstracts every distinct rigid argument, including extra
-- applications after the captured telescope. it is checked before committing.
solvePattern :: K.Context -> Int -> [(Plicity, N.Value)] -> N.Value -> Elaboration Bool
solvePattern context identity arguments right = do
  meta@MetaEntry {..} <- entry identity
  active <- checkingSolutions <$> get
  when (Set.member identity active) (failure "cyclic term inference solution")
  when (isJust metaSolution) (failure "term inference solution was already assigned")
  variables <- rigidLevels (map snd arguments)
  case variables of
    Just levels -> do
      let depth = K.contextDepth context
          mapping = Map.fromList (zip levels [0 ..])
      -- a folded solution nameth its definitions, so it stayeth small.
      body <- quoteFolded depth right >>= prune depth mapping
      cyclic <- occurs identity Set.empty body
      when cyclic (failure "occurs check failed for term inference hole")
      case rename depth (length levels) mapping body of
        Left _ -> pure False
        Right renamed -> do
          ty <- evaluate K.emptyContext (metaType meta)
          domains <- patternDomains depth mapping ty arguments
          maybe (pure False) (settle identity . foldr (uncurry Lambda) renamed) domains
    _ -> pure False

-- a hole of function type applied to inputs that are not all distinct
-- locals, as a property `?p b` meeting the goal of `throughbear`, is solved by
-- abstracting those inputs from the other side, as lean's `▸` doth. the side
-- is searched as written first and as a normal form second, so `first p`
-- is found inside `(first ‥ rest) sift p`. every abstracted input must
-- occur, neither side may hold an unsolved hole, and a carrier is left to
-- instance search. a candidate that the kernel rejecteth is no solution.
solveAbstraction :: K.Context -> Int -> [(Plicity, N.Value)] -> N.Value -> Elaboration Bool
solveAbstraction context identity arguments right = do
  meta@MetaEntry {..} <- entry identity
  carrier <- Set.member identity . carriers <$> get
  let (captured, extra) = splitAt (metaArity meta) arguments
  variables <- rigidLevels (map snd captured)
  forced <- traverse (force . snd) extra
  case variables of
    Just levels
      | not carrier,
        isNothing metaSolution,
        not (null extra) -> do
          -- a local not seen before is a pattern variable; any other input is
          -- abstracted.
          let classify (seen, targets) (position, value) = case value of
                N.VNeutral (N.NLocal level) | Map.notMember level seen -> (Map.insert level position seen, targets)
                _ -> (seen, targets ++ [(position, value)])
              (mapping, targets) = foldl classify (Map.fromList (zip levels [0 ..]), []) (zip [metaArity meta ..] forced)
          ty <- evaluate K.emptyContext (metaType meta)
          domains <- telescopeDomains (metaArity meta + length extra) ty
          case domains of
            Just binders
              | not (null targets),
                map fst (drop (metaArity meta) binders) == map fst extra ->
                  anyM (candidate mapping targets binders) [quoteFolded, quote]
            _ -> pure False
    _ -> pure False
  where
    depth = K.contextDepth context
    candidate mapping targets binders quoting = do
      body <- quoting depth right
      abstracted <- traverse (quoting depth . snd) targets
      let (abstraction, found) = abstractTerms abstracted body
          extended = Map.union mapping (Map.fromList [(depth + offset, position) | (offset, (position, _)) <- zip [0 ..] targets])
      case rename (depth + length targets) (length binders) extended abstraction of
        Right renamed
          | and found,
            all (null . termHoles) (body : abstracted) ->
              speculate (settle identity (foldr (uncurry Lambda) renamed binders)) >>= \case
                Just (True, keep) -> True <$ keep
                _ -> pure False
        _ -> pure False

-- the first domains of a closed type, each over the binders before it.
telescopeDomains :: Int -> N.Value -> Elaboration (Maybe [(Plicity, Term)])
telescopeDomains count = go 0
  where
    go position ty
      | position == count = pure (Just [])
      | otherwise =
          force ty >>= \case
            N.VPi plicity domain codomain -> do
              domainTerm <- quoteFolded position domain
              rest <- instantiate codomain (N.VNeutral (N.NLocal position)) >>= go (position + 1)
              pure (((plicity, domainTerm) :) <$> rest)
            _ -> pure Nothing

-- a hole in a solution may capture a local that the solved hole cannot see,
-- as `?f x` in `?t := ?f x` when `?t` hath no `x`. if the hole's type doth
-- not need that input, it is replaced by a fresh hole without it, and the
-- solution is quoted again. the body is quoted at `depth`; `mapping` holdeth
-- the levels the solution may mention.
prune :: Int -> Map.Map Int Int -> Term -> Elaboration Term
prune depth mapping body = case find (not . and . snd) (candidates body) of
  Nothing -> pure body
  Just (target, keeps) ->
    narrow target keeps >>= \case
      True -> requote
      False -> pure body
  where
    -- holes applied only to locals, each with which of its inputs may stay.
    candidates = getConst . traverseScoped collect
    collect bound (Meta target arguments) _
      | Just keeps <- traverse (allowed bound) arguments = Const [(target, keeps)]
    collect _ _ descend = descend
    allowed bound = \case
      Local index
        | index < bound -> Just True
        | otherwise -> Just (Map.member (depth - 1 - (index - bound)) mapping)
      _ -> Nothing
    requote = normalised (\normal -> N.evaluateWith normal (N.openEnvironment depth) body) >>= quote depth >>= prune depth mapping
    narrow target keeps = do
      MetaEntry {metaDomains = domains, metaTarget = result, metaSolution} <- entry target
      case metaSolution of
        Nothing
          | Just (keptDomains, keptResult) <- strengthened keeps domains result -> do
              fresh <- nextMeta <$> get
              modify' (\state -> state {nextMeta = fresh + 1, metaEntries = Map.insert fresh (MetaEntry keptDomains keptResult Nothing) (metaEntries state)})
              let arguments = [Local (length domains - 1 - position) | (position, True) <- zip [0 ..] keeps]
              commit target (foldr (Lambda Explicit) (Meta fresh arguments) domains)
              pure True
        _ -> pure False

-- a telescope without the inputs not kept, if nothing kept mentioneth them.
strengthened :: [Bool] -> [Term] -> Term -> Maybe ([Term], Term)
strengthened keeps domains result = do
  kept <- sequence [dropInputs (reverse (take position keeps)) domain | (position, (True, domain)) <- zip [0 ..] (zip keeps domains)]
  (kept,) <$> dropInputs (reverse keeps) result
  where
    -- `flags` mark the enclosing inputs, innermost first.
    dropInputs flags = traverseScoped dropLocal
      where
        dropLocal bound (Local index) _
          | index < bound = Just (Local index)
          | otherwise =
              let outer = index - bound
               in if flags !! outer then Just (Local (bound + length (filter id (take outer flags)))) else Nothing
        dropLocal _ _ descend = descend

rigidLevels :: [N.Value] -> Elaboration (Maybe [Int])
rigidLevels arguments = do
  levels <- traverse (fmap rigid . force) arguments
  pure (mfilter (\variables -> length variables == Set.size (Set.fromList variables)) (sequence levels))
  where
    rigid (N.VNeutral (N.NLocal level)) = Just level
    rigid _ = Nothing

commit :: Int -> Term -> Elaboration ()
commit identity candidate =
  assign identity candidate >>= \case
    Right () -> pure ()
    Left (_, Just problem) -> raise problem
    Left (_, Nothing) -> failure "inference solution typing requireth an annotation"

-- a candidate whose typing waiteth on another hole, such as a dictionary
-- projection before instance search, is not assigned. its check is undone
-- and the caller keepeth the equation postponed until that hole is solved.
-- the same candidate is not checked again until one of those holes is solved.
settle :: Int -> Term -> Elaboration Bool
settle identity candidate = do
  waiting <- Map.lookup identity . unsettled <$> get
  stuck <- case waiting of
    Just (previous, blockers) | previous == candidate -> all (isNothing . metaSolution) <$> traverse entry (Set.toList blockers)
    _ -> pure False
  if stuck
    then pure False
    else
      trial (assign identity candidate) >>= \case
        Left problem -> raise problem
        Right (Right (), keep) -> True <$ keep
        Right (Left (blockers, _), _) -> do
          modify' (\state -> state {unsettled = Map.insert identity (candidate, blockers) (unsettled state)})
          pure False

-- assigneth the candidate if checking it leaveth no new postponed equation.
-- otherwise it returneth the unsolved holes in those equations. a kernel failure
-- is returned with the candidate's unsolved holes, since solving them may
-- give an application its function type; without any, it is raised.
assign :: Int -> Term -> Elaboration (Either (Set.Set Int, Maybe SourceFailure) ())
assign identity candidate = do
  meta@MetaEntry {metaSolution = solution} <- entry identity
  active <- checkingSolutions <$> get
  when (Set.member identity active) (failure "cyclic term inference solution")
  when (isJust solution) (failure "term inference solution was already assigned")
  cyclic <- occurs identity Set.empty candidate
  when cyclic (failure "occurs check failed for term inference hole")
  firstNewEquation <- nextEquation <$> get
  modify' (\state -> state {checkingSolutions = Set.insert identity (checkingSolutions state)})
  trial (K.checkTermWith operations K.emptyContext candidate (metaType meta)) >>= \case
    Left problem -> do
      blockers <- (<>) <$> openHoles candidate <*> openHoles (metaType meta)
      if Set.null blockers then raise problem else pure (Left (blockers, Just problem))
    Right ((), keep) -> do
      keep
      pending <- pendingEquations <$> get
      case [equation | equation@(Equation number _ _ _) <- pending, number >= firstNewEquation] of
        new@(_ : _) -> Left . (,Nothing) . Set.unions <$> traverse equationHoles new
        [] -> do
          latest <- entry identity
          when (isJust (metaSolution latest)) (failure "term inference solution changed during checking")
          modify' (\state -> state {metaEntries = Map.insert identity (latest {metaSolution = Just candidate}) (metaEntries state), checkingSolutions = Set.delete identity (checkingSolutions state), solutionVersion = solutionVersion state + 1})
          pure (Right ())
  where
    equationHoles (Equation _ context left right) = do
      let depth = K.contextDepth context
      (<>) <$> (quote depth left >>= openHoles) <*> (quote depth right >>= openHoles)

-- the holes in a term that are still unsolved.
openHoles :: Term -> Elaboration (Set.Set Int)
openHoles term = Set.fromList <$> filterM (fmap (isNothing . metaSolution) . entry) (termHoles term)

-- the holes a term mentioneth. a quoted term mentioneth only unsolved ones.
termHoles :: Term -> [Int]
termHoles = \case
  Meta target arguments -> target : concatMap termHoles arguments
  other -> concatMap (termHoles . snd) (children other)

patternDomains :: Int -> Map.Map Int Int -> N.Value -> [(Plicity, N.Value)] -> Elaboration (Maybe [(Plicity, Term)])
patternDomains depth mapping = go 0
  where
    go _ _ [] = pure (Just [])
    go position ty ((plicity, argument) : rest) =
      force ty >>= \case
        N.VPi expected domain codomain | plicity == expected -> do
          domainTerm <- quote depth domain
          case rename depth position (Map.filter (< position) mapping) domainTerm of
            Left _ -> pure Nothing
            Right renamed -> do
              result <- instantiate codomain argument
              remaining <- go (position + 1) result rest
              pure (((plicity, renamed) :) <$> remaining)
        _ -> failure "term inference pattern differeth from its ilk"

-- indirect solutions are followed as well; an inference hole cannot conceal
-- a cycle behind another assigned hole or one of its contextual arguments.
occurs :: Int -> Set.Set Int -> Term -> Elaboration Bool
occurs target visited = \case
  Meta identity arguments
    | identity == target -> pure True
    | otherwise -> do
        inArguments <- anyM (occurs target visited) arguments
        if inArguments || Set.member identity visited
          then pure inArguments
          else entry identity >>= maybe (pure False) (occurs target (Set.insert identity visited)) . metaSolution
  term -> anyM (occurs target visited . snd) (children term)

anyM :: (a -> Elaboration Bool) -> [a] -> Elaboration Bool
anyM _ [] = pure False
anyM predicate (value : rest) = do
  found <- predicate value
  if found then pure True else anyM predicate rest

-- quoted terms use indices, but inversion maps their original rigid levels.
-- binders introduced inside the term retain their local indices unchanged.
rename :: Int -> Int -> Map.Map Int Int -> Term -> Either String Term
rename sourceDepth targetDepth mapping = traverseScoped renameLocal
  where
    renameLocal bound (Local index) _
      | index < 0 = Left "negative inference variable index"
      | index < bound = pure (Local index)
      | otherwise =
          let level = sourceDepth - 1 - (index - bound)
           in case Map.lookup level mapping of
                Just target -> pure (Local (bound + targetDepth - 1 - target))
                Nothing -> Left "term inference solution would escape its scope"
    renameLocal _ _ descend = descend

-- an equation is postponed only after an attempt, and its outcome changeth
-- only when a hole is solved. so a retry without a new solution is skipped.
retry :: Elaboration ()
retry = do
  Inference {..} <- get
  unless (retryingEquations || not (Set.null checkingSolutions) || retriedVersion == solutionVersion) do
    modify' (\state -> state {retryingEquations = True})
    loop
    modify' (\state -> state {retryingEquations = False})
  where
    loop = repeatProgress do
      Inference {pendingEquations, solutionVersion = before} <- get
      modify' (\state -> state {pendingEquations = []})
      mapM_ attempt pendingEquations
      after <- solutionVersion <$> get
      when (after == before) (modify' (\state -> state {retriedVersion = after}))
      pure (after /= before)
    attempt (Equation _ context left right) = do
      solved <- unifyNow context left right
      unless solved (postpone context left right)

-- a last resort for a stuck equation between an applied hole and a rigid
-- application: `?f a = g b` becometh `?f = g` and `a = b`, as in agda and
-- lean. it may miss a non-first-order solution, so it runs only when
-- nothing else can progress. the result reporteth whether an equation was split.
approximate :: Elaboration Bool
approximate = approximateWith False

-- like 'approximate', and also between two applied holes. let
-- generalisation useth it last, as hindley-milner unification of type
-- applications doth.
approximateFlexible :: Elaboration Bool
approximateFlexible = approximateWith True

approximateWith :: Bool -> Elaboration Bool
approximateWith both = do
  Inference {pendingEquations} <- get
  split pendingEquations []
  where
    split [] _ = pure False
    split (equation@(Equation _ context left right) : rest) kept = do
      actual <- force left
      expected <- force right
      blocked <- (||) <$> blockedComputation context actual <*> blockedComputation context expected
      case (blocked, applied actual, applied expected) of
        (False, Just (p, function, argument), Just (q, otherFunction, otherArgument))
          | p == q,
            both || flexible actual /= flexible expected -> do
              Inference {solutionVersion = before, pendingEquations = waiting} <- get
              modify' (\state -> state {pendingEquations = reverse kept ++ rest})
              unify context function otherFunction
              unify context argument otherArgument
              -- the postponed parts are split at once, as `?φ ?a x = ∧ α x`
              -- needeth two splits to reach `?φ = ∧`; each split shorteneth
              -- a spine, so this endeth. a split that only postponeth its parts
              -- is no progress, so a caller that retrieth on progress stopeth.
              deeper <- approximateWith both
              Inference {solutionVersion = after, pendingEquations = now} <- get
              pure (deeper || after > before || length now < length waiting)
        _ -> split rest (equation : kept)
    applied = \case
      N.VNeutral (N.NApply plicity function argument) -> Just (plicity, N.VNeutral function, argument)
      _ -> Nothing
    flexible = isJust . metaSpine

-- holes still open after every postponed equation is retried, oldest first,
-- with the type each hole hath beneath its telescope.
unsolved :: Elaboration [(Int, Term)]
unsolved = do
  retry
  Inference {metaEntries} <- get
  pure [(identity, metaTarget) | (identity, MetaEntry {..}) <- Map.toAscList metaEntries, isNothing metaSolution]

-- the boundary rejecteth unresolved holes even when a discarded result no
-- longer mentioneth them. no arbitrary inhabitants or defaults are inserted.
zonk :: Term -> Elaboration Term
zonk term = do
  retry
  Inference {..} <- get
  unless (null pendingEquations) (failure "unsolved inference equation")
  when (any (isNothing . metaSolution) (Map.elems metaEntries)) (failure "unsolved implicit argument or lambda domain")
  traverseScoped expand term
  where
    -- a folded solution keepeth definitions by name; normalising it would
    -- inline every dictionary and proof it reacheth.
    expand depth meta@Meta {} _ = normalised (\normal -> N.evaluateWith normal (N.openEnvironment depth) meta) >>= quoteFolded depth
    expand _ _ descend = descend
