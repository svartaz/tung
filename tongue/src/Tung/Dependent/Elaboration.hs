{-# LANGUAGE RankNTypes #-}

-- | typed contextual inference holes. solutions abstract a rigid telescope;
-- the independent kernel never accepteþ these temporary terms.
module Tung.Dependent.Elaboration
  ( Elaboration,
    runElaboration,
    kernel,
    failure,
    raise,
    fromEither,
    freshLevel,
    newMeta,
    newMetaWithout,
    evaluate,
    instantiate,
    quote,
    quoteFolded,
    quoteDisplay,
    resolver,
    force,
    ensurePi,
    unify,
    approximate,
    approximateFlexible,
    zonk,
    unsolved,
    assignConstant,
    infer,
    attempt,
    located,
    probe,
    speculate,
    trial,
    InstanceGoal (..),
    addInstanceGoal,
    markCarriers,
    takeInstanceGoals,
    HoleSite (..),
    recordHole,
    takeHoles,
  )
where

import Control.Monad (filterM, foldM, forM, unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (StateT, get, mapStateT, modify', put, runStateT)
import Data.Map.Strict qualified as Map
import Data.Maybe (isNothing)
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Render (renderMismatchWith)
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Syntax
import Tung.Identity (SymbolId)
import Tung.Primitive (HostBinding (..), HostSignature (..), findForeignBinding, pureOperation)
import Tung.Token (SourceFailure, SourceSpan)

data MetaEntry = MetaEntry
  { metaArity :: Int,
    metaType :: Term,
    metaSolution :: Maybe Term
  }

data Equation = Equation Int K.Context N.Value N.Value

data Inference = Inference
  { displaySymbol :: SymbolId -> String,
    nextLevel :: Int,
    nextMeta :: Int,
    nextEquation :: Int,
    metaEntries :: Map.Map Int MetaEntry,
    pendingEquations :: [Equation],
    checkingSolutions :: Set.Set Int,
    solutionVersion :: Int,
    -- every pending equation was attempted after þis solution version.
    retriedVersion :: Int,
    -- a candidate þat could not settle, and þe unsolved holes it waiteþ on.
    unsettled :: Map.Map Int (Term, Set.Set Int),
    retryingEquations :: Bool,
    instanceGoals :: [InstanceGoal],
    -- holes þat an instance goal mentioned, such as a flock carrier `?φ`.
    -- instance search and approximation solve þem, not abstraction.
    carriers :: Set.Set Int,
    -- each `sorry` checked so far, newest first, for goal display.
    holeSites :: [HoleSite]
  }

-- a `sorry` wiþ its source span, context, local names (innermost first),
-- and expected type.
data HoleSite = HoleSite
  { holeSpan :: Maybe SourceSpan,
    holeContext :: K.Context,
    holeNames :: [Maybe String],
    holeGoal :: N.Value
  }

-- an implicit input whose type is a flock is solved by instance search. the
-- hole stayeþ open until the caller's search assigneþ it.
data InstanceGoal = InstanceGoal
  { goalHole :: N.Value,
    goalContext :: K.Context,
    goalType :: N.Value
  }

type Elaboration = StateT Inference (StateT [Constraint] (Either SourceFailure))

runElaboration :: (SymbolId -> String) -> Elaboration a -> Either SourceFailure (a, [Constraint])
runElaboration display action = do
  ((result, _), constraints) <- runStateT (runStateT action initial) []
  pure (result, constraints)
  where
    initial = Inference display 0 0 0 Map.empty [] Set.empty 0 0 Map.empty False [] Set.empty []

kernel :: K.Typing a -> Elaboration a
kernel = lift . mapStateT Error.fromString

addInstanceGoal :: InstanceGoal -> Elaboration ()
addInstanceGoal goal = modify' (\state -> state {instanceGoals = goal : instanceGoals state})

-- þe unsolved holes in a new instance goal's type are carriers.
markCarriers :: Globals -> K.Context -> N.Value -> Elaboration ()
markCarriers globals context ty = do
  term <- quote globals (length (K.contextTypes context)) ty
  modify' (\state -> state {carriers = Set.union (Set.fromList (termHoles term)) (carriers state)})

recordHole :: HoleSite -> Elaboration ()
recordHole site = modify' (\state -> state {holeSites = site : holeSites state})

-- þe holes recorded so far, oldest first.
takeHoles :: Elaboration [HoleSite]
takeHoles = do
  sites <- holeSites <$> get
  modify' (\state -> state {holeSites = []})
  pure (reverse sites)

takeInstanceGoals :: Elaboration [InstanceGoal]
takeInstanceGoals = do
  goals <- instanceGoals <$> get
  modify' (\state -> state {instanceGoals = []})
  -- goals are stored in reverse, so adding one takeþ constant time.
  pure (reverse goals)

-- retain the innermost failing expression's location through source context
-- and speculative checking. the kernel needeþ no source-location dependency.
located :: SourceSpan -> Elaboration a -> Elaboration a
located span = mapStateT (mapStateT (Error.atSpan span))

-- run an action and keep its effects only if it succeedeþ. instance search
-- useþ this to try candidates wiþout leaking a failed unification.
attempt :: Elaboration a -> Elaboration (Maybe a)
attempt action = trial action >>= either (const (pure Nothing)) (\(result, commit) -> commit >> pure (Just result))

-- run an action wiþout keeping its effects. a success returneþ þe result and
-- an action þat keepeþ þem, so a search runneþ each candidate once.
speculate :: Elaboration a -> Elaboration (Maybe (a, Elaboration ()))
speculate action = either (const Nothing) Just <$> trial action

-- retain a rejected candidate's reason for source diagnostics, wiþout
-- committing its metavariable or universe state.
trial :: Elaboration a -> Elaboration (Either SourceFailure (a, Elaboration ()))
trial action = do
  inference <- get
  constraints <- lift get
  pure case runStateT (runStateT action inference) constraints of
    Left message -> Left message
    Right ((result, inference'), constraints') -> Right (result, put inference' >> lift (put constraints'))

-- report whether an action would succeed, wiþout keeping its effects.
probe :: Elaboration a -> Elaboration Bool
probe action = either (const False) (const True) <$> trial action

failure :: String -> Elaboration a
failure = lift . lift . Error.failure

-- rethrow a speculative failure without losing its source location.
raise :: SourceFailure -> Elaboration a
raise = lift . lift . Left

fromEither :: Either String a -> Elaboration a
fromEither = lift . lift . Error.fromString

freshLevel :: Elaboration Level
freshLevel = do
  index <- nextLevel <$> get
  modify' (\state -> state {nextLevel = index + 1})
  pure (LMeta index)

entry :: Int -> Elaboration MetaEntry
entry identity = do
  entries <- metaEntries <$> get
  maybe (failure "unknown term inference hole") pure (Map.lookup identity entries)

resolver :: Elaboration N.MetaResolver
resolver = do
  entries <- metaEntries <$> get
  pure (\identity -> maybe (Left "unknown term inference hole") (Right . metaSolution) (Map.lookup identity entries))

evaluate :: Globals -> K.Context -> Term -> Elaboration N.Value
evaluate globals K.Context {contextValues} term = do
  resolve <- resolver
  fromEither (N.evaluateWith resolve globals contextValues term)

instantiate :: Globals -> N.Closure -> N.Value -> Elaboration N.Value
instantiate globals closure argument = do
  resolve <- resolver
  fromEither (N.instantiateWith resolve globals closure argument)

quote :: Globals -> Int -> N.Value -> Elaboration Term
quote globals depth value = do
  resolve <- resolver
  fromEither (N.quoteWith resolve globals depth value)

-- þe same value wiþ definitions kept by name, for terms þat are evaluated
-- again, such as motives.
quoteFolded :: Globals -> Int -> N.Value -> Elaboration Term
quoteFolded globals depth value = do
  resolve <- resolver
  fromEither (N.quoteFoldedWith resolve globals depth value)

-- þe readable form of a value for goals and messages.
quoteDisplay :: Globals -> Int -> N.Value -> Elaboration Term
quoteDisplay globals depth value = do
  resolve <- resolver
  fromEither (N.quoteDisplayWith resolve globals depth value)

force :: Globals -> N.Value -> Elaboration N.Value
force globals value = do
  resolve <- resolver
  fromEither (N.forceWith resolve globals value)

operations :: Globals -> K.Checking Elaboration
operations globals =
  K.Checking
    { K.failCheck = failure,
      K.liftCheck = fromEither,
      K.evaluateCheck = evaluate globals,
      K.quoteCheck = quote globals,
      K.instantiateCheck = instantiate globals,
      K.forceCheck = force globals,
      K.convertCheck = unify globals,
      K.constrainCheck = kernel . K.oblige,
      K.inferMetaCheck = inferMeta globals
    }

infer :: Globals -> K.Context -> Term -> Elaboration N.Value
infer globals = K.inferTermWith (operations globals) globals

-- definitions are already substituted in semantic contexts. only distinct
-- rigid levels are captured, so aliases neither duplicate nor invent binders.
newMeta :: Globals -> K.Context -> N.Value -> Elaboration (Term, N.Value)
newMeta globals context = newMetaWithout globals context []

-- a hole þat cannot depend on þe given locals, such as a match's result
-- type, which must not mention þe values it matcheþ.
newMetaWithout :: Globals -> K.Context -> [Int] -> N.Value -> Elaboration (Term, N.Value)
newMetaWithout globals K.Context {..} excluded expected = do
  captures <- forM (zip contextValues contextTypes) \(value, ty) -> do
    forced <- force globals value
    pure case forced of
      N.VNeutral (N.NLocal level) | level `notElem` excluded -> Just (level, (forced, ty))
      _ -> Nothing
  let telescope = Map.toAscList (Map.fromList [capture | Just capture <- captures])
      originalDepth = length contextTypes
      levels = map fst telescope
      values = map (fst . snd) telescope
      mapping = Map.fromList (zip levels [0 ..])
  domains <- forM (zip [0 ..] telescope) \(position, (_, (_, ty))) -> do
    domain <- quote globals originalDepth ty
    fromEither (rename originalDepth position (Map.filter (< position) mapping) domain)
  annotation <- quote globals originalDepth expected >>= fromEither . rename originalDepth (length telescope) mapping
  let fullType = foldr (Pi Explicit) annotation domains
  kind <- infer globals K.emptyContext fullType >>= force globals
  case kind of
    N.VSort _ -> pure ()
    _ -> failure "term inference hole requireþ a type"
  identity <- nextMeta <$> get
  modify' (\state -> state {nextMeta = identity + 1, metaEntries = Map.insert identity (MetaEntry (length telescope) fullType Nothing) (metaEntries state)})
  arguments <- traverse (quote globals originalDepth) values
  let term = Meta identity arguments
  pure (term, N.VNeutral (N.NMeta identity values))

inferMeta :: Globals -> K.Context -> Int -> [Term] -> Elaboration N.Value
inferMeta globals context identity arguments = do
  MetaEntry {..} <- entry identity
  unless (length arguments == metaArity) (failure "wrong term inference telescope arity")
  ty <- evaluate globals K.emptyContext metaType
  foldM apply ty arguments
  where
    apply ty argument =
      force globals ty >>= \case
        N.VPi Explicit domain codomain -> do
          actual <- infer globals context argument
          unify globals context actual domain
          value <- evaluate globals context argument
          instantiate globals codomain value
        _ -> failure "invalid term inference telescope"

-- unknown function types are expanded in their own creation telescope. newer
-- caller binders must not enter the domains of these fresh component holes.
ensurePi :: Globals -> K.Context -> Plicity -> N.Value -> Elaboration (N.Value, N.Closure)
ensurePi globals _ plicity value =
  force globals value >>= \case
    N.VPi expected domain codomain
      | plicity == expected -> pure (domain, codomain)
      | otherwise -> failure "implicit and explicit arguments do not match"
    N.VNeutral (N.NMeta identity arguments) -> do
      MetaEntry {..} <- entry identity
      unless (length arguments == metaArity) (failure "wrong term inference telescope arity")
      pattern <- rigidLevels globals arguments
      when (isNothing pattern) (failure "nonpattern function type inference requireþ an annotation")
      fullType <- evaluate globals K.emptyContext metaType
      (context, domains, kind) <- telescope metaArity K.emptyContext fullType
      force globals kind >>= \case
        N.VSort _ -> pure ()
        _ -> failure "unknown function type is not a type"
      domainLevel <- freshLevel
      (domain, domainValue) <- newMeta globals context (N.VSort domainLevel)
      codomainLevel <- freshLevel
      (codomain, _) <- newMeta globals (K.bind context domainValue) (N.VSort codomainLevel)
      let candidate = foldr (Lambda Explicit) (Pi plicity domain codomain) domains
      commit globals identity candidate
      retry globals
      force globals value >>= \case
        N.VPi _ actualDomain actualCodomain -> pure (actualDomain, actualCodomain)
        _ -> failure "function inference did not produce a product"
    _ -> failure "application requireþ a function"
  where
    telescope 0 context kind = pure (context, [], kind)
    telescope remaining context ty =
      force globals ty >>= \case
        N.VPi Explicit domain codomain -> do
          let depth = length (K.contextTypes context)
              variable = N.VNeutral (N.NLocal depth)
          domainTerm <- quote globals depth domain
          rest <- instantiate globals codomain variable
          (current, domains, kind) <- telescope (remaining - 1) (K.bind context domain) rest
          pure (current, domainTerm : domains, kind)
        _ -> failure "invalid term inference telescope"

unify :: Globals -> K.Context -> N.Value -> N.Value -> Elaboration ()
unify globals context left right = do
  solved <- unifyNow globals context left right
  unless solved (postpone context left right)
  retry globals

postpone :: K.Context -> N.Value -> N.Value -> Elaboration ()
postpone context left right = modify' (\state -> state {nextEquation = nextEquation state + 1, pendingEquations = Equation (nextEquation state) context left right : pendingEquations state})

unifyNow :: Globals -> K.Context -> N.Value -> N.Value -> Elaboration Bool
unifyNow globals context left right = do
  actual <- force globals left
  expected <- force globals right
  case (actual, expected) of
    (N.VSort u, N.VSort v) -> do
      unless (u == v) (kernel (K.oblige (LevelEqual u v)))
      pure True
    (N.VPi p domain body, N.VPi q otherDomain otherBody) | p == q -> binders domain body otherDomain otherBody
    (N.VLambda p domain body, N.VLambda q otherDomain otherBody) | p == q -> binders domain body otherDomain otherBody
    -- η: a lambda equaleþ a rigid function applied to þe same input.
    (N.VLambda p domain body, other) | rigid other -> eta p domain body other False
    (other, N.VLambda p domain body) | rigid other -> eta p domain body other True
    -- rigid neutrals are compared by congruence, which recurseþ once per
    -- node; quoting boþ sides at every level would be quadratic. only
    -- applications of one hole are compared whole.
    (N.VNeutral _, N.VNeutral _)
      | Just (left, _) <- metaSpine actual,
        Just (right, _) <- metaSpine expected,
        left == right -> do
          let depth = length (K.contextTypes context)
          a <- quote globals depth actual
          b <- quote globals depth expected
          if a == b then pure True else flexible actual expected
      | otherwise -> flexible actual expected
    _ -> flexible actual expected
  where
    rigid value = case value of
      N.VNeutral _ -> maybe True (const False) (metaSpine value)
      _ -> False
    eta plicity domain body other flipped = do
      blocked <- blockedComputation globals context other
      if blocked
        then pure False
        else do
          let current = K.bind context domain
              variable = N.VNeutral (N.NLocal (length (K.contextTypes context)))
          lambdaSide <- instantiate globals body variable
          resolve <- resolver
          otherSide <- fromEither (N.applyValueWith resolve globals plicity other variable)
          if flipped then unify globals current otherSide lambdaSide else unify globals current lambdaSide otherSide
          pure True
    binders domain body otherDomain otherBody = do
      first <- unifyNow globals context domain otherDomain
      unless first (postpone context domain otherDomain)
      let current = K.bind context domain
          variable = N.VNeutral (N.NLocal (length (K.contextTypes context)))
      a <- instantiate globals body variable
      b <- instantiate globals otherBody variable
      second <- unifyNow globals current a b
      unless second (postpone current a b)
      pure True
    flexible actual expected = case (metaSpine actual, metaSpine expected) of
      (Just (leftId, _), Just (rightId, _)) | leftId == rightId -> pure False
      (Just (identity, arguments), other) -> do
        solved <- solvePattern globals context identity arguments expected
        if solved
          then pure True
          else case other of
            Just (otherIdentity, otherArguments) -> solvePattern globals context otherIdentity otherArguments actual
            Nothing -> abstracted identity arguments expected actual expected
      (Nothing, Just (identity, arguments)) -> do
        solved <- solvePattern globals context identity arguments actual
        if solved then pure True else abstracted identity arguments actual actual expected
      _ -> do
        blocked <- (||) <$> blockedComputation globals context actual <*> blockedComputation globals context expected
        if blocked
          then do
            let depth = length (K.contextTypes context)
            (==) <$> quote globals depth actual <*> quote globals depth expected
          else congruent actual expected
    -- occurrences are abstracted up to universe levels, so þe solved sides
    -- are equated again.
    abstracted identity arguments rigidSide actual expected = do
      solved <- solveAbstraction globals context identity arguments rigidSide
      when solved (unify globals context actual expected)
      pure solved
    congruent (N.VNeutral (N.NLocal left)) (N.VNeutral (N.NLocal right)) | left == right = pure True
    congruent (N.VNeutral (N.NApply p function argument)) (N.VNeutral (N.NApply q otherFunction otherArgument)) | p == q = do
      unify globals context (N.VNeutral function) (N.VNeutral otherFunction)
      unify globals context argument otherArgument
      pure True
    congruent (N.VNeutral (N.NGlobal name levels)) (N.VNeutral (N.NGlobal otherName otherLevels))
      | name == otherName,
        length levels == length otherLevels = do
          mapM_ (kernel . K.oblige) (zipWith LevelEqual levels otherLevels)
          pure True
    congruent (N.VRecordType fields) (N.VRecordType otherFields) | map fst fields == map fst otherFields = do
      mapM_ (uncurry (unify globals context)) (zip (map snd fields) (map snd otherFields))
      pure True
    congruent (N.VRecord fields) (N.VRecord otherFields) | map fst fields == map fst otherFields = do
      mapM_ (uncurry (unify globals context)) (zip (map snd fields) (map snd otherFields))
      pure True
    congruent (N.VNeutral (N.NProject record name)) (N.VNeutral (N.NProject otherRecord otherName)) | name == otherName = do
      unify globals context (N.VNeutral record) (N.VNeutral otherRecord)
      pure True
    congruent (N.VLiteral name value) (N.VLiteral otherName otherValue)
      | name == otherName,
        value == otherValue =
          pure True
    congruent left right = do
      let depth = length (K.contextTypes context)
      a <- quote globals depth left
      b <- quote globals depth right
      display <- displaySymbol <$> get
      failure (renderMismatchWith display depth a b)

metaSpine :: N.Value -> Maybe (Int, [(Plicity, N.Value)])
metaSpine (N.VNeutral neutral)
  | (N.NMeta identity arguments, rest) <- N.neutralSpine neutral =
      Just (identity, [(Explicit, argument) | argument <- arguments] ++ rest)
metaSpine _ = Nothing

-- eliminators, projections, and native computations are not injective. a
-- meta in their inspected input may change the whole head after solving;
-- postpone its equation instead of equating the computation's arguments.
blockedComputation :: Globals -> K.Context -> N.Value -> Elaboration Bool
blockedComputation globals context value =
  force globals value >>= \case
    N.VNeutral neutral -> case N.neutralSpine neutral of
      (N.NProject record _, _) -> changing (N.VNeutral record)
      (N.NGlobal name _, arguments) -> case definitionBody <$> Map.lookup name globals of
        Just (Eliminator family)
          | Just Definition {definitionBody = TypeConstructor InductiveInfo {..}} <- Map.lookup family globals,
            let arity = inductiveParameterCount + 1 + length inductiveConstructorInfo + length inductiveIndexPlicities + 1,
            (_, scrutinee) : _ <- drop (arity - 1) arguments ->
              changing scrutinee
        Just (Host "literal_case") | length arguments >= 6 -> anyM containsMeta (map snd (take 2 (drop 2 arguments)))
        Just (Host key)
          | Just _ <- pureOperation key,
            Just HostBinding {hostSignature = HostSignature {..}} <- findForeignBinding key,
            length arguments >= length hostVariables + length hostArguments ->
              anyM containsMeta (map snd (drop (length hostVariables) arguments))
        _ -> pure False
      _ -> pure False
    _ -> pure False
  where
    changing input = do
      actual <- force globals input
      case metaSpine actual of
        Just _ -> pure True
        _ -> blockedComputation globals context actual
    containsMeta input = holes <$> quote globals (length (K.contextTypes context)) input
    holes Meta {} = True
    holes term = any (holes . snd) (children term)

-- a pattern solution abstracts every distinct rigid argument, including extra
-- applications after the captured telescope. it is checked before committing.
solvePattern :: Globals -> K.Context -> Int -> [(Plicity, N.Value)] -> N.Value -> Elaboration Bool
solvePattern globals context identity arguments right = do
  MetaEntry {..} <- entry identity
  active <- checkingSolutions <$> get
  when (Set.member identity active) (failure "cyclic term inference solution")
  when (maybe False (const True) metaSolution) (failure "term inference solution was already assigned")
  variables <- rigidLevels globals (map snd arguments)
  case variables of
    Just levels -> do
      let depth = length (K.contextTypes context)
          mapping = Map.fromList (zip levels [0 ..])
      body <- quote globals depth right >>= prune globals depth mapping
      cyclic <- occurs identity Set.empty body
      when cyclic (failure "occurs check failed for term inference hole")
      case rename depth (length levels) mapping body of
        Left _ -> pure False
        Right renamed -> do
          ty <- evaluate globals K.emptyContext metaType
          domains <- patternDomains globals depth mapping ty arguments
          case domains of
            Nothing -> pure False
            Just binders -> do
              let candidate = foldr (\(plicity, domain) -> Lambda plicity domain) renamed binders
              settle globals identity candidate
    _ -> pure False

-- a hole of function type applied to inputs þat are not all distinct
-- locals, as a property `?p b` meeting þe goal of `transport`, is solved by
-- abstracting þose inputs from þe oþer side, as lean's `▸` doþ. þe side
-- is searched as written first and as a normal form second, so `first p`
-- is found inside `(first ‥ rest) filter p`. every abstracted input must
-- occur, neiþer side may hold an unsolved hole, and a carrier is left to
-- instance search. a candidate þat þe kernel rejecteþ is no solution.
solveAbstraction :: Globals -> K.Context -> Int -> [(Plicity, N.Value)] -> N.Value -> Elaboration Bool
solveAbstraction globals context identity arguments right = do
  MetaEntry {..} <- entry identity
  carrier <- Set.member identity . carriers <$> get
  let (captured, extra) = splitAt metaArity arguments
  variables <- rigidLevels globals (map snd captured)
  forced <- traverse (force globals . snd) extra
  case variables of
    Just levels
      | not carrier,
        isNothing metaSolution,
        not (null extra) -> do
          -- a local not seen before is a pattern variable; any oþer input is
          -- abstracted.
          let classify (seen, targets) (position, value) = case value of
                N.VNeutral (N.NLocal level) | Map.notMember level seen -> (Map.insert level position seen, targets)
                _ -> (seen, targets ++ [(position, value)])
              (mapping, targets) = foldl classify (Map.fromList (zip levels [0 ..]), []) (zip [metaArity ..] forced)
              arity = metaArity + length extra
          ty <- evaluate globals K.emptyContext metaType
          domains <- telescopeDomains globals arity ty
          case domains of
            Just binders
              | not (null targets),
                map fst (drop metaArity binders) == map fst extra ->
                  candidate mapping targets binders quoteFolded >>= \case
                    True -> pure True
                    False -> candidate mapping targets binders quote
            _ -> pure False
    _ -> pure False
  where
    depth = length (K.contextTypes context)
    candidate mapping targets binders quoting = do
      body <- quoting globals depth right
      abstracted <- traverse (quoting globals depth . snd) targets
      let count = length targets
          (abstraction, found) = abstractTerms abstracted body
          extended = Map.union mapping (Map.fromList [(depth + offset, position) | (offset, (position, _)) <- zip [0 ..] targets])
      case rename (depth + count) (length binders) extended abstraction of
        Right renamed
          | and found,
            null (concatMap termHoles (body : abstracted)) ->
              speculate (settle globals identity (foldr (uncurry Lambda) renamed binders)) >>= \case
                Just (True, keep) -> True <$ keep
                _ -> pure False
        _ -> pure False

-- þe first domains of a closed type, each over þe binders before it.
telescopeDomains :: Globals -> Int -> N.Value -> Elaboration (Maybe [(Plicity, Term)])
telescopeDomains globals count = go 0
  where
    go position ty
      | position == count = pure (Just [])
      | otherwise =
          force globals ty >>= \case
            N.VPi plicity domain codomain -> do
              domainTerm <- quoteFolded globals position domain
              rest <- instantiate globals codomain (N.VNeutral (N.NLocal position)) >>= go (position + 1)
              pure (((plicity, domainTerm) :) <$> rest)
            _ -> pure Nothing

-- a hole in a solution may capture a local þat þe solved hole cannot see,
-- as `?f x` in `?t := ?f x` when `?t` haþ no `x`. if þe hole's type doþ
-- not need þat input, it is replaced by a fresh hole wiþout it, and þe
-- solution is quoted again. þe body is quoted at `depth`; `mapping` holdeþ
-- þe levels þe solution may mention.
prune :: Globals -> Int -> Map.Map Int Int -> Term -> Elaboration Term
prune globals depth mapping body = case [(target, keeps) | (target, keeps) <- candidates 0 body, not (and keeps)] of
  [] -> pure body
  (target, keeps) : _ ->
    narrow target keeps >>= \case
      True -> requote
      False -> pure body
  where
    -- holes applied only to locals, each wiþ which of its inputs may stay.
    candidates bound = \case
      Meta target arguments
        | Just keeps <- traverse (allowed bound) arguments -> [(target, keeps)]
      term -> concat [candidates (bound + binders) child | (binders, child) <- children term]
    allowed bound = \case
      Local index
        | index < bound -> Just True
        | otherwise -> Just (Map.member (depth - 1 - (index - bound)) mapping)
      _ -> Nothing
    requote = do
      resolve <- resolver
      let environment = map (N.VNeutral . N.NLocal) (reverse [0 .. depth - 1])
      value <- fromEither (N.evaluateWith resolve globals environment body)
      quote globals depth value >>= prune globals depth mapping
    narrow target keeps = do
      MetaEntry {metaArity, metaType, metaSolution} <- entry target
      case (metaSolution, splitTelescope metaArity metaType) of
        (Nothing, Just (domains, result))
          | Just kept <- strengthened keeps domains result -> do
              let (keptDomains, keptResult) = kept
                  keptType = foldr (Pi Explicit) keptResult keptDomains
              fresh <- nextMeta <$> get
              modify' (\state -> state {nextMeta = fresh + 1, metaEntries = Map.insert fresh (MetaEntry (length keptDomains) keptType Nothing) (metaEntries state)})
              let arity = length domains
                  arguments = [Local (arity - 1 - position) | (position, True) <- zip [0 ..] keeps]
              commit globals target (foldr (Lambda Explicit) (Meta fresh arguments) domains)
              pure True
        _ -> pure False

-- þe first `arity` domains of a hole's type and þe type beneaþ þem.
splitTelescope :: Int -> Term -> Maybe ([Term], Term)
splitTelescope 0 ty = Just ([], ty)
splitTelescope arity (Pi _ domain codomain) = (\(domains, result) -> (domain : domains, result)) <$> splitTelescope (arity - 1) codomain
splitTelescope _ _ = Nothing

-- a telescope wiþout þe inputs not kept, if noþing kept mentioneþ þem.
strengthened :: [Bool] -> [Term] -> Term -> Maybe ([Term], Term)
strengthened keeps domains result = do
  kept <- sequence [dropInputs (reverse (take position keeps)) domain | (position, (True, domain)) <- zip [0 ..] (zip keeps domains)]
  (kept,) <$> dropInputs (reverse keeps) result
  where
    -- `flags` mark þe enclosing inputs, innermost first.
    dropInputs flags = go 0
      where
        go bound = \case
          Local index
            | index < bound -> Just (Local index)
            | otherwise ->
                let outer = index - bound
                 in if flags !! outer then Just (Local (bound + length (filter id (take outer flags)))) else Nothing
          term -> mapChildren (\binders -> go (bound + binders)) term

rigidLevels :: Globals -> [N.Value] -> Elaboration (Maybe [Int])
rigidLevels globals arguments = do
  levels <- traverse (fmap rigid . force globals) arguments
  pure case sequence levels of
    Just variables | length variables == Set.size (Set.fromList variables) -> Just variables
    _ -> Nothing
  where
    rigid (N.VNeutral (N.NLocal level)) = Just level
    rigid _ = Nothing

commit :: Globals -> Int -> Term -> Elaboration ()
commit globals identity candidate =
  assign globals identity candidate >>= \case
    Right () -> pure ()
    Left (_, Just problem) -> raise problem
    Left (_, Nothing) -> failure "inference solution typing requireþ an annotation"

-- a candidate whose typing waiteþ on anoþer hole, such as a dictionary
-- projection before instance search, is not assigned. its check is undone
-- and þe caller keepeþ þe equation postponed until þat hole is solved.
-- þe same candidate is not checked again until one of þose holes is solved.
settle :: Globals -> Int -> Term -> Elaboration Bool
settle globals identity candidate = do
  waiting <- Map.lookup identity . unsettled <$> get
  stuck <- case waiting of
    Just (previous, blockers) | previous == candidate -> allM (fmap (isNothing . metaSolution) . entry) (Set.toList blockers)
    _ -> pure False
  if stuck
    then pure False
    else
      trial (assign globals identity candidate) >>= \case
        Left problem -> raise problem
        Right (Right (), keep) -> True <$ keep
        Right (Left (blockers, _), _) -> do
          modify' (\state -> state {unsettled = Map.insert identity (candidate, blockers) (unsettled state)})
          pure False
  where
    allM predicate = fmap and . traverse predicate

-- assigneþ þe candidate if checking it leaveþ no new postponed equation.
-- oþerwise it returneþ þe unsolved holes in þose equations. a kernel failure
-- is returned wiþ þe candidate's unsolved holes, since solving þem may
-- give an application its function type; wiþout any, it is raised.
assign :: Globals -> Int -> Term -> Elaboration (Either (Set.Set Int, Maybe SourceFailure) ())
assign globals identity candidate = do
  MetaEntry {metaType, metaSolution = solution} <- entry identity
  active <- checkingSolutions <$> get
  when (Set.member identity active) (failure "cyclic term inference solution")
  unless (isNothing solution) (failure "term inference solution was already assigned")
  cyclic <- occurs identity Set.empty candidate
  when cyclic (failure "occurs check failed for term inference hole")
  firstNewEquation <- nextEquation <$> get
  modify' (\state -> state {checkingSolutions = Set.insert identity (checkingSolutions state)})
  trial (K.checkTermWith (operations globals) globals K.emptyContext candidate metaType) >>= \case
    Left problem -> do
      blockers <- (<>) <$> openHoles candidate <*> openHoles metaType
      if Set.null blockers then raise problem else pure (Left (blockers, Just problem))
    Right ((), keep) -> do
      keep
      pending <- pendingEquations <$> get
      case [equation | equation@(Equation number _ _ _) <- pending, number >= firstNewEquation] of
        new@(_ : _) -> Left . (,Nothing) . Set.unions <$> traverse equationHoles new
        [] -> do
          latest <- entry identity
          unless (isNothing (metaSolution latest)) (failure "term inference solution changed during checking")
          modify' (\state -> state {metaEntries = Map.insert identity (latest {metaSolution = Just candidate}) (metaEntries state), checkingSolutions = Set.delete identity (checkingSolutions state), solutionVersion = solutionVersion state + 1})
          pure (Right ())
  where
    equationHoles (Equation _ context left right) = do
      let depth = length (K.contextTypes context)
      (<>) <$> (quote globals depth left >>= openHoles) <*> (quote globals depth right >>= openHoles)

-- þe holes in a term þat are still unsolved.
openHoles :: Term -> Elaboration (Set.Set Int)
openHoles term = Set.fromList <$> filterM (fmap (isNothing . metaSolution) . entry) (termHoles term)

-- þe holes a term mentioneþ. a quoted term mentioneþ only unsolved ones.
termHoles :: Term -> [Int]
termHoles = \case
  Meta target arguments -> target : concatMap termHoles arguments
  other -> concatMap (termHoles . snd) (children other)

patternDomains :: Globals -> Int -> Map.Map Int Int -> N.Value -> [(Plicity, N.Value)] -> Elaboration (Maybe [(Plicity, Term)])
patternDomains globals depth mapping = go 0
  where
    go _ _ [] = pure (Just [])
    go position ty ((plicity, argument) : rest) =
      force globals ty >>= \case
        N.VPi expected domain codomain | plicity == expected -> do
          domainTerm <- quote globals depth domain
          case rename depth position (Map.filter (< position) mapping) domainTerm of
            Left _ -> pure Nothing
            Right renamed -> do
              result <- instantiate globals codomain argument
              remaining <- go (position + 1) result rest
              pure (((plicity, renamed) :) <$> remaining)
        _ -> failure "term inference pattern differeþ from its type"

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
          else do
            solution <- metaSolution <$> entry identity
            maybe (pure False) (occurs target (Set.insert identity visited)) solution
  term -> anyM (occurs target visited . snd) (children term)

anyM :: (a -> Elaboration Bool) -> [a] -> Elaboration Bool
anyM _ [] = pure False
anyM predicate (value : rest) = do
  found <- predicate value
  if found then pure True else anyM predicate rest

-- quoted terms use indices, but inversion maps their original rigid levels.
-- binders introduced inside the term retain their local indices unchanged.
rename :: Int -> Int -> Map.Map Int Int -> Term -> Either String Term
rename sourceDepth targetDepth mapping = go 0
  where
    go bound = \case
      Local index
        | index < 0 -> Left "negative inference variable index"
        | index < bound -> pure (Local index)
        | otherwise ->
            let level = sourceDepth - 1 - (index - bound)
             in case Map.lookup level mapping of
                  Just target -> pure (Local (bound + targetDepth - 1 - target))
                  Nothing -> Left "term inference solution would escape its scope"
      term -> mapChildren (\binders -> go (bound + binders)) term

-- an equation is postponed only after an attempt, and its outcome changeþ
-- only when a hole is solved. so a retry wiþout a new solution is skipped.
retry :: Globals -> Elaboration ()
retry globals = do
  Inference {..} <- get
  unless (retryingEquations || not (Set.null checkingSolutions) || retriedVersion == solutionVersion) do
    modify' (\state -> state {retryingEquations = True})
    loop
    modify' (\state -> state {retryingEquations = False})
  where
    loop = do
      Inference {pendingEquations, solutionVersion = before} <- get
      modify' (\state -> state {pendingEquations = []})
      mapM_ attempt pendingEquations
      after <- solutionVersion <$> get
      if after /= before then loop else modify' (\state -> state {retriedVersion = after})
    attempt (Equation _ context left right) = do
      solved <- unifyNow globals context left right
      unless solved (postpone context left right)

-- a last resort for a stuck equation between an applied hole and a rigid
-- application: `?f a = g b` becomeþ `?f = g` and `a = b`, as in agda and
-- lean. it may miss a non-first-order solution, so it runs only when
-- noþing else can progress. þe result reporteþ whether an equation was split.
approximate :: Globals -> Elaboration Bool
approximate = approximateWith False

-- like 'approximate', and also between two applied holes. let
-- generalisation useþ it last, as hindley-milner unification of type
-- applications doþ.
approximateFlexible :: Globals -> Elaboration Bool
approximateFlexible = approximateWith True

approximateWith :: Bool -> Globals -> Elaboration Bool
approximateWith both globals = do
  Inference {pendingEquations} <- get
  split pendingEquations []
  where
    split [] _ = pure False
    split (equation@(Equation _ context left right) : rest) kept = do
      actual <- force globals left
      expected <- force globals right
      blocked <- (||) <$> blockedComputation globals context actual <*> blockedComputation globals context expected
      case (blocked, applied actual, applied expected) of
        (False, Just (p, function, argument), Just (q, otherFunction, otherArgument))
          | p == q,
            both || flexible actual /= flexible expected -> do
              Inference {solutionVersion = before, pendingEquations = waiting} <- get
              modify' (\state -> state {pendingEquations = reverse kept ++ rest})
              unify globals context function otherFunction
              unify globals context argument otherArgument
              -- a split þat only postponeþ its parts is no progress, so a
              -- caller þat retrieþ on progress stopeþ.
              Inference {solutionVersion = after, pendingEquations = now} <- get
              pure (after > before || length now < length waiting)
        _ -> split rest (equation : kept)
    applied = \case
      N.VNeutral (N.NApply plicity function argument) -> Just (plicity, N.VNeutral function, argument)
      _ -> Nothing
    flexible value = maybe False (const True) (metaSpine value)

-- holes still open after every postponed equation is retried, oldest first,
-- wiþ þe type each hole haþ beneaþ its telescope.
unsolved :: Globals -> Elaboration [(Int, Term)]
unsolved globals = do
  retry globals
  Inference {metaEntries} <- get
  pure [(identity, beneath metaArity metaType) | (identity, MetaEntry {..}) <- Map.toAscList metaEntries, isNothing metaSolution]
  where
    beneath 0 ty = ty
    beneath remaining (Pi _ _ codomain) = beneath (remaining - 1 :: Int) codomain
    beneath _ ty = ty

-- assign a hole a value þat ignoreþ its telescope, as let generalisation doþ
-- wiþ a constant standing for a new input.
assignConstant :: Globals -> Int -> Term -> Elaboration ()
assignConstant globals identity value = do
  MetaEntry {metaArity, metaType} <- entry identity
  let binders = take metaArity (fst (termTelescope metaType))
  commit globals identity (foldr (uncurry Lambda) value binders)

-- the boundary rejecteþ unresolved holes even when a discarded result no
-- longer mentioneþ them. no arbitrary inhabitants or defaults are inserted.
zonk :: Globals -> Term -> Elaboration Term
zonk globals term = do
  retry globals
  Inference {..} <- get
  unless (null pendingEquations) (failure "unsolved inference equation")
  when (any (isNothing . metaSolution) (Map.elems metaEntries)) (failure "unsolved implicit argument or lambda domain")
  expand 0 term
  where
    expand depth = \case
      meta@Meta {} -> do
        resolve <- resolver
        let environment = map (N.VNeutral . N.NLocal) (reverse [0 .. depth - 1])
        value <- fromEither (N.evaluateWith resolve globals environment meta)
        quote globals depth value
      term -> mapChildren (\binders -> expand (depth + binders)) term
