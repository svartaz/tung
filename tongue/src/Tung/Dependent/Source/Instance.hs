-- | class dictionary goals and instance selection. candidates run in isolated
-- elaboration trials; only the chosen dictionary committeþ its inference state.
-- search useþ core types and class metadata, never source syntax.
module Tung.Dependent.Source.Instance
  ( implicitArgument,
    classFamily,
    solveInstances,
    solveDeterminedInstances,
    settleAnnotation,
    resolveInstance,
    sameInstance,
  )
where

import Control.Monad (filterM, foldM, forM_, when)
import Data.Functor ((<&>))
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Ord (Down (..))
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Render (renderTermWith)
import Tung.Dependent.Source.Environment
import Tung.Dependent.Syntax
import Tung.Identity (SymbolId)
import Tung.Token (SourceFailure (..))

type Elaboration = E.Elaboration

-- search for a complete goal may use registered instances. an unknown goal
-- first useþ only local requirements and the parent dictionaries they project.
data SearchMode = LocalRequirements | AllInstances
  deriving stock (Eq)

-- equivalent patterns are rejected before a dictionary is registered.
sameInstance :: K.Environment -> SymbolId -> SymbolId -> Bool
sameInstance environment left right = case (instancePattern environment left, instancePattern environment right) of
  (Just first, Just second) -> instanceOf first second && instanceOf second first
  _ -> False

-- a dictionary's class arguments, under þe count of its own binders.
instancePattern :: K.Environment -> SymbolId -> Maybe (Int, [Term])
instancePattern environment symbol = do
  Definition {definitionType} <- Map.lookup symbol (globals environment)
  let (binders, result) = termTelescope definitionType
  pure (length binders, map snd (snd (termSpine result)))

-- `broad` matcheþ `narrow` when its own binders can stand for subterms.
instanceOf :: (Int, [Term]) -> (Int, [Term]) -> Bool
instanceOf (broadBound, broad) (narrowBound, narrow) = maybe False (const True) (foldM go Map.empty (zip broad narrow))
  where
    go solution (Local index, term)
      | index < broadBound = case Map.lookup index solution of
          Nothing -> Just (Map.insert index term solution)
          Just existing -> if existing == term then Just solution else Nothing
    go solution (Local index, Local other)
      | index - broadBound == other - narrowBound = Just solution
    go solution (Apply plicity function argument, Apply plicity' function' argument')
      | plicity == plicity' = go solution (function, function') >>= \next -> go next (argument, argument')
    go solution (Global symbol _, Global symbol' _)
      | symbol == symbol' = Just solution
    go solution (left, right)
      | left == right = Just solution
    go _ _ = Nothing

-- an implicit input whose type applieþ a class becomeþ an instance goal.
implicitArgument :: Names -> K.Context -> N.Value -> Elaboration (Term, N.Value)
implicitArgument names context domain = do
  hole@(_, holeValue) <- E.newMeta context domain
  family <- classFamily names domain
  case family of
    Just _ -> do
      E.markCarriers context domain
      E.addInstanceGoal (E.InstanceGoal holeValue context domain)
    Nothing -> pure ()
  pure hole

classFamily :: Names -> N.Value -> Elaboration (Maybe SymbolId)
classFamily names ty =
  E.force ty >>= \case
    N.VNeutral neutral
      | (N.NGlobal family _, _) <- N.neutralSpine neutral,
        Map.member family (nameClasses names) ->
          pure (Just family)
    _ -> pure Nothing

-- goals are solved after the declaration's ordinary unification, so their
-- types are as specific as the program makeþ them.
-- a goal waiteþ while þe head of an input parameter of its flock is still
-- unknown, as rocq's `!` mode doþ; output parameters (`* out`) are found by
-- þe search. a waiting goal may still be fixed by a local requirement or by
-- splitting a stuck equation; no candidate bizen fixeþ an unknown input.
solveInstances :: K.Environment -> Names -> Elaboration ()
solveInstances environment names = E.repeatProgress do
  (ready, waiting) <- takeReadyGoals names
  mapM_ (search AllInstances) ready
  still <- catMaybes <$> traverse (\goal -> E.speculate (search LocalRequirements goal) >>= maybe (pure (Just goal)) (\(_, commit) -> commit >> pure Nothing)) waiting
  if null ready && length still == length waiting
    then
      E.approximate >>= \case
        True -> mapM_ E.addInstanceGoal still >> pure True
        False -> fallback still
    else mapM_ E.addInstanceGoal still >> pure True
  where
    search = searchGoal environment names
    -- a goal still stuck on an unknown input trieþ its flock's fallback
    -- bizens; þe first þat fiteþ fixeþ þe input.
    fallback = \case
      [] -> pure False
      goal : rest ->
        E.speculate (searchFallback environment names goal) >>= \case
          Just (_, commit) -> commit >> mapM_ E.addInstanceGoal rest >> pure True
          Nothing -> do
            more <- fallback rest
            E.addInstanceGoal goal
            pure more

-- goals whose class argument is known are solved now, so a computed match
-- scrutinee can be compared wiþ its goal. oþer goals keep waiting.
solveDeterminedInstances :: K.Environment -> Names -> Elaboration ()
solveDeterminedInstances environment names = E.repeatProgress do
  (ready, waiting) <- takeReadyGoals names
  mapM_ E.addInstanceGoal waiting
  mapM_ (searchGoal environment names AllInstances) ready
  pure (not (null ready))

-- a declaration's annotation is closed, so its dictionaries are chosen before
-- its body is checked. known goals are solved, and a stuck equation of þe
-- annotation is split by first-order approximation, first against a rigid
-- application and þen between two applied holes, as nested flock calls
-- such as `(l filter p) filter p` need. þe unique-instance fallback still
-- waiteþ for þe whole declaration.
settleAnnotation :: K.Environment -> Names -> Elaboration ()
settleAnnotation environment names = E.repeatProgress do
  solveDeterminedInstances environment names
  rigid <- E.approximate
  if rigid then pure True else E.approximateFlexible

-- the same ordered partition serveþ body and annotation phases.
takeReadyGoals :: Names -> Elaboration ([E.InstanceGoal], [E.InstanceGoal])
takeReadyGoals names = E.takeInstanceGoals >>= partitionM (determined names . E.goalType)

searchGoal :: K.Environment -> Names -> SearchMode -> E.InstanceGoal -> Elaboration ()
searchGoal environment names mode E.InstanceGoal {..} = do
  hole <- E.force goalHole
  case hole of
    N.VNeutral neutral | (N.NMeta _ _, _) <- N.neutralSpine neutral -> do
      term <- searchInstance environment names mode [] goalContext goalType
      value <- E.evaluate goalContext term
      E.unify goalContext goalHole value
    _ -> pure ()

-- þe flock's fallback bizens, by priority, for a goal wiþ unknown inputs.
searchFallback :: K.Environment -> Names -> E.InstanceGoal -> Elaboration ()
searchFallback environment names E.InstanceGoal {..} = do
  family <- classFamily names goalType >>= maybe (E.failure "instance goal is not a flock") pure
  let fallbacks = maybe [] classFallbacks (Map.lookup family (nameClasses names))
  when (null fallbacks) (E.failure "no fallback bizen")
  term <- searchInstanceAmong (Just fallbacks) environment names AllInstances [] goalContext goalType
  value <- E.evaluate goalContext term
  E.unify goalContext goalHole value

partitionM :: (Monad m) => (a -> m Bool) -> [a] -> m ([a], [a])
partitionM predicate = foldr (\goal rest -> do (yes, no) <- rest; keep <- predicate goal; pure (if keep then (goal : yes, no) else (yes, goal : no))) (pure ([], []))

-- a goal is ready when every input parameter of its flock haþ a known head.
determined :: Names -> N.Value -> Elaboration Bool
determined names goal =
  E.force goal >>= \case
    N.VNeutral neutral
      | (N.NGlobal family _, arguments) <- N.neutralSpine neutral -> do
          let outputs = maybe [] classOutputs (Map.lookup family (nameClasses names))
              inputs = [argument | (index, (_, argument)) <- zip [0 :: Int ..] arguments, not (or (take 1 (drop index outputs)))]
          and <$> traverse known inputs
    _ -> pure True
  where
    known argument =
      E.force argument <&> \case
        N.VNeutral neutral | (N.NMeta _ _, _) <- N.neutralSpine neutral -> False
        _ -> True

-- þe first local requirement of þe goal's class þat unifieþ wiþ it.
localInstance :: Names -> K.Context -> SymbolId -> N.Value -> Elaboration (Maybe Term)
localInstance names context family goal = do
  let localTypes = zip [0 ..] (K.contextTypes context)
  locals <- filterM (\(_, ty) -> (== Just family) <$> classFamily names ty) localTypes
  firstJust [E.attempt (E.unify context ty goal >> pure (Local index)) | (index, ty) <- locals]

-- local requirements are tried first, then registered instances, then inherited
-- instances. one registered match þat refineþ every oþer winneþ; þe first matching
-- inherited instance is used. a candidate's own requirements are solved
-- recursively.
-- a goal þat repeateþ one of its own ancestors cannot be solved by þat path.
-- a local search useþ only local requirements and þe parents þey project, as
-- for a goal whose type is still unknown.
resolveInstance :: K.Environment -> Names -> K.Context -> N.Value -> Elaboration Term
resolveInstance environment names = searchInstance environment names AllInstances []

searchInstance :: K.Environment -> Names -> SearchMode -> [Term] -> K.Context -> N.Value -> Elaboration Term
searchInstance = searchInstanceAmong Nothing

-- a search restricted to þe given bizens, such as a flock's fallbacks.
searchInstanceAmong :: Maybe [SymbolId] -> K.Environment -> Names -> SearchMode -> [Term] -> K.Context -> N.Value -> Elaboration Term
searchInstanceAmong restriction environment names mode ancestors context goal = do
  when (length ancestors > 16) (E.failure "instance search is too deep")
  current <- E.quote (length (K.contextTypes context)) goal
  -- global universe instantiations do not distinguish repeated goals;
  -- sort arguments remain significant to the kernel's constraints.
  let key = eraseGlobalLevels current
  when (key `elem` ancestors) (E.failure "cyclic instance search")
  family <- classFamily names goal >>= maybe (E.failure "instance goal is not a flock") pure
  localMatch <- localInstance names context family goal
  case localMatch of
    Just term -> pure term
    Nothing -> do
      let classInfo = Map.lookup family (nameClasses names)
      wanted <- goalHeads goal
      let path = key : ancestors
      -- candidates are tried by priority, þe latest first among equals, as
      -- lean doþ; þe first þat succeedeþ is chosen, wiþ its requirements.
      (direct, failures) <-
        if mode == LocalRequirements
          then pure ([], [])
          else firstSuccess path (filter (\symbol -> fits wanted symbol && maybe True (symbol `elem`) restriction) (maybe [] ordered classInfo))
      -- instances are unique per type, so every parent projection reacheþ þe
      -- same dictionary; a diamond of parents is not ambiguous.
      inherited <-
        if null direct && restriction == Nothing
          then do
            localFamilies <- catMaybes <$> traverse (classFamily names) (K.contextTypes context)
            firstMatching path (filter (viable localFamilies [family] wanted . Just) (maybe [] classInherited classInfo))
          else pure []
      case direct ++ inherited of
        (term, commit) : _ -> commit >> pure term
        [] -> do
          localRequirements <- filterM (fmap (/= Nothing) . classFamily names) (K.contextTypes context)
          available <- traverse (E.quote (length (K.contextTypes context))) localRequirements
          let rendered = renderTermWith (displayName names) []
              detail = ["available requirement '" ++ rendered requirement ++ "'" | requirement <- available] ++ take 1 failures
          E.failure ("no bizen of flock '" ++ displayName names family ++ "' matcheþ goal '" ++ rendered current ++ "'" ++ concatMap ("; " ++) detail)
  where
    ordered ClassInfo {classInstances, classPriorities} =
      map snd (sortOn fst [((Down (Map.findWithDefault defaultPriority symbol classPriorities), Down age), symbol) | (age, symbol) <- zip [0 :: Int ..] classInstances])
    firstSuccess path = \case
      [] -> pure ([], [])
      symbol : rest ->
        E.trial (candidate path symbol) >>= \case
          Right found -> pure ([found], [])
          Left failure -> fmap (failureMessage failure :) <$> firstSuccess path rest
    firstMatching path = \case
      [] -> pure []
      symbol : rest -> E.speculate (candidate path symbol) >>= maybe (firstMatching path rest) (pure . pure)
    -- a cheap filter: an instance whose class arguments start wiþ a different
    -- family can never match. any oþer argument is compared by unification.
    rigid symbol = case definitionBody <$> Map.lookup symbol (globals environment) of
      Just (TypeConstructor _) -> True
      Just (Host _ _) -> True
      _ -> False
    goalHeads value =
      E.force value >>= \case
        N.VNeutral neutral -> traverse (argumentHead . snd) (snd (N.neutralSpine neutral))
        _ -> pure []
    argumentHead value =
      E.force value <&> \case
        N.VNeutral neutral | (N.NGlobal symbol _, _) <- N.neutralSpine neutral, rigid symbol -> Just symbol
        _ -> Nothing
    fits wanted symbol = case Map.lookup symbol (globals environment) of
      Just Definition {definitionType} -> and (zipWith agree wanted (resultHeads definitionType))
      Nothing -> True
    agree (Just left) (Just right) = left == right
    agree _ _ = True
    -- an inherited instance projecteþ from a child class's dictionary. when
    -- þe child passeþ its own parameters unchanged, þe child needeþ a local
    -- requirement or an instance wiþ þe same heads, direct or inherited in turn;
    -- oþerwise it may match.
    viable localFamilies visited wanted = \case
      Nothing -> True
      Just symbol -> case childClass symbol of
        Nothing -> True
        Just child
          | child `elem` localFamilies -> True
          | child `elem` visited -> False
          | otherwise -> case Map.lookup child (nameClasses names) of
              Nothing -> False
              Just ClassInfo {classInstances, classInherited} ->
                (mode == AllInstances && any (fits wanted) classInstances) || any (viable localFamilies (child : visited) wanted . Just) classInherited
    childClass symbol = do
      Definition {definitionType} <- Map.lookup symbol (globals environment)
      (dictionary, result) <- lastBinder definitionType
      (Global child _, childArguments) <- pure (termSpine dictionary)
      (_, parentArguments) <- pure (termSpine result)
      if map (shift . snd) childArguments == map snd parentArguments then Just child else Nothing
    lastBinder = \case
      Pi Implicit _ result@(Pi {}) -> lastBinder result
      Pi Implicit domain result -> Just (domain, result)
      _ -> Nothing
    shift = \case
      Local index -> Local (index + 1)
      term -> term
    resultHeads term = [termHead argument | (_, argument) <- snd (termSpine (snd (termTelescope term)))]
    termHead term = case fst (termSpine term) of
      Global symbol _ | rigid symbol -> Just symbol
      _ -> Nothing
    candidate path symbol = do
      levels <- E.freshUniverses symbol
      let headTerm = Global symbol levels
      headType <- E.infer context headTerm
      (term, ty, pending) <- instantiate headTerm headType []
      E.unify context ty goal
      forM_ pending \(holeValue, domain) ->
        determined names domain >>= \case
          True -> do
            sub <- searchInstance environment names mode path context domain
            value <- E.evaluate context sub
            E.unify context holeValue value
          False -> E.addInstanceGoal (E.InstanceGoal holeValue context domain)
      pure term
    instantiate term ty pending =
      E.force ty >>= \case
        N.VPi Implicit domain codomain -> do
          (argument, value) <- E.newMeta context domain
          isClass <- classFamily names domain
          next <- E.instantiate codomain value
          instantiate (Apply Implicit term argument) next ([(value, domain) | Just _ <- [isClass]] ++ pending)
        other -> pure (term, other, reverse pending)

firstJust :: [Elaboration (Maybe a)] -> Elaboration (Maybe a)
firstJust [] = pure Nothing
firstJust (action : rest) = action >>= maybe (firstJust rest) (pure . Just)
