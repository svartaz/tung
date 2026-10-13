-- | index unification: an indexed split refineth each branch by unifying
-- constructor indices with the scrutinee's.
module Tung.Dependent.Source.Pattern.Index
  ( indexPattern,
    patternLeaves,
    ConstructorFit (..),
    constructorFit,
    constructorFits,
    constructorPossible,
    indexBindings,
    matchedIndexBindings,
    constructorView,
    unifiedMotive,
    allM,
    columnValue,
    constructorValue,
    abstractLevels,
  )
where

import Control.Monad (foldM, forM, unless, zipWithM)
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity (..))
import Data.List (elemIndex)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Pattern.Common
import Tung.Dependent.Source.Scope
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core
import Tung.Identity (SymbolId (..))

type Elaboration = E.Elaboration

indexPattern :: K.Environment -> N.Value -> Elaboration (Maybe IndexPattern)
indexPattern environment value =
  E.force value >>= \case
    N.VNeutral (N.NLocal level) -> pure (Just (IndexVariable level))
    forced ->
      constructorView environment forced >>= \case
        Just (constructor, fields) -> fmap (IndexConstructor constructor) . sequence <$> traverse (indexPattern environment) fields
        Nothing -> pure Nothing

patternLeaves :: IndexPattern -> [Int]
patternLeaves = \case
  IndexVariable level -> [level]
  IndexConstructor _ subpatterns -> concatMap patternLeaves subpatterns

-- a constructor application and its fields; a number literal readeth as its
-- outer constructor.
constructorView :: K.Environment -> N.Value -> Elaboration (Maybe (SymbolId, [N.Value]))
constructorView environment value = do
  forced <- E.force value
  pure $ case N.constructorForm forced of
    N.VNeutral neutral
      | (N.NGlobal constructor _, arguments) <- N.neutralSpine neutral,
        Just Definition {definitionBody = DataConstructor owner _} <- Map.lookup constructor (globals environment),
        Just Definition {definitionBody = TypeConstructor info} <- Map.lookup owner (globals environment) ->
          Just (constructor, map snd (drop (inductiveParameterCount info) arguments))
    _ -> Nothing

-- the result indices of a constructor applied to the family parameters and
-- the given fields.
constructorIndices :: K.Environment -> Split -> SymbolId -> [N.Value] -> Elaboration [N.Value]
constructorIndices environment Split {..} constructor fieldValues = do
  Definition {definitionType} <- maybe (E.failure "missing constructor") pure (Map.lookup constructor (globals environment))
  term <- E.fromEither (instantiateLevels splitLevels definitionType)
  ty <- E.evaluate (K.Context [] []) term
  result <-
    foldM
      ( \current value ->
          E.force current >>= \case
            N.VPi _ _ codomain -> E.instantiate codomain value
            _ -> E.failure "invalid constructor ilk"
      )
      ty
      (splitParameters ++ fieldValues)
  E.force result >>= \case
    N.VNeutral neutral -> pure (map snd (drop (inductiveParameterCount splitInfo) (snd (N.neutralSpine neutral))))
    _ -> E.failure "invalid constructor result"

-- forced fields are promises to split through ordinary eliminators, never
-- assignments to the generic constructor method's local variables.
data ConstructorFit
  = IndexFits (Map.Map Int IndexPattern)
  | IndexImpossible (Map.Map Int IndexPattern)
  | IndexUndecidable

data IndexConstraint
  = ForcedField Int IndexPattern
  | IndexConflict
  | UnknownIndex

constructorFit :: K.Environment -> Split -> [IndexPattern] -> SymbolId -> [N.Value] -> Elaboration ConstructorFit
constructorFit environment split indexPatterns constructor fieldValues = do
  values <- traverse E.force fieldValues
  let fields = Set.fromList [level | N.VNeutral (N.NLocal level) <- values]
  indices <- constructorIndices environment split constructor fieldValues
  constraints <- concat <$> zipWithM (fits fields) indexPatterns indices
  let (forced, inconsistent) = foldl' constrain (Map.empty, False) constraints
  pure $
    if inconsistent || any conflict constraints
      then IndexImpossible forced
      else
        if any unknown constraints
          then IndexUndecidable
          else IndexFits forced
  where
    fits _ (IndexVariable _) _ = pure []
    fits fields pattern@(IndexConstructor expected subpatterns) value =
      E.force value >>= \case
        N.VNeutral (N.NLocal level) | level `Set.member` fields -> pure [ForcedField level pattern]
        forced ->
          constructorView environment forced >>= \case
            Nothing -> pure [UnknownIndex]
            Just (actual, values)
              | actual /= expected -> pure [IndexConflict]
              | otherwise -> concat <$> zipWithM (fits fields) subpatterns values
    conflict IndexConflict = True
    conflict _ = False
    unknown UnknownIndex = True
    unknown _ = False
    -- an impossible method still needeth these splits so its motive can
    -- compute to the trivial type. on conflict the first shape sufficeth.
    constrain (forced, inconsistent) (ForcedField level pattern) =
      case maybe (Just pattern) (`intersectIndices` pattern) (Map.lookup level forced) of
        Just combined -> (Map.insert level combined forced, inconsistent)
        Nothing -> (forced, True)
    constrain state _ = state

-- written index variables impose no shape. repeated requirements on one
-- constructor field must agree before any branch is generated.
intersectIndices :: IndexPattern -> IndexPattern -> Maybe IndexPattern
intersectIndices (IndexVariable _) right = Just right
intersectIndices left (IndexVariable _) = Just left
intersectIndices (IndexConstructor left fields) (IndexConstructor right others)
  | left == right && length fields == length others = IndexConstructor left <$> zipWithM intersectIndices fields others
  | otherwise = Nothing

-- a forced field still needeth elimination before the old yes/no query can
-- answer; callers compiling methods use 'constructorFit' instead.
constructorFits :: K.Environment -> Split -> [IndexPattern] -> SymbolId -> [N.Value] -> Elaboration (Maybe Bool)
constructorFits environment split indexPatterns constructor fieldValues =
  constructorFit environment split indexPatterns constructor fieldValues <&> \case
    IndexFits forced | Map.null forced -> Just True
    IndexImpossible _ -> Just False
    _ -> Nothing

constructorPossible :: K.Environment -> Split -> [IndexPattern] -> SymbolId -> [N.Value] -> Elaboration Bool
constructorPossible environment split indexPatterns constructor fieldValues =
  constructorFits environment split indexPatterns constructor fieldValues >>= \case
    Just possible -> pure possible
    Nothing -> E.failure ("matching cannot decide whether " ++ symbolName constructor ++ " fiteth the indices")

-- after forced fields have been split, each written index variable bindeth
-- the matching part of the constructor's actual index in the branch.
matchedIndexBindings :: K.Environment -> Split -> [IndexPattern] -> SymbolId -> [N.Value] -> Elaboration [(Int, N.Value)]
matchedIndexBindings environment split indexPatterns constructor fieldValues = do
  indices <- constructorIndices environment split constructor fieldValues
  indexBindings environment indexPatterns indices

-- only known constructor shapes justify a recursive call in the declared
-- domain. unlike field planning, this check cannot promise a later split.
indexBindings :: K.Environment -> [IndexPattern] -> [N.Value] -> Elaboration [(Int, N.Value)]
indexBindings environment = bindings
  where
    bindings [] [] = pure []
    bindings (pattern : rest) (value : values) =
      (++) <$> bind pattern value <*> bindings rest values
    bindings _ _ = mismatch
    bind (IndexVariable level) value = pure [(level, value)]
    bind (IndexConstructor expected subpatterns) value =
      constructorView environment value >>= \case
        Just (actual, fields) | actual == expected -> bindings subpatterns fields
        _ -> mismatch
    mismatch = E.failure "the indices do not match the declared index shape"

-- the motive of a split whose indices are constructor patterns. it bindeth
-- fresh indices and the value, and eliminateth the fresh indices into types:
-- where they agree with the patterns, it giveth the goal with each pattern
-- variable replaced by the matching part; elsewhere the trivial
-- `[goal, goal]`. at the written indices it computeth back to the goal.
unifiedMotive :: K.Environment -> Scope -> Int -> Split -> [Level] -> [Term] -> [IndexPattern] -> [Int] -> N.Value -> Elaboration Term
unifiedMotive environment scope level Split {..} levels parameterTerms indexPatterns dependents expected = do
  goalTerm <- quoteFolded scope expected
  dependentDomains <- forM dependents (quote scope . contextType scope)
  let reverted =
        foldr
          (Pi Explicit)
          (abstractLevels (depth scope) dependents goalTerm)
          (zipWith (\position term -> abstractLevels (depth scope) (take position dependents) term) [0 ..] dependentDomains)
  goalLevel <- requireUniverse scope =<< inferCore scope reverted
  motiveType <- inductiveMotiveType scope Split {..} levels parameterTerms
  bindIndices reverted goalLevel scope motiveType (inductiveIndexPlicities splitInfo) []
  where
    bindIndices reverted goalLevel current ty plicities indexLevels =
      E.force ty >>= \case
        N.VPi actual domain codomain
          | plicity : rest <- plicities,
            actual == plicity -> do
              domainTerm <- quote current domain
              let indexLevel = depth current
              (inner, next) <- bindDomain current Nothing domain codomain
              Core.Lambda plicity domainTerm <$> bindIndices reverted goalLevel inner next rest (indexLevel : indexLevels)
          | [] <- plicities,
            actual == Explicit -> do
              domainTerm <- quote current domain
              generalised <- eval current (Pi Explicit domainTerm (Sort goalLevel))
              caseTerm <- unify reverted current (zip (reverse indexLevels) indexPatterns) [] generalised
              pure (Core.Lambda Explicit domainTerm (Apply Explicit (shiftTerm 1 caseTerm) (Local 0)))
        _ -> E.failure "invalid eliminator motive"
    -- `result` is `[worth type, *]` at the current targets.
    unify reverted current [] substitution result =
      E.force result >>= \case
        N.VPi Explicit valueDomain _ -> do
          valueDomainTerm <- quote current valueDomain
          let valueLevel = depth current
              replace outer
                | outer == level = N.VNeutral (N.NLocal valueLevel)
                | Just value <- lookup outer substitution = value
                | otherwise = columnValue scope outer
              values = map replace (reverse [0 .. depth scope - 1])
          goal <- E.evaluate (K.Context values (K.contextTypes (scopeContext scope))) reverted
          -- the rebuilt goal retaineth global names for diagnostics and holes.
          Core.Lambda Explicit valueDomainTerm <$> quoteFolded (extend current Nothing valueDomain) goal
        _ -> E.failure "invalid unified motive"
    unify reverted current ((target, IndexVariable leaf) : rest) substitution result =
      unify reverted current rest ((leaf, N.VNeutral (N.NLocal target)) : substitution) result
    unify reverted current ((target, IndexConstructor constructor subpatterns) : rest) substitution result = do
      let targetType = contextType current target
      split@Split {splitLevels = _, splitInfo = info, splitParameters = parameters, splitIndices = indices, splitEliminator = eliminator} <- columnFamily environment targetType
      unless (null indices) (E.failure "an index pattern cannot match a value of an indexed family")
      fresh <- E.freshUniverses eliminator
      parameterTerms' <- traverse (quote current) parameters
      targetTypeTerm <- quote current targetType
      resultTerm <- quoteFolded current result
      -- splitting an earlier index must also refine the domains of later
      -- indices and constructor fields. revert their telescope before the
      -- split, then rebind it at each constructor's refined types.
      dependents <- dependentInputs current [target]
      domains <- traverse (quote current . contextType current) dependents
      let revertedResult =
            foldr
              (Pi Explicit)
              (abstractLevels (depth current) dependents resultTerm)
              (zipWith (\position term -> abstractLevels (depth current) (take position dependents) term) [0 ..] domains)
          motive = Core.Lambda Explicit targetTypeTerm (abstractLevels (depth current) [target] revertedResult)
      (prefix, prefixType) <- eliminatorPrefix current split fresh parameterTerms' motive (columnValue current target) Nothing
      methods <- E.fromEither (inductiveMethods (globals environment) info)
      (applied, _) <-
        foldM
          ( \partial (candidate, fields) ->
              fmap fst . applyMethod current partial $ \methodType ->
                (,())
                  <$> if candidate `elem` map fst (inductiveConstructorInfo info)
                    then bindMethod current methodType fields [] \inner fieldLevels branchType ->
                      rebind inner branchType dependents [] \entered result' rebound ->
                        if candidate == constructor
                          then do
                            let replace old = maybe (columnValue current old) (N.VNeutral . N.NLocal) (lookup old rebound)
                                context = K.Context (map replace (reverse [0 .. depth current - 1])) (K.contextTypes (scopeContext current))
                            substitution' <- traverse (\(leaf, value) -> (leaf,) <$> (E.evaluate context =<< quote current value)) substitution
                            unify reverted entered (zip fieldLevels subpatterns ++ [(maybe old id (lookup old rebound), pattern) | (old, pattern) <- rest]) substitution' result'
                          else trivial reverted entered result'
                    else trivialMethod current methodType fields
          )
          (prefix, prefixType)
          methods
      pure (foldl (Apply Explicit) (Apply Explicit applied (Local (depth current - target - 1))) [Local (depth current - dependent - 1) | dependent <- dependents])
    rebind current ty [] rebound continue = continue current ty rebound
    rebind current ty (old : rest) rebound continue = do
      (annotation, _, inner, next) <- bindInput "invalid reverted index motive" Explicit Nothing current ty
      Core.Lambda Explicit annotation <$> rebind inner next rest ((old, depth current) : rebound) continue
    trivial reverted current result =
      E.force result >>= \case
        N.VPi Explicit valueDomain _ -> do
          valueDomainTerm <- quote current valueDomain
          -- reverted inputs may raise the goal's universe. the trivial type
          -- must inhabit that same universe, rather than the final result's.
          goal <- quoteFolded (extend current Nothing valueDomain) =<< eval scope reverted
          pure (Core.Lambda Explicit valueDomainTerm (Pi Explicit goal (shiftTerm 1 goal)))
        _ -> E.failure "invalid unified motive"

-- bindeth a method's fields, each recursive one followed by its hypothesis.
bindMethod :: Scope -> N.Value -> [(Plicity, Term, Maybe SymbolId)] -> [Int] -> (Scope -> [Int] -> N.Value -> Elaboration Term) -> Elaboration Term
bindMethod current ty [] levels continue = continue current (reverse levels) ty
bindMethod current ty (field : rest) levels continue = do
  (fieldLevel, _, inner, next, wrap) <- methodField current ty field
  wrap <$> bindMethod inner next rest (fieldLevel : levels) continue

contextType :: Scope -> Int -> N.Value
contextType scope level = K.contextTypes (scopeContext scope) !! (depth scope - level - 1)

allM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
allM predicate = fmap and . traverse predicate

-- a let-bound column carrieth its value; a bound input is its own neutral.
columnValue :: Scope -> Int -> N.Value
columnValue scope level = K.contextValues (scopeContext scope) !! (depth scope - level - 1)

constructorValue :: SymbolId -> [Level] -> [N.Value] -> [(Plicity, N.Value)] -> N.Value
constructorValue constructor levels parameters fields =
  N.VNeutral (foldl (\function (plicity, argument) -> N.NApply plicity function argument) (N.NGlobal constructor levels) ([(Implicit, parameter) | parameter <- parameters] ++ fields))

-- the abstracted levels become new binders, the first outermost.
abstractLevels :: Int -> [Int] -> Term -> Term
abstractLevels depthNow levels = runIdentity . traverseScoped replace
  where
    count = length levels
    replace bound (Local index) _
      | index < bound = pure (Local index)
      | Just position <- elemIndex (depthNow - (index - bound) - 1) levels = pure (Local (bound + count - 1 - position))
      | otherwise = pure (Local (index + count))
    replace _ _ descend = descend
