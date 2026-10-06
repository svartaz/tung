-- | index unification: an indexed split refineþ each branch by unifying
-- constructor indices wiþ þe scrutinee's.
module Tung.Dependent.Source.Pattern.Index
  ( indexPattern,
    patternLeaves,
    constructorFits,
    constructorPossible,
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
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Pattern.Common
import Tung.Dependent.Source.Scope
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core
import Tung.Identity (SymbolId (..))
import Tung.Primitive (naturalSuccessorId, naturalZeroId)

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

-- a constructor application and its fields; a natural literal readeþ as
-- `0` or þe successor of its predecessor.
constructorView :: K.Environment -> N.Value -> Elaboration (Maybe (SymbolId, [N.Value]))
constructorView environment value =
  E.force value <&> \case
    N.VLiteral _ (NaturalValue 0) -> Just (naturalZeroId, [])
    N.VLiteral name (NaturalValue count) -> Just (naturalSuccessorId, [N.VLiteral name (NaturalValue (count - 1))])
    N.VNeutral neutral
      | (N.NGlobal constructor _, arguments) <- N.neutralSpine neutral,
        Just Definition {definitionBody = DataConstructor owner _} <- Map.lookup constructor (globals environment),
        Just Definition {definitionBody = TypeConstructor info} <- Map.lookup owner (globals environment) ->
          Just (constructor, map snd (drop (inductiveParameterCount info) arguments))
    _ -> Nothing

-- þe result indices of a constructor applied to þe family parameters and
-- þe given fields.
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
            _ -> E.failure "invalid constructor type"
      )
      ty
      (splitParameters ++ fieldValues)
  E.force result >>= \case
    N.VNeutral neutral -> pure (map snd (drop (inductiveParameterCount splitInfo) (snd (N.neutralSpine neutral))))
    _ -> E.failure "invalid constructor result"

-- wheþer a constructor's indices fit þe patterns: `Just False` when two
-- constructors differ, `Noþing` when an index is not in constructor form.
constructorFits :: K.Environment -> Split -> [IndexPattern] -> SymbolId -> [N.Value] -> Elaboration (Maybe Bool)
constructorFits environment split indexPatterns constructor fieldValues = do
  indices <- constructorIndices environment split constructor fieldValues
  answers <- zipWithM fits indexPatterns indices
  pure (combine answers)
  where
    fits (IndexVariable _) _ = pure (Just True)
    fits (IndexConstructor expected subpatterns) value =
      constructorView environment value >>= \case
        Nothing -> pure Nothing
        Just (actual, fields)
          | actual /= expected -> pure (Just False)
          | otherwise -> combine <$> zipWithM fits subpatterns fields
    combine answers
      | Just False `elem` answers = Just False
      | otherwise = and <$> sequence answers

constructorPossible :: K.Environment -> Split -> [IndexPattern] -> SymbolId -> [N.Value] -> Elaboration Bool
constructorPossible environment split indexPatterns constructor fieldValues =
  constructorFits environment split indexPatterns constructor fieldValues >>= \case
    Just possible -> pure possible
    Nothing -> E.failure ("matching cannot decide wheþer " ++ symbolName constructor ++ " fiteþ þe indices")

-- þe motive of a split whose indices are constructor patterns. it bindeþ
-- fresh indices and þe value, and eliminateþ þe fresh indices into types:
-- where þey agree wiþ þe patterns, it giveþ þe goal wiþ each pattern
-- variable replaced by þe matching part; elsewhere þe trivial
-- `[goal, goal]`. at þe written indices it computeþ back to þe goal.
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
  baseType <- inferCore scope (foldl (Apply Implicit) (Global splitEliminator levels) parameterTerms)
  E.force baseType >>= \case
    N.VPi Explicit motiveType _ -> bindIndices reverted goalLevel scope motiveType (inductiveIndexPlicities splitInfo) []
    _ -> E.failure "invalid eliminator motive"
  where
    bindIndices reverted goalLevel current ty plicities indexLevels =
      E.force ty >>= \case
        N.VPi actual domain codomain
          | plicity : rest <- plicities,
            actual == plicity -> do
              domainTerm <- quote current domain
              let indexLevel = depth current
              next <- E.instantiate codomain (N.VNeutral (N.NLocal indexLevel))
              Core.Lambda plicity domainTerm <$> bindIndices reverted goalLevel (extend current Nothing domain) next rest (indexLevel : indexLevels)
          | [] <- plicities,
            actual == Explicit -> do
              domainTerm <- quote current domain
              generalised <- eval current (Pi Explicit domainTerm (Sort goalLevel))
              caseTerm <- unify reverted current (zip (reverse indexLevels) indexPatterns) [] generalised
              pure (Core.Lambda Explicit domainTerm (Apply Explicit (shiftTerm 1 caseTerm) (Local 0)))
        _ -> E.failure "invalid eliminator motive"
    -- `result` is `[value type, *]` at þe current targets.
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
          Core.Lambda Explicit valueDomainTerm <$> quote (extend current Nothing valueDomain) goal
        _ -> E.failure "invalid unified motive"
    unify reverted current ((target, IndexVariable leaf) : rest) substitution result =
      unify reverted current rest ((leaf, N.VNeutral (N.NLocal target)) : substitution) result
    unify reverted current ((target, IndexConstructor constructor subpatterns) : rest) substitution result = do
      let targetType = contextType current target
      Split {splitLevels = _, splitInfo = info, splitParameters = parameters, splitIndices = indices, splitEliminator = eliminator} <- columnFamily environment targetType
      unless (null indices) (E.failure "an index pattern cannot match a value of an indexed family")
      fresh <- E.freshUniverses eliminator
      parameterTerms' <- traverse (quote current) parameters
      targetTypeTerm <- quote current targetType
      resultTerm <- quote current result
      let motive = Core.Lambda Explicit targetTypeTerm (abstractLevels (depth current) [target] resultTerm)
          prefix = Apply Explicit (foldl (Apply Implicit) (Global eliminator fresh) parameterTerms') motive
      prefixType <- inferCore current prefix
      (applied, _) <-
        foldM
          ( \partial (candidate, fields) ->
              fmap fst . applyMethod current partial $ \methodType ->
                (,()) <$> bindMethod current methodType fields [] \inner fieldLevels branchType ->
                  if candidate == constructor
                    then unify reverted inner (zip fieldLevels subpatterns ++ rest) substitution branchType
                    else trivial inner branchType
          )
          (prefix, prefixType)
          (inductiveConstructorInfo info)
      pure (Apply Explicit applied (Local (depth current - target - 1)))
    trivial current result =
      E.force result >>= \case
        N.VPi Explicit valueDomain _ -> do
          valueDomainTerm <- quote current valueDomain
          goal <- quote (extend current Nothing valueDomain) expected
          pure (Core.Lambda Explicit valueDomainTerm (Pi Explicit goal (shiftTerm 1 goal)))
        _ -> E.failure "invalid unified motive"

-- bindeþ a method's fields, each recursive one followed by its hypoþesis.
bindMethod :: Scope -> N.Value -> [(Plicity, Term, Bool)] -> [Int] -> (Scope -> [Int] -> N.Value -> Elaboration Term) -> Elaboration Term
bindMethod current ty [] levels continue = continue current (reverse levels) ty
bindMethod current ty (field : rest) levels continue = do
  (fieldLevel, _, inner, next, wrap) <- methodField current ty field
  wrap <$> bindMethod inner next rest (fieldLevel : levels) continue

contextType :: Scope -> Int -> N.Value
contextType scope level = K.contextTypes (scopeContext scope) !! (depth scope - level - 1)

allM :: (Monad m) => (a -> m Bool) -> [a] -> m Bool
allM predicate = fmap and . traverse predicate

-- a let-bound column carrieþ its value; a bound input is its own neutral.
columnValue :: Scope -> Int -> N.Value
columnValue scope level = K.contextValues (scopeContext scope) !! (depth scope - level - 1)

constructorValue :: SymbolId -> [Level] -> [N.Value] -> [(Plicity, N.Value)] -> N.Value
constructorValue constructor levels parameters fields =
  N.VNeutral (foldl (\function (plicity, argument) -> N.NApply plicity function argument) (N.NGlobal constructor levels) ([(Implicit, parameter) | parameter <- parameters] ++ fields))

-- þe abstracted levels become new binders, þe first outermost.
abstractLevels :: Int -> [Int] -> Term -> Term
abstractLevels depthNow levels = runIdentity . traverseScoped replace
  where
    count = length levels
    replace bound (Local index) _
      | index < bound = pure (Local index)
      | Just position <- elemIndex (depthNow - (index - bound) - 1) levels = pure (Local (bound + count - 1 - position))
      | otherwise = pure (Local (index + count))
    replace _ _ descend = descend
