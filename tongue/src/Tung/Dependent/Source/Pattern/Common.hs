-- | types and binder helpers shared by pattern compilation, index
-- unification, and structural recursion.
module Tung.Dependent.Source.Pattern.Common
  ( ExpressionChecker (..),
    Column (..),
    PatternTree (..),
    MatchRow (..),
    Split (..),
    columnFamily,
    familyOf,
    IndexPattern (..),
    dependentInputs,
    bindInput,
    methodField,
    applyMethod,
    inductiveMotiveType,
    eliminatorPrefix,
    trivialMethod,
    childName,
    memoRecord,
    applyIndexedMotive,
    applyMemo,
    Clauses (..),
  )
where

import Control.Monad (foldM, unless)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust)
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core
import Tung.Identity (SymbolId (..), inducedFamily, inductionSymbol)

type Elaboration = E.Elaboration

-- expression checking may re-enter pattern compilation through these callbacks.
-- the interface carrieth no module loader or declaration checker.
data ExpressionChecker = ExpressionChecker
  { -- the definitions and names the callbacks elaborate against.
    checkerEnvironment :: K.Environment,
    checkerNames :: Names,
    inferTerm :: Scope -> Expression -> Elaboration (Term, N.Value),
    annotationType :: Scope -> Expression -> Elaboration N.Value,
    checkTerm :: Scope -> Expression -> N.Value -> Elaboration Term,
    applyTerm :: Scope -> Term -> N.Value -> [Argument] -> [Argument] -> Elaboration (Term, N.Value),
    -- solveth instance goals whose class argument is already known.
    settleInstances :: Elaboration ()
  }

-- a match column is a bound local and its type. splitting a column applieth
-- the family's eliminator, so the kernel needeth no case or fixpoint rule.
data Column = Column
  { columnLevel :: Int,
    columnType :: N.Value,
    -- only fields determined by an index split carry a known constructor.
    -- ordinary scrutinees require coverage of their entire input type, even
    -- when their supplied value is a constructor.
    columnConstructor :: Maybe (SymbolId, [N.Value])
  }

data PatternTree
  = PVariable (Maybe String)
  | PConstructor SymbolId [(Plicity, PatternTree)]
  | -- a literal of a primitive type, compared with `literal_case`.
    PLiteral HostLiteral
  | -- another name for the whole column, whether from a repeated pattern or
    -- a recursive input rebound to the value matched at each step.
    PNamed String PatternTree

data MatchRow = MatchRow
  { matchRowId :: Int,
    matchPatterns :: [PatternTree],
    -- names bound by earlier splits, with their values and types.
    matchBindings :: [(String, N.Value, N.Value)],
    matchBody :: Expression
  }

-- the family of a column, with its parameters and eliminator.
data Split = Split
  { splitLevels :: [Level],
    splitInfo :: InductiveInfo,
    splitParameters :: [N.Value],
    splitIndices :: [N.Value],
    splitEliminator :: SymbolId
  }

-- a column whose type is still a hole may be fixed by splitting a stuck
-- equation, as instance search doth.
columnFamily :: K.Environment -> N.Value -> Elaboration Split
columnFamily environment ty =
  familyOf environment ty >>= \case
    Just split -> pure split
    Nothing ->
      E.approximate >>= \case
        True -> columnFamily environment ty
        False -> E.failure "a constructor pattern requireth a value of an inductive type"

familyOf :: K.Environment -> N.Value -> Elaboration (Maybe Split)
familyOf environment ty =
  E.force ty >>= \case
    N.VNeutral neutral
      | (N.NGlobal family levels, arguments) <- N.neutralSpine neutral,
        Just Definition {definitionBody = TypeConstructor info} <- Map.lookup family (globals environment),
        let eliminator = inductionSymbol family,
        Just Definition {definitionBody = Eliminator _} <- Map.lookup eliminator (globals environment) ->
          pure (Just (Split levels info (map snd (take (inductiveParameterCount info) arguments)) (map snd (drop (inductiveParameterCount info) arguments)) eliminator))
    _ -> pure Nothing

-- later bound inputs whose domains depend transitively on the split locals.
-- they must be reverted together, in telescope order, before elimination.
dependentInputs :: Scope -> [Int] -> Elaboration [Int]
dependentInputs _ [] = pure []
dependentInputs scope targets =
  foldM include [] [level | level <- [minimum targets + 1 .. depth scope - 1], level `notElem` targets]
  where
    include found level = do
      let position = depth scope - level - 1
          context = scopeContext scope
      mentioned <- map (\index -> depth scope - index - 1) . freeIndices <$> quote scope (K.contextTypes context !! position)
      bound <- E.force (K.contextValues context !! position)
      pure case bound of
        N.VNeutral (N.NLocal same)
          | same == level && any (`elem` (targets ++ found)) mentioned -> found ++ [level]
        _ -> found

-- bindeth the next input of a function type at the next level: the input's
-- domain term and value, the extended scope, and the type of the rest.
bindInput :: String -> Plicity -> Maybe String -> Scope -> N.Value -> Elaboration (Term, N.Value, Scope, N.Value)
bindInput problem plicity name current ty =
  E.force ty >>= \case
    N.VPi actual domain codomain | actual == plicity -> do
      domainTerm <- quote current domain
      (inner, next) <- bindDomain current name domain codomain
      pure (domainTerm, domain, inner, next)
    _ -> E.failure problem

-- bindeth one method field, and after a recursive field its hypothesis: the
-- field's level, the hypothesis level, the scope and type after them, and the
-- lambdas that wrap a body.
methodField :: Scope -> N.Value -> (Plicity, Term, Maybe SymbolId) -> Elaboration (Int, Maybe Int, Scope, N.Value, Term -> Term)
methodField current ty (plicity, _, recursive) = do
  (domainTerm, _, afterField, next) <- bindInput "invalid eliminator method" plicity Nothing current ty
  if isJust recursive
    then do
      (hypothesisTerm, _, afterHypothesis, next') <- bindInput "invalid induction hypothesis" Explicit Nothing afterField next
      pure (depth current, Just (depth afterField), afterHypothesis, next', Core.Lambda plicity domainTerm . Core.Lambda Explicit hypothesisTerm)
    else pure (depth current, Nothing, afterField, next, Core.Lambda plicity domainTerm)

-- applieth an eliminator prefix to the method `build` maketh from the method
-- type, and returneth the applied term with its type.
applyMethod :: Scope -> (Term, N.Value) -> (N.Value -> Elaboration (Term, a)) -> Elaboration ((Term, N.Value), a)
applyMethod scope (term, termType) build =
  E.force termType >>= \case
    N.VPi Explicit methodType codomain -> do
      (method, result) <- build methodType
      next <- eval scope method >>= E.instantiate codomain
      pure ((Apply Explicit term method, next), result)
    _ -> E.failure "invalid eliminator method type"

-- motive domains depend only on the common parameters, never earlier motives.
-- bind those earlier motives privately to reach this family's domain.
inductiveMotiveType :: Scope -> Split -> [Level] -> [Term] -> Elaboration N.Value
inductiveMotiveType scope Split {..} levels parameters = do
  ty <- inferCore scope (foldl (Apply Implicit) (Global splitEliminator levels) parameters)
  go scope ty (inductiveFamilies splitInfo)
  where
    go current ty (family : rest) =
      E.force ty >>= \case
        N.VPi Explicit domain codomain
          | Just family == inducedFamily splitEliminator -> pure domain
          | otherwise -> do
              (inner, next) <- bindDomain current Nothing domain codomain
              go inner next rest
        _ -> E.failure "invalid inductive motive type"
    go _ _ [] = E.failure "missing inductive motive"

-- ordinary matching instantiateth joint induction with the selected motive.
-- peer motives use the inhabited [goal, goal], or their joint memo records.
eliminatorPrefix :: Scope -> Split -> [Level] -> [Term] -> Term -> N.Value -> Maybe Memo -> Elaboration (Term, N.Value)
eliminatorPrefix scope Split {..} levels parameters motive target memo = do
  let prefix = foldl (Apply Implicit) (Global splitEliminator levels) parameters
  ty <- inferCore scope prefix
  foldM supply (prefix, ty) (inductiveFamilies splitInfo)
  where
    supply (term, ty) family =
      E.force ty >>= \case
        N.VPi Explicit domain codomain -> do
          chosen <- case memo of
            _ | Just family == inducedFamily splitEliminator -> pure motive
            Just Memo {memoTypes} -> maybe (E.failure "missing joint memo motive") (quote scope . snd) (lookup family memoTypes)
            Nothing -> do
              indices <- traverse (quote scope) splitIndices
              value <- quote scope target
              goal <- eval scope (applyArguments motive (zip (inductiveIndexPlicities splitInfo) indices ++ [(Explicit, value)]))
              goalTerm <- quoteFolded scope goal
              trivial <- eval scope (Pi Explicit goalTerm (shiftTerm 1 goalTerm))
              constantMotive scope domain trivial
          inferred <- inferCore scope chosen
          E.unify (scopeContext scope) inferred domain
          result <- eval scope chosen >>= E.instantiate codomain
          pure (Apply Explicit term chosen, result)
        _ -> E.failure "invalid inductive motive type"
    constantMotive current ty trivial =
      E.force ty >>= \case
        N.VPi plicity domain codomain -> do
          annotation <- quote current domain
          (inner, next) <- bindDomain current Nothing domain codomain
          Core.Lambda plicity annotation <$> constantMotive inner next trivial
        N.VSort _ -> quote current trivial
        _ -> E.failure "invalid inductive motive result"

trivialMethod :: Scope -> N.Value -> [(Plicity, Term, Maybe SymbolId)] -> Elaboration Term
trivialMethod current ty [] =
  E.force ty >>= \case
    N.VPi Explicit domain _ -> do
      annotation <- quote current domain
      pure (Core.Lambda Explicit annotation (Local 0))
    _ -> E.failure "invalid trivial eliminator method"
trivialMethod current ty (field : rest) = do
  (_, _, inner, next, wrap) <- methodField current ty field
  wrap <$> trivialMethod inner next rest

-- recursive fields are named in order; zero padding keepeth the record sorted.
childName :: Int -> String
childName index = "child" ++ replicate (3 - length (show index)) '0' ++ show index

-- a function field's record taketh the same arguments as the field. a known
-- prefix must match before its remaining arguments may select a descendant.
memoRecord :: Scope -> Memo -> N.Value -> Elaboration (Maybe (SymbolId, Term))
memoRecord scope Memo {memoEntries} value = do
  wanted <- quote scope value
  known <- traverse (\(entry, place) -> (,place) <$> quote scope entry) memoEntries
  let (function, arguments) = termSpine wanted
      find [] = Nothing
      find ((entry, (target, level, path)) : rest) =
        let (entryFunction, prefix) = termSpine entry
         in if sameUpToLevels function entryFunction && length prefix <= length arguments && and (zipWith (\(plicity, value) (other, entry) -> plicity == other && sameUpToLevels value entry) arguments prefix)
              then Just (target, applyArguments (foldl Project (Local (depth scope - level - 1)) path) (drop (length prefix) arguments))
              else find rest
  pure (find known)

-- the memoised motive applied to a value, quoted in the given scope.
applyMemo :: Scope -> Memo -> SymbolId -> N.Value -> Elaboration Term
applyMemo scope Memo {memoTypes} target value = do
  (plicities, motive) <- maybe (E.failure "missing joint memo motive") pure (lookup target memoTypes)
  applyIndexedMotive scope plicities motive value >>= quote scope

-- a child's checked type giveth its own indices, including dependent ones.
-- public container heads may differ from specialised target labels, so only
-- the final index arguments are read; unindexed motives need no type query.
applyIndexedMotive :: Scope -> [Plicity] -> N.Value -> N.Value -> Elaboration N.Value
applyIndexedMotive scope plicities motive value = do
  indices <-
    if null plicities
      then pure []
      else do
        ty <- inferCore scope =<< quote scope value
        E.force ty >>= \case
          N.VNeutral neutral
            | (N.NGlobal _ _, arguments) <- N.neutralSpine neutral -> do
                let count = length plicities
                    ending = drop (length arguments - count) arguments
                unless (length arguments >= count && map fst ending == plicities) (E.failure "invalid memoised target indices")
                pure ending
          _ -> E.failure "invalid memoised target type"
  foldM instantiate motive (indices ++ [(Explicit, value)])
  where
    instantiate current (plicity, argument) =
      E.force current >>= \case
        N.VLambda actual _ closure | actual == plicity -> E.instantiate closure argument
        _ -> E.failure "invalid memoised motive"

-- a recursive definition's inputs and clauses. named lambda binders become
-- variable columns; a final case function or a match on inputs supplieth rows.
data Clauses = Clauses
  { clauseScope :: Scope,
    -- every input in order: its level, plicity, and type.
    clauseInputs :: [(Int, Plicity, N.Value)],
    clauseResult :: N.Value,
    clauseRows :: [MatchRow],
    clauseWrittenRows :: [MatchRow],
    -- columns a `match` scrutiniseth by input name.
    clauseAliases :: [(Int, String)]
  }
