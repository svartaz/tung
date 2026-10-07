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
    bindInput,
    methodField,
    applyMethod,
    childName,
    memoRecord,
    applyMemo,
    Clauses (..),
  )
where

import Data.Map.Strict qualified as Map
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core
import Tung.Identity (SymbolId (..), inductionSymbol)

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
    columnType :: N.Value
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

-- an index in constructor form over variables, as `n s` or `a ‥ empty`.
data IndexPattern = IndexVariable Int | IndexConstructor SymbolId [IndexPattern]

-- bindeth the next input of a function type at the next level: the input's
-- domain term and value, the extended scope, and the type of the rest.
bindInput :: String -> Plicity -> Maybe String -> Scope -> N.Value -> Elaboration (Term, N.Value, Scope, N.Value)
bindInput problem plicity name current ty =
  E.force ty >>= \case
    N.VPi actual domain codomain | actual == plicity -> do
      domainTerm <- quote current domain
      next <- E.instantiate codomain (N.VNeutral (N.NLocal (depth current)))
      pure (domainTerm, domain, extend current name domain, next)
    _ -> E.failure problem

-- bindeth one method field, and after a recursive field its hypothesis: the
-- field's level, the hypothesis level, the scope and type after them, and the
-- lambdas that wrap a body.
methodField :: Scope -> N.Value -> (Plicity, Term, Bool) -> Elaboration (Int, Maybe Int, Scope, N.Value, Term -> Term)
methodField current ty (plicity, _, recursive) = do
  (domainTerm, _, afterField, next) <- bindInput "invalid eliminator method" plicity Nothing current ty
  if recursive
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

-- recursive fields are named in order; zero padding keepeth the record sorted.
childName :: Int -> String
childName index = "child" ++ replicate (3 - length (show index)) '0' ++ show index

-- the record of a known descendant, reached from its local.
memoRecord :: Scope -> Memo -> N.Value -> Elaboration (Maybe Term)
memoRecord scope Memo {memoEntries} value = do
  wanted <- eraseGlobalLevels <$> quote scope value
  known <- traverse (\(entry, place) -> (,place) . eraseGlobalLevels <$> quote scope entry) memoEntries
  pure case lookup wanted known of
    Just (level, path) -> Just (foldl Project (Local (depth scope - level - 1)) path)
    Nothing -> Nothing

-- the memoised motive applied to a value, quoted in the given scope.
applyMemo :: Scope -> Memo -> N.Value -> Elaboration Term
applyMemo scope Memo {memoType} value =
  E.force memoType >>= \case
    N.VLambda _ _ closure -> E.instantiate closure value >>= quote scope
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
