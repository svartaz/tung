-- | pattern matrices and total recursion lower to dependent eliminators.
-- this module checkeþ coverage, refineþ indexed branches, and constructeþ motives.
-- general expressions are delegated to the supplied checking operations.
module Tung.Dependent.Source.Pattern
  ( ExpressionChecker (..),
    constructorBinder,
    constructorNamed,
    checkCases,
    checkMatch,
    elaborateRecursive,
    recursiveCall,
  )
where

import Control.Applicative ((<|>))
import Control.Monad (filterM, foldM, forM, forM_, unless, when, zipWithM)
import Data.Foldable (foldrM)
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity (..))
import Data.List (elemIndex, nub, nubBy)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes)
import Data.Set qualified as Set
import GHC.TypeLits qualified
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Host qualified as H
import Tung.Dependent.Literal (literalType)
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core
import Tung.Identity (SymbolId (..), inductionSymbol)
import Tung.Primitive (naturalSuccessorId, naturalZeroId)

type Elaboration = E.Elaboration

-- expression checking may re-enter pattern compilation through these callbacks.
-- the interface carrieþ no module loader or declaration checker.
data ExpressionChecker = ExpressionChecker
  { inferTerm :: Scope -> Expression -> Elaboration (Term, N.Value),
    annotationType :: Scope -> Expression -> Elaboration N.Value,
    checkTerm :: Scope -> Expression -> N.Value -> Elaboration Term,
    applyTerm :: Scope -> Term -> N.Value -> [Argument] -> [Argument] -> Elaboration (Term, N.Value),
    -- solveþ instance goals whose class argument is already known.
    settleInstances :: Elaboration ()
  }

-- a match column is a bound local and its type. splitting a column applieþ
-- the family's eliminator, so the kernel needeþ no case or fixpoint rule.
data Column = Column
  { columnLevel :: Int,
    columnType :: N.Value
  }

data PatternTree
  = PVariable (Maybe String)
  | PConstructor SymbolId [(Plicity, PatternTree)]
  | -- a literal of a primitive type, compared wiþ `literal_case`.
    PLiteral HostLiteral
  | -- another name for þe whole column, whether from a repeated pattern or
    -- a recursive input rebound to þe value matched at each step.
    PNamed String PatternTree

-- þe names a column pattern bindeþ to þe whole value, and þe pattern beneaþ.
unnamed :: PatternTree -> ([String], PatternTree)
unnamed = \case
  PNamed name pattern -> let (names, inner) = unnamed pattern in (name : names, inner)
  pattern -> ([], pattern)

data MatchRow = MatchRow
  { matchRowId :: Int,
    matchPatterns :: [PatternTree],
    -- names bound by earlier splits, wiþ their values and types.
    matchBindings :: [(String, N.Value, N.Value)],
    matchBody :: Expression
  }

constructorBinder :: K.Environment -> Names -> Binder -> Bool
constructorBinder environment names Binder {binderPlicity = Explicit, binderName = Just name, binderAnnotation = Nothing} =
  maybe False (const True) (constructorNamed environment names name)
constructorBinder _ _ _ = False

constructorNamed :: K.Environment -> Names -> String -> Maybe SymbolId
constructorNamed environment names name = do
  identity <- lookupName name names >>= bindingSymbol
  Definition {definitionBody = DataConstructor _ _} <- Map.lookup identity (globals environment)
  pure identity

-- a name that is not a constructor bindeþ a variable, even when it shadoweþ
-- a local or global value.
resolvePattern :: K.Environment -> Names -> Expression -> Elaboration PatternTree
resolvePattern environment names = \case
  Name name | Just (AmbiguousName modules) <- lookupName name names -> E.failure (ambiguousName name modules)
  Wildcard -> pure (PVariable Nothing)
  -- a natural literal is `0` or þe successor of its predecessor.
  LiteralExpression (NaturalValue value) -> pure (naturalPattern value)
  LiteralExpression literal -> pure (PLiteral literal)
  Name name -> pure (maybe (PVariable (bindingName (Just name))) (`PConstructor` []) (constructorNamed environment names name))
  Application (Name name) arguments
    | Just constructor <- constructorNamed environment names name ->
        PConstructor constructor <$> traverse (\Argument {..} -> (argumentPlicity,) <$> resolvePattern environment names argumentExpression) arguments
  Application _ _ -> E.failure "a pattern application must name a constructor"
  _ -> E.failure "unsupported pattern"

-- `{}` hath one input, of an empty family.
naturalPattern :: GHC.TypeLits.Natural -> PatternTree
naturalPattern 0 = PConstructor naturalZeroId []
naturalPattern value = PConstructor naturalSuccessorId [(Explicit, naturalPattern (value - 1))]

rowArity :: [Row] -> Int
rowArity = \case
  Row {rowPatterns} : _ -> length rowPatterns
  [] -> 1

matchRows :: K.Environment -> Names -> [Row] -> Elaboration [MatchRow]
matchRows environment names rows = do
  requireRowArity rows
  resolved <- sequence [MatchRow index <$> traverse (resolvePattern environment names) rowPatterns <*> pure [] <*> pure rowBody | (index, Row {..}) <- zip [0 ..] rows]
  -- a row bindeþ each name once.
  forM_ resolved \MatchRow {matchPatterns} ->
    let bound = concatMap variables matchPatterns
     in case [name | (index, name) <- zip [0 :: Int ..] bound, name `elem` take index bound] of
          name : _ -> E.failure ("'" ++ name ++ "' is bound twice in one row")
          [] -> pure ()
  pure resolved
  where
    variables = \case
      PVariable (Just name) -> [name]
      PVariable Nothing -> []
      PConstructor _ subpatterns -> concatMap (variables . snd) subpatterns
      PLiteral _ -> []
      PNamed _ pattern -> variables pattern

-- validate the written matrix before recursive clauses project its columns.
requireRowArity :: [Row] -> Elaboration ()
requireRowArity rows =
  unless (all ((== rowArity rows) . length . rowPatterns) rows) (E.failure "every case must have the same number of patterns")

requireMatchArity :: [Expression] -> [Row] -> Elaboration ()
requireMatchArity scrutinees rows =
  unless (null rows || length scrutinees == rowArity rows) (E.failure "a match needs one pattern per scrutinee")

-- each group containeþ all written columns that denote one input. their
-- patterns intersect; aliases retain every binder and impossible rows retain
-- their original identity for the caller's redundancy check.
projectRows :: K.Environment -> [[Int]] -> [PatternTree] -> [MatchRow] -> Elaboration [MatchRow]
projectRows environment groups defaults rows = catMaybes <$> traverse project rows
  where
    project row@MatchRow {..} = do
      patterns <- if any ((> 1) . length) groups then traverse align matchPatterns else pure matchPatterns
      let merge (positions, fallback) = case map (patterns !!) positions of
            [] -> Just fallback
            first : rest -> foldM intersectPattern first rest
          merged = traverse merge (zip groups defaults)
      pure ((\patterns' -> row {matchPatterns = patterns'}) <$> merged)
    -- constructor fields have one canonical order before intersection, so
    -- omitted implicit patterns and explicit patterns cannot be misaligned.
    align = \case
      PConstructor constructor subpatterns -> do
        fields <- case do
          Definition {definitionBody = DataConstructor owner _} <- Map.lookup constructor (globals environment)
          Definition {definitionBody = TypeConstructor info} <- Map.lookup owner (globals environment)
          lookup constructor (inductiveConstructorInfo info) of
          Just fields -> pure fields
          Nothing -> E.failure "missing constructor fields"
        assigned <- assignFields fields subpatterns >>= traverse align
        pure (PConstructor constructor (zip [plicity | (plicity, _, _) <- fields] assigned))
      PNamed name pattern -> PNamed name <$> align pattern
      pattern -> pure pattern

-- the inputs are aligned by projectRows. two patterns of one value require
-- compatible constructors or literals; variables add whole-value aliases.
intersectPattern :: PatternTree -> PatternTree -> Maybe PatternTree
intersectPattern left right =
  let (leftNames, leftPattern) = unnamed left
      (rightNames, rightPattern) = unnamed right
      named = foldr PNamed
   in case (leftPattern, rightPattern) of
        (PVariable name, _) -> Just (named rightPattern (leftNames ++ maybe [] pure name ++ rightNames))
        (_, PVariable name) -> Just (named leftPattern (leftNames ++ rightNames ++ maybe [] pure name))
        (PConstructor constructor leftFields, PConstructor other rightFields)
          | constructor == other -> do
              fields <- traverse (\((plicity, first), (_, second)) -> (plicity,) <$> intersectPattern first second) (zip leftFields rightFields)
              pure (named (PConstructor constructor fields) (leftNames ++ rightNames))
        (PLiteral literal, PLiteral other)
          | literal == other -> Just (named (PLiteral literal) (leftNames ++ rightNames))
        _ -> Nothing

-- explicit patterns fill explicit fields; omitted implicit fields are wildcards.
assignFields :: [(Plicity, Term, Bool)] -> [(Plicity, PatternTree)] -> Elaboration [PatternTree]
assignFields fields subpatterns = do
  let explicitFields = length [() | (Explicit, _, _) <- fields]
      explicitPatterns = [pattern | (Explicit, pattern) <- subpatterns]
      implicitPatterns = [pattern | (Implicit, pattern) <- subpatterns]
  unless (length explicitPatterns == explicitFields) (E.failure ("a constructor pattern needs " ++ show explicitFields ++ " explicit arguments"))
  unless (length implicitPatterns <= length fields - explicitFields) (E.failure "too many implicit constructor pattern arguments")
  pure (distribute fields explicitPatterns implicitPatterns)
  where
    distribute [] _ _ = []
    distribute ((Explicit, _, _) : rest) (pattern : explicitPatterns) implicitPatterns = pattern : distribute rest explicitPatterns implicitPatterns
    distribute ((Implicit, _, _) : rest) explicitPatterns (pattern : implicitPatterns) = pattern : distribute rest explicitPatterns implicitPatterns
    distribute (_ : rest) explicitPatterns implicitPatterns = PVariable Nothing : distribute rest explicitPatterns implicitPatterns

-- explicit inputs become columns; an implicit product before them gaineþ an
-- unnamed binder, as wiþ an ordinary lambda.
checkCases :: ExpressionChecker -> K.Environment -> Names -> Scope -> [Row] -> N.Value -> Elaboration Term
checkCases checker environment names scope rows expected = do
  resolved <- matchRows environment names rows
  (current, inputs, resultType) <- bindCaseInputs environment scope (rowArity rows) expected
  let columns = [Column level domain | (level, Explicit, domain) <- inputs]
  (term, used) <- compileMatch checker environment names current columns resolved resultType
  requireUsed resolved used
  wrapInputs environment inputs term

-- domains are quoted at their original binder depth after body checking,
-- so inferred holes need no parallel list of quoted annotations.
wrapInputs :: K.Environment -> [(Int, Plicity, N.Value)] -> Term -> Elaboration Term
wrapInputs environment inputs term = foldrM wrap term inputs
  where
    wrap (level, plicity, domain) body = do
      annotation <- E.quote (globals environment) level domain
      pure (Core.Lambda plicity annotation body)

-- consume one product spine for ordinary and recursive case functions.
-- implicit inputs gain anonymous locals without consuming written patterns.
bindCaseInputs :: K.Environment -> Scope -> Int -> N.Value -> Elaboration (Scope, [(Int, Plicity, N.Value)], N.Value)
bindCaseInputs environment start count expected = go start count expected []
  where
    go current 0 ty inputs = pure (current, reverse inputs, ty)
    go current remaining ty inputs =
      E.force (globals environment) ty >>= \case
        N.VPi plicity domain codomain -> do
          let level = depth current
              remaining' = if plicity == Explicit then remaining - 1 else remaining
          resultType <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal level))
          go (extend current Nothing domain) remaining' resultType ((level, plicity, domain) : inputs)
        _ -> E.failure "a case function needs a function type wiþ one input per pattern"

-- a scrutinee that is already a local is matched in place, so the result
-- type may depend on it. oþer scrutinees are bound first.
checkMatch :: ExpressionChecker -> K.Environment -> Names -> Scope -> [Expression] -> [Row] -> N.Value -> Elaboration Term
checkMatch checker environment names scope scrutinees rows expected = do
  resolved <- matchRows environment names rows
  requireMatchArity scrutinees rows
  bindScrutinees scope scrutinees [] expected \current columns goal -> do
    let distinct = nubBy (\left right -> columnLevel left == columnLevel right) columns
        levels = map columnLevel distinct
        groups = [[index | (index, column) <- zip [0 ..] columns, columnLevel column == level] | level <- levels]
    projected <- projectRows environment groups (map (const (PVariable Nothing)) distinct) resolved
    (term, used) <- compileMatch checker environment names current distinct projected goal
    requireUsed resolved used
    pure term
  where
    bindScrutinees current [] columns goal continue = continue current (reverse columns) goal
    bindScrutinees current (scrutinee : remaining) columns goal continue = do
      (term, ty) <- inferTerm checker current scrutinee
      value <- eval environment current term >>= E.force (globals environment)
      annotation <- quote environment current ty
      let level = depth current
      case value of
        N.VNeutral (N.NLocal local) -> bindScrutinees current remaining (Column local ty : columns) goal continue
        _ ->
          generalise current value ty goal >>= \case
            -- þe computed scrutinee becomeþ an input, so each row seeþ its
            -- constructor in þe goal, as agda's `with` doþ.
            Just abstracted -> do
              body <- bindScrutinees (extend current Nothing ty) remaining (Column level ty : columns) abstracted continue
              pure (Apply Explicit (Core.Lambda Explicit annotation body) term)
            Nothing -> Let annotation term <$> bindScrutinees (define current Nothing value ty) remaining (Column level ty : columns) goal continue
    -- þe goal over a new input in place of each occurrence of a stuck
    -- computation. constructors and literals are not abstracted, nor is a
    -- goal þat doþ not mention þe value or would be ill-typed wiþout it.
    -- occurrences match up to universe levels; reinstating þe scrutinee
    -- equateþ þose levels and confirmeþ þat þe goal is unchanged.
    generalise current value ty goal = do
      stuck <- computation value
      if not stuck
        then pure Nothing
        else do
          settleInstances checker
          pattern <- quote environment current value
          goalTerm <- quote environment current goal
          let (abstracted, found) = abstractTerms [pattern] goalTerm
              inner = extend current Nothing ty
          if not (or found)
            then pure Nothing
            else
              E.speculate (abstraction inner abstracted) >>= \case
                Nothing -> pure Nothing
                Just (result, keep) -> Just result <$ keep
      where
        abstraction inner abstracted = do
          requireUniverse environment inner =<< inferCore environment inner abstracted
          reinstated <- eval environment (define current Nothing value ty) abstracted
          E.unify (globals environment) (scopeContext current) reinstated goal
          eval environment inner abstracted
    computation = \case
      N.VNeutral neutral -> case N.neutralSpine neutral of
        (N.NGlobal name _, _) | Just Definition {definitionBody = DataConstructor {}} <- Map.lookup name (globals environment) -> pure False
        _ -> pure True
      _ -> pure False

requireUsed :: [MatchRow] -> Set.Set Int -> Elaboration ()
requireUsed rows used = case [matchRowId row | row <- rows, matchRowId row `Set.notMember` used] of
  [] -> pure ()
  index : _ -> E.failure ("case " ++ show (index + 1) ++ " is redundant")

-- wiþout rows, only a column of an empty family can still be split.
compileMatch :: ExpressionChecker -> K.Environment -> Names -> Scope -> [Column] -> [MatchRow] -> N.Value -> Elaboration (Term, Set.Set Int)
compileMatch checker environment names scope columns [] expected = do
  empty <- filterM (emptyColumn . columnType . snd) (zip [0 ..] columns)
  case empty of
    (index, _) : _ -> splitColumn checker environment names scope columns [] expected index Nothing
    [] -> E.failure "the match is not exhaustive"
  where
    -- a column is empty when its family haþ no constructor, or when its
    -- indices rule out every constructor.
    emptyColumn ty =
      familyOf environment ty >>= \case
        Nothing -> pure False
        Just split@Split {splitInfo, splitIndices} -> do
          patterns <- sequence <$> traverse (indexPattern environment) splitIndices
          case patterns of
            Just indexPatterns
              | any (not . isVariable) indexPatterns ->
                  allM
                    ( \(constructor, fields) -> do
                        let fieldValues = [N.VNeutral (N.NLocal (depth scope + position)) | position <- [0 .. length fields - 1]]
                        (== Just False) <$> constructorFits environment split indexPatterns constructor fieldValues
                    )
                    (inductiveConstructorInfo splitInfo)
            _ -> pure (null (inductiveConstructorInfo splitInfo))
    isVariable = \case
      IndexVariable _ -> True
      _ -> False
compileMatch checker environment names scope columns rows@(row : _) expected =
  case [(index, inner) | (index, pattern) <- zip [0 ..] (matchPatterns row), let inner = snd (unnamed pattern), refutable inner] of
    (index, PLiteral literal) : _ -> splitLiteral checker environment names scope columns rows expected index literal
    [] -> do
      let bindings =
            matchBindings row
              ++ [ (name, columnValue scope columnLevel, columnType)
                 | (pattern, Column {..}) <- zip (matchPatterns row) columns,
                   let (aliases, inner) = unnamed pattern,
                   name <- aliases ++ [variable | PVariable (Just variable) <- [inner]]
                 ]
      term <- bindAll scope bindings
      pure (term, Set.singleton (matchRowId row))
    (index, _) : _ -> splitColumn checker environment names scope columns rows expected index Nothing
  where
    refutable = \case
      PConstructor {} -> True
      PLiteral _ -> True
      _ -> False
    bindAll current [] = checkTerm checker current (matchBody row) expected
    bindAll current ((name, value, ty) : rest) = do
      annotation <- quote environment current ty
      valueTerm <- quote environment current value
      Let annotation valueTerm <$> bindAll (define current (Just name) value ty) rest

-- a literal row splitteþ its column in two: rows þat accept þe literal, and
-- rows þat accept any oþer value. `literal_case` chooseþ between þem.
splitLiteral :: ExpressionChecker -> K.Environment -> Names -> Scope -> [Column] -> [MatchRow] -> N.Value -> Int -> HostLiteral -> Elaboration (Term, Set.Set Int)
splitLiteral checker environment names scope columns rows expected index literal = do
  let Column level ty = columns !! index
      literalTy = N.VNeutral (N.NGlobal (literalType literal) [])
      value = columnValue scope level
  E.unify (globals environment) (scopeContext scope) ty literalTy
  kind <- inferCore environment scope =<< quote environment scope expected
  resultLevel <- requireUniverse environment scope kind
  -- an accepting row's names bind þe column; þe column becomeþ a wildcard.
  let accept row@MatchRow {..} = case unnamed (matchPatterns !! index) of
        (aliases, PLiteral written)
          | written == literal -> Just (settle row aliases)
          | otherwise -> Nothing
        (aliases, PVariable name) -> Just (settle row (aliases ++ maybe [] pure name))
        _ -> Nothing
      reject row = case snd (unnamed (matchPatterns row !! index)) of
        PLiteral written -> written /= literal
        _ -> True
      settle row bound = row {matchPatterns = replace (matchPatterns row), matchBindings = matchBindings row ++ [(name, value, ty) | name <- bound]}
      replace patterns = take index patterns ++ [PVariable Nothing] ++ drop (index + 1) patterns
  when (any (\row -> case snd (unnamed (matchPatterns row !! index)) of PConstructor {} -> True; _ -> False) rows) (E.failure "a constructor pattern cannot match a literal type")
  (yes, yesUsed) <- compileMatch checker environment names scope columns [accepted | Just accepted <- map accept rows] expected
  (no, noUsed) <- compileMatch checker environment names scope columns (filter reject rows) expected
  result <- quote environment scope expected
  typeTerm <- quote environment scope ty
  let chosen = applyArguments (Global H.literalCaseSymbol [resultLevel]) [(Implicit, typeTerm), (Implicit, result), (Explicit, Local (depth scope - level - 1)), (Explicit, Core.Literal (literalType literal) literal), (Explicit, yes), (Explicit, no)]
  pure (chosen, Set.union yesUsed noUsed)

-- the family of a column, wiþ its parameters and eliminator.
data Split = Split
  { splitLevels :: [Level],
    splitInfo :: InductiveInfo,
    splitParameters :: [N.Value],
    splitIndices :: [N.Value],
    splitEliminator :: SymbolId
  }

-- a column whose type is still a hole may be fixed by splitting a stuck
-- equation, as instance search doþ.
columnFamily :: K.Environment -> N.Value -> Elaboration Split
columnFamily environment ty =
  familyOf environment ty >>= \case
    Just split -> pure split
    Nothing ->
      E.approximate (globals environment) >>= \case
        True -> columnFamily environment ty
        False -> E.failure "a constructor pattern requireþ a value of an inductive type"

familyOf :: K.Environment -> N.Value -> Elaboration (Maybe Split)
familyOf environment ty =
  E.force (globals environment) ty >>= \case
    N.VNeutral neutral
      | (N.NGlobal family levels, arguments) <- N.neutralSpine neutral,
        Just Definition {definitionBody = TypeConstructor info} <- Map.lookup family (globals environment),
        let eliminator = inductionSymbol family,
        Just Definition {definitionBody = Eliminator _} <- Map.lookup eliminator (globals environment) ->
          pure (Just (Split levels info (map snd (take (inductiveParameterCount info) arguments)) (map snd (drop (inductiveParameterCount info) arguments)) eliminator))
    _ -> pure Nothing

-- the motive abstracteþ the split column from the expected type. recursion
-- supplieþ its own motive and records induction hypotheses for children.
splitColumn :: ExpressionChecker -> K.Environment -> Names -> Scope -> [Column] -> [MatchRow] -> N.Value -> Int -> Maybe (Term, Scope -> [(Int, Int)] -> Scope) -> Elaboration (Term, Set.Set Int)
splitColumn checker environment names scope columns rows expected index recursive = do
  let Column level ty = columns !! index
  Split {..} <- columnFamily environment ty
  eliminatorUniverses <- case Map.lookup splitEliminator (globals environment) of
    Just definition -> pure (definitionUniverses definition)
    Nothing -> E.failure "missing eliminator"
  levels <- mapM (const E.freshLevel) [1 .. eliminatorUniverses]
  parameterTerms <- traverse (quote environment scope) splitParameters
  -- indices þat are distinct locals are abstracted in place. oþerwise each
  -- index is a constructor pattern over distinct locals, unified by large
  -- elimination: þe motive computeþ þe goal where þe constructors agree.
  patterns <- traverse (indexPattern environment) splitIndices
  parameterLevels <- concat <$> traverse (\parameter -> map (\index -> depth scope - index - 1) . freeIndices <$> quote environment scope parameter) splitParameters
  let simple = [indexLevel | Just (IndexVariable indexLevel) <- patterns]
      inPlace = length simple == length splitIndices && length (nub simple) == length simple && level `notElem` simple
  unified <-
    if inPlace
      then pure Nothing
      else case sequence patterns of
        Nothing -> E.failure "matching needs each index of an indexed family to be a variable or a constructor applied to variables"
        Just indexPatterns -> do
          let leaves = concatMap patternLeaves indexPatterns
          unless (length (nub leaves) == length leaves && level `notElem` leaves) (E.failure "matching needs þe variables in þe indices of an indexed family to be distinct")
          bound <- allM (\leaf -> E.force (globals environment) (columnValue scope leaf) <&> \case N.VNeutral (N.NLocal same) -> same == leaf; _ -> False) leaves
          unless bound (E.failure "matching needs þe variables in þe indices of an indexed family to be inputs")
          when (maybe False (const True) recursive) (E.failure "recursion cannot yet match a value whose indices are constructors")
          pure (Just indexPatterns)
  let indexLevels = maybe simple (concatMap patternLeaves) unified
  -- an index variable þat a parameter also useþ would need axiom K, which
  -- stayeþ unprovable.
  when (any (`elem` parameterLevels) indexLevels) (E.failure "matching would equate an index wiþ a parameter, which needeþ axiom K")
  generalised <- case recursive of
    Nothing -> fmap catMaybes . forM (scopeRecursions scope) $ \Recursion {..} -> case recursionMemo of
      Just memo -> memoRecord environment scope memo (columnValue scope level) <&> fmap (recursionName,memo,)
      Nothing -> pure Nothing
    Just _ -> pure []
  -- inputs whose types mention þe indices or þe value are reverted into þe
  -- motive and rebound in each branch at þeir refined types, as `known` in
  -- `{yea, known ^ ...}` wiþ `known: (x p) = b` seeþ `(x p) = yea`. a split
  -- þat also carrieþ course-of-values records revertþ noþing.
  dependents <-
    if maybe False (const True) recursive || (null indexLevels && not (null generalised))
      then pure []
      else
        foldM
          ( \found candidate -> do
              let candidateType = K.contextTypes (scopeContext scope) !! (depth scope - candidate - 1)
              mentioned <- map (\index -> depth scope - index - 1) . freeIndices <$> quote environment scope candidateType
              bound <-
                E.force (globals environment) (columnValue scope candidate) <&> \case
                  N.VNeutral (N.NLocal same) -> same == candidate
                  _ -> False
              pure (if bound && any (`elem` (indexLevels ++ [level] ++ found)) mentioned then found ++ [candidate] else found)
          )
          []
          [candidate | candidate <- [0 .. depth scope - 1], candidate `notElem` (level : indexLevels), candidate > minimum (level : indexLevels)]
  motive <- case recursive of
    Just (motive, _) -> pure motive
    Nothing -> do
      domain <- quote environment scope ty
      -- þe motive keepeþ definitions by name, so each branch goal still
      -- nameþ þem.
      result <- quoteFolded environment scope expected
      if maybe False (const True) unified
        then do
          unless (null generalised) (E.failure "course-of-values recursion cannot match an indexed family")
          unifiedMotive environment scope level Split {..} levels parameterTerms (maybe [] id unified) dependents expected
        else
          if not (null indexLevels && null dependents)
            then do
              indexDomains <- forM indexLevels \indexLevel -> quote environment scope (K.contextTypes (scopeContext scope) !! (depth scope - indexLevel - 1))
              dependentDomains <- forM dependents \dependent -> quote environment scope (K.contextTypes (scopeContext scope) !! (depth scope - dependent - 1))
              let binders = indexLevels ++ [level] ++ dependents
                  abstracted = abstractLevels (depth scope) binders result
                  domains = zipWith (\position term -> abstractLevels (depth scope) (take position binders) term) [0 ..] (indexDomains ++ [domain] ++ dependentDomains)
                  (lambdaDomains, piDomains) = splitAt (length indexLevels + 1) domains
                  plicities = inductiveIndexPlicities splitInfo ++ [Explicit]
              unless (null generalised) (E.failure "course-of-values recursion cannot match an indexed family")
              pure (foldr (\(plicity, binderDomain) -> Core.Lambda plicity binderDomain) (foldr (Pi Explicit) abstracted piDomains) (zip plicities lambdaDomains))
            else do
              let abstracted = abstractLevels (depth scope) [level] result
              -- every enclosing recursion whose memo containeþ the matched value
              -- contributeþ a record binder; nested recursion needeþ all of them.
              let bindRecords _ [] = pure (shiftTerm (length generalised) abstracted)
                  bindRecords current ((_, memo, _) : rest) = do
                    record <- applyMemo environment current memo (N.VNeutral (N.NLocal (depth scope)))
                    recordType <- eval environment current record
                    Pi Explicit record <$> bindRecords (extend current Nothing recordType) rest
              Core.Lambda Explicit domain <$> bindRecords (extend scope Nothing ty) generalised
  let prefix = Apply Explicit (foldl (Apply Implicit) (Global splitEliminator levels) parameterTerms) motive
  prefixType <- inferCore environment scope prefix
  (applied, appliedType, used) <-
    foldM
      ( \(term, termType, used) (constructor, fields) ->
          E.force (globals environment) termType >>= \case
            N.VPi Explicit methodType codomain -> do
              (method, methodUsed) <- constructorMethod unified generalised dependents constructor fields methodType ty Split {..}
              methodValue <- eval environment scope method
              next <- E.instantiate (globals environment) codomain methodValue
              pure (Apply Explicit term method, next, Set.union used methodUsed)
            _ -> E.failure "invalid eliminator method type"
      )
      (prefix, prefixType, Set.empty)
      (inductiveConstructorInfo splitInfo)
  -- þe eliminator takeþ þe indices, þen þe matched value.
  let indexTargets = case unified of
        Just _ -> zip (inductiveIndexPlicities splitInfo) splitIndices
        Nothing -> zip (inductiveIndexPlicities splitInfo) (map (columnValue scope) indexLevels)
      targets = indexTargets ++ [(Explicit, columnValue scope level)] ++ [(Explicit, columnValue scope dependent) | dependent <- dependents]
  (target, targetType) <-
    foldM
      ( \(term, termType) (plicity, targetValue) ->
          E.force (globals environment) termType >>= \case
            N.VPi actual _ codomain
              | actual == plicity -> do
                  targetTerm <- quote environment scope targetValue
                  (Apply plicity term targetTerm,) <$> E.instantiate (globals environment) codomain targetValue
            _ -> E.failure "invalid eliminator target type"
      )
      (applied, appliedType)
      targets
  (term, resultType) <-
    foldM
      ( \(term, ty) (_, _, record) -> do
          recordValue <- eval environment scope record
          E.force (globals environment) ty >>= \case
            N.VPi Explicit _ codomain -> (Apply Explicit term record,) <$> E.instantiate (globals environment) codomain recordValue
            _ -> E.failure "invalid generalised motive"
      )
      (target, targetType)
      generalised
  case recursive of
    Nothing -> E.unify (globals environment) (scopeContext scope) resultType expected
    Just _ -> pure ()
  -- written index targets carry þeir own universe holes; checking þe whole
  -- application relateþ þem to þe family's parameters.
  when (maybe False (const True) unified) (() <$ inferCore environment scope term)
  pure (term, used)
  where
    constructorMethod unified generalised dependents constructor fields methodType columnTy Split {..} = do
      let selected = [row | row <- rows, keeps row]
          keeps row = case snd (unnamed (matchPatterns row !! index)) of
            PConstructor name _ -> name == constructor
            PLiteral _ -> False
            _ -> True
      bindFields scope methodType fields [] [] \current fieldLevels hypotheses branchType -> do
        let fieldValues = [N.VNeutral (N.NLocal fieldLevel) | fieldLevel <- fieldLevels]
        possible <- case unified of
          Just indexPatterns -> constructorPossible environment Split {..} indexPatterns constructor fieldValues
          Nothing -> pure True
        if not possible
          then -- þe motive computeþ þe trivial `[goal, goal]` here.
            E.force (globals environment) branchType >>= \case
              N.VPi Explicit trivial _ -> do
                trivialTerm <- quote environment current trivial
                pure (Core.Lambda Explicit trivialTerm (Local 0), Set.empty)
              _ -> E.failure "invalid impossible case"
          else do
            when (null selected) (E.failure ("the match is not exhaustive: missing " ++ symbolName constructor))
            let constructed = constructorValue constructor splitLevels splitParameters (zip (map fieldPlicity fields) fieldValues)
            rows' <- traverse (expandRow fields constructed columnTy) selected
            let fieldColumns = [Column fieldLevel (K.contextTypes (scopeContext current) !! (depth current - fieldLevel - 1)) | fieldLevel <- fieldLevels]
                columns' = take index columns ++ fieldColumns ++ drop (index + 1) columns
            -- in course-of-values recursion each direct recursive field's
            -- record is its hypothesis.
            let directHypotheses = [hypothesis | ((_, annotation, _), hypothesis) <- zip [field | field@(_, _, True) <- fields] hypotheses, direct annotation]
            case recursive of
              Just (_, enter) -> do
                -- recursion rebindeþ quantified inputs after the fields. þeir
                -- columns move by þe number of fields þat replaced þe split column.
                let inner = enter current hypotheses
                    moved position = if position < index then position else position + length fields - 1
                    quantified = case scopeRecursions inner of
                      recursion : _ -> recursionQuantified recursion
                      [] -> []
                    rebind entered ty = bindQuantified entered ty [(moved position, plicity) | (position, plicity) <- quantified] columns' rows'
                case scopeRecursions inner of
                  Recursion {recursionName, recursionMemo = Just _} : _ -> do
                    now <-
                      E.force (globals environment) branchType >>= \case
                        N.VRecordType [("below", _), ("now", now)] -> pure now
                        _ -> E.failure "invalid memoised motive"
                    let entries = [(N.VNeutral (N.NLocal field), (hypothesis, [])) | (field, hypothesis) <- directHypotheses]
                    (body, used) <- rebind (remember recursionName entries inner) now
                    let below = Record [(childName child, Local (depth current - hypothesis - 1)) | (child, (_, hypothesis)) <- zip [0 ..] directHypotheses]
                    pure (Record [("below", below), ("now", body)], used)
                  _ -> rebind inner branchType
              Nothing -> case generalised of
                [] -> revert current branchType dependents columns' rows'
                -- þe carried record of þe split value now nameþ þe record of
                -- each recursive field.
                records ->
                  let bindRecords entered ty [] = compileMatch checker environment names entered columns' rows' ty
                      bindRecords entered ty ((name, _, _) : rest) =
                        E.force (globals environment) ty >>= \case
                          N.VPi Explicit recordType codomain -> do
                            recordTerm <- quote environment entered recordType
                            let recordLevel = depth entered
                                afterRecord = extend entered Nothing recordType
                                entries =
                                  (constructed, (recordLevel, []))
                                    : [(N.VNeutral (N.NLocal field), (recordLevel, ["below", childName child])) | (child, (field, _)) <- zip [0 ..] directHypotheses]
                            resultType <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal recordLevel))
                            (body, used) <- bindRecords (remember name entries afterRecord) resultType rest
                            pure (Core.Lambda Explicit recordTerm body, used)
                          _ -> E.failure "invalid generalised motive"
                   in bindRecords current branchType records
    direct = \case
      Pi {} -> False
      _ -> True
    remember name entries current =
      current {scopeRecursions = [if recursionName recursion == name then recursion {recursionMemo = (\memo -> memo {memoEntries = entries ++ memoEntries memo}) <$> recursionMemo recursion} else recursion | recursion <- scopeRecursions current]}
    -- each reverted input is rebound under its name at its refined type; a
    -- column þat was þat input followeþ it.
    revert current ty [] columns' rows' = compileMatch checker environment names current columns' rows' ty
    revert current ty (dependent : rest) columns' rows' =
      E.force (globals environment) ty >>= \case
        N.VPi Explicit domain codomain -> do
          domainTerm <- quote environment current domain
          let rebound = depth current
              name = scopeNames scope !! (depth scope - dependent - 1)
              moved = [if columnLevel == dependent then Column rebound domain else column | column@(Column columnLevel _) <- columns']
          resultType <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal rebound))
          (body, used) <- revert (extend current name domain) resultType rest moved rows'
          pure (Core.Lambda Explicit domainTerm body, used)
        _ -> E.failure "invalid reverted motive"
    bindQuantified current ty [] columns' rows' = compileMatch checker environment names current columns' rows' ty
    bindQuantified current ty ((column, plicity) : rest) columns' rows' =
      E.force (globals environment) ty >>= \case
        N.VPi actual domain codomain | actual == plicity -> do
          domainTerm <- quote environment current domain
          let level = depth current
              -- the column index shifteþ when the split column became fields.
              replaced = [if position == column then Column level domain else existing | (position, existing) <- zip [0 ..] columns']
          resultType <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal level))
          (body, used) <- bindQuantified (extend current Nothing domain) resultType rest replaced rows'
          pure (Core.Lambda plicity domainTerm body, used)
        _ -> E.failure "invalid recursive motive"
    fieldPlicity (plicity, _, _) = plicity
    bindFields current ty [] levels hypotheses continue = continue current (reverse levels) (reverse hypotheses) ty
    bindFields current ty ((plicity, _, recursiveField) : rest) levels hypotheses continue =
      E.force (globals environment) ty >>= \case
        N.VPi actual domain codomain | actual == plicity -> do
          domainTerm <- quote environment current domain
          let fieldLevel = depth current
              afterField = extend current Nothing domain
          next <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal fieldLevel))
          if recursiveField
            then
              E.force (globals environment) next >>= \case
                N.VPi Explicit hypothesisDomain hypothesisCodomain -> do
                  hypothesisTerm <- quote environment afterField hypothesisDomain
                  let hypothesisLevel = depth afterField
                  next' <- E.instantiate (globals environment) hypothesisCodomain (N.VNeutral (N.NLocal hypothesisLevel))
                  (body, used) <- bindFields (extend afterField Nothing hypothesisDomain) next' rest (fieldLevel : levels) ((fieldLevel, hypothesisLevel) : hypotheses) continue
                  pure (Core.Lambda plicity domainTerm (Core.Lambda Explicit hypothesisTerm body), used)
                _ -> E.failure "invalid induction hypothesis"
            else do
              (body, used) <- bindFields afterField next rest (fieldLevel : levels) hypotheses continue
              pure (Core.Lambda plicity domainTerm body, used)
        _ -> E.failure "invalid eliminator method"
    expandRow fields constructed columnTy row@MatchRow {..} = do
      let (aliases, pattern) = unnamed (matchPatterns !! index)
      (subpatterns, bound) <- case pattern of
        PConstructor _ subpatterns -> (,aliases) <$> assignFields fields subpatterns
        PVariable name -> pure (map (const (PVariable Nothing)) fields, aliases ++ maybe [] pure name)
        _ -> E.failure "a literal pattern cannot match an inductive type"
      pure row {matchPatterns = take index matchPatterns ++ subpatterns ++ drop (index + 1) matchPatterns, matchBindings = matchBindings ++ [(binding, constructed, columnTy) | binding <- bound]}

-- index unification ----------------------------------------------------

-- an index in constructor form over variables, as `n s` or `a ‥ empty`.
data IndexPattern = IndexVariable Int | IndexConstructor SymbolId [IndexPattern]

indexPattern :: K.Environment -> N.Value -> Elaboration (Maybe IndexPattern)
indexPattern environment value =
  E.force (globals environment) value >>= \case
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
  E.force (globals environment) value <&> \case
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
  ty <- E.evaluate (globals environment) (K.Context [] []) term
  result <-
    foldM
      ( \current value ->
          E.force (globals environment) current >>= \case
            N.VPi _ _ codomain -> E.instantiate (globals environment) codomain value
            _ -> E.failure "invalid constructor type"
      )
      ty
      (splitParameters ++ fieldValues)
  E.force (globals environment) result >>= \case
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
  goalTerm <- quoteFolded environment scope expected
  dependentDomains <- forM dependents (quote environment scope . contextType scope)
  let reverted =
        foldr
          (Pi Explicit)
          (abstractLevels (depth scope) dependents goalTerm)
          (zipWith (\position term -> abstractLevels (depth scope) (take position dependents) term) [0 ..] dependentDomains)
  goalLevel <- requireUniverse environment scope =<< inferCore environment scope reverted
  baseType <- inferCore environment scope (foldl (Apply Implicit) (Global splitEliminator levels) parameterTerms)
  E.force (globals environment) baseType >>= \case
    N.VPi Explicit motiveType _ -> bindIndices reverted goalLevel scope motiveType (inductiveIndexPlicities splitInfo) []
    _ -> E.failure "invalid eliminator motive"
  where
    bindIndices reverted goalLevel current ty plicities indexLevels =
      E.force (globals environment) ty >>= \case
        N.VPi actual domain codomain
          | plicity : rest <- plicities,
            actual == plicity -> do
              domainTerm <- quote environment current domain
              let indexLevel = depth current
              next <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal indexLevel))
              Core.Lambda plicity domainTerm <$> bindIndices reverted goalLevel (extend current Nothing domain) next rest (indexLevel : indexLevels)
          | [] <- plicities,
            actual == Explicit -> do
              domainTerm <- quote environment current domain
              generalised <- eval environment current (Pi Explicit domainTerm (Sort goalLevel))
              caseTerm <- unify reverted current (zip (reverse indexLevels) indexPatterns) [] generalised
              pure (Core.Lambda Explicit domainTerm (Apply Explicit (shiftTerm 1 caseTerm) (Local 0)))
        _ -> E.failure "invalid eliminator motive"
    -- `result` is `[value type, *]` at þe current targets.
    unify reverted current [] substitution result =
      E.force (globals environment) result >>= \case
        N.VPi Explicit valueDomain _ -> do
          valueDomainTerm <- quote environment current valueDomain
          let valueLevel = depth current
              replace outer
                | outer == level = N.VNeutral (N.NLocal valueLevel)
                | Just value <- lookup outer substitution = value
                | otherwise = columnValue scope outer
              values = map replace (reverse [0 .. depth scope - 1])
          goal <- E.evaluate (globals environment) (K.Context values (K.contextTypes (scopeContext scope))) reverted
          Core.Lambda Explicit valueDomainTerm <$> quote environment (extend current Nothing valueDomain) goal
        _ -> E.failure "invalid unified motive"
    unify reverted current ((target, IndexVariable leaf) : rest) substitution result =
      unify reverted current rest ((leaf, N.VNeutral (N.NLocal target)) : substitution) result
    unify reverted current ((target, IndexConstructor constructor subpatterns) : rest) substitution result = do
      let targetType = contextType current target
      Split {splitLevels = _, splitInfo = info, splitParameters = parameters, splitIndices = indices, splitEliminator = eliminator} <- columnFamily environment targetType
      unless (null indices) (E.failure "an index pattern cannot match a value of an indexed family")
      universes <- maybe (E.failure "missing eliminator") (pure . definitionUniverses) (Map.lookup eliminator (globals environment))
      fresh <- mapM (const E.freshLevel) [1 .. universes]
      parameterTerms' <- traverse (quote environment current) parameters
      targetTypeTerm <- quote environment current targetType
      resultTerm <- quote environment current result
      let motive = Core.Lambda Explicit targetTypeTerm (abstractLevels (depth current) [target] resultTerm)
          prefix = Apply Explicit (foldl (Apply Implicit) (Global eliminator fresh) parameterTerms') motive
      prefixType <- inferCore environment current prefix
      (applied, _) <-
        foldM
          ( \(term, termType) (candidate, fields) ->
              E.force (globals environment) termType >>= \case
                N.VPi Explicit methodType codomain -> do
                  method <- bindMethod environment current methodType fields [] \inner fieldLevels branchType ->
                    if candidate == constructor
                      then unify reverted inner (zip fieldLevels subpatterns ++ rest) substitution branchType
                      else trivial inner branchType
                  methodValue <- eval environment current method
                  next <- E.instantiate (globals environment) codomain methodValue
                  pure (Apply Explicit term method, next)
                _ -> E.failure "invalid eliminator method type"
          )
          (prefix, prefixType)
          (inductiveConstructorInfo info)
      pure (Apply Explicit applied (Local (depth current - target - 1)))
    trivial current result =
      E.force (globals environment) result >>= \case
        N.VPi Explicit valueDomain _ -> do
          valueDomainTerm <- quote environment current valueDomain
          goal <- quote environment (extend current Nothing valueDomain) expected
          pure (Core.Lambda Explicit valueDomainTerm (Pi Explicit goal (shiftTerm 1 goal)))
        _ -> E.failure "invalid unified motive"

-- bindeþ a method's fields, each recursive one followed by its hypoþesis.
bindMethod :: K.Environment -> Scope -> N.Value -> [(Plicity, Term, Bool)] -> [Int] -> (Scope -> [Int] -> N.Value -> Elaboration Term) -> Elaboration Term
bindMethod _ current ty [] levels continue = continue current (reverse levels) ty
bindMethod environment current ty ((plicity, _, recursiveField) : rest) levels continue =
  E.force (globals environment) ty >>= \case
    N.VPi actual domain codomain | actual == plicity -> do
      domainTerm <- quote environment current domain
      let fieldLevel = depth current
          afterField = extend current Nothing domain
      next <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal fieldLevel))
      if recursiveField
        then
          E.force (globals environment) next >>= \case
            N.VPi Explicit hypothesisDomain hypothesisCodomain -> do
              hypothesisTerm <- quote environment afterField hypothesisDomain
              next' <- E.instantiate (globals environment) hypothesisCodomain (N.VNeutral (N.NLocal (depth afterField)))
              body <- bindMethod environment (extend afterField Nothing hypothesisDomain) next' rest (fieldLevel : levels) continue
              pure (Core.Lambda plicity domainTerm (Core.Lambda Explicit hypothesisTerm body))
            _ -> E.failure "invalid induction hypothesis"
        else Core.Lambda plicity domainTerm <$> bindMethod environment afterField next rest (fieldLevel : levels) continue
    _ -> E.failure "invalid eliminator method"

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
abstractLevels depthNow levels = go 0
  where
    count = length levels
    go bound = \case
      Local index
        | index < bound -> Local index
        | Just position <- elemIndex (depthNow - (index - bound) - 1) levels -> Local (bound + count - 1 - position)
        | otherwise -> Local (index + count)
      term -> runIdentity (mapChildren (\binders -> Identity . go (bound + binders)) term)

-- structural recursion ---------------------------------------------------

-- recursive fields are named in order; zero padding keepeþ þe record sorted.
childName :: Int -> String
childName index = "child" ++ replicate (3 - length (show index)) '0' ++ show index

-- þe record of a known descendant, reached from its local.
memoRecord :: K.Environment -> Scope -> Memo -> N.Value -> Elaboration (Maybe Term)
memoRecord environment scope Memo {memoEntries} value = do
  wanted <- eraseGlobalLevels <$> quote environment scope value
  known <- traverse (\(entry, place) -> (,place) . eraseGlobalLevels <$> quote environment scope entry) memoEntries
  pure case lookup wanted known of
    Just (level, path) -> Just (foldl Project (Local (depth scope - level - 1)) path)
    Nothing -> Nothing

-- þe memoised motive applied to a value, quoted in þe given scope.
applyMemo :: K.Environment -> Scope -> Memo -> N.Value -> Elaboration Term
applyMemo environment scope Memo {memoType} value =
  E.force (globals environment) memoType >>= \case
    N.VLambda _ _ closure -> E.instantiate (globals environment) closure value >>= quote environment scope
    _ -> E.failure "invalid memoised motive"

-- a recursive definition's inputs and clauses. named lambda binders become
-- variable columns; a final case function or a match on inputs supplieþ rows.
data Clauses = Clauses
  { clauseScope :: Scope,
    -- every input in order: its level, plicity, and type.
    clauseInputs :: [(Int, Plicity, N.Value)],
    clauseResult :: N.Value,
    clauseRows :: [MatchRow],
    clauseWrittenRows :: [MatchRow],
    -- columns a `match` scrutiniseþ by input name.
    clauseAliases :: [(Int, String)]
  }

gatherClauses :: ExpressionChecker -> K.Environment -> Names -> Scope -> N.Value -> Expression -> Elaboration Clauses
gatherClauses checker environment names start annotation body = go start annotation body [] []
  where
    go scope ty source inputs columnNames =
      E.force (globals environment) ty >>= \case
        N.VPi plicity domain codomain
          | Lambda (Binder {..} : rest) inner <- source,
            binderPlicity == plicity -> do
              forM_ binderAnnotation \annotation -> do
                written <- annotationType checker scope annotation
                E.unify (globals environment) (scopeContext scope) written domain
              bind plicity binderName domain codomain (Lambda rest inner) [maybe Wildcard Name binderName | plicity == Explicit]
          | Lambda [] inner <- source -> go scope ty inner inputs columnNames
          -- an unwritten implicit input belongeþ to a following lambda or case
          -- function. a match keepeþ the rest of the type as its result.
          | plicity == Implicit,
            bindsInputs source ->
              bind Implicit Nothing domain codomain source []
          | Cases rows <- source,
            rowArity rows > 0 ->
              casesColumns rows
        resultType -> finish resultType
      where
        bindsInputs = \case
          Lambda _ _ -> True
          Cases _ -> True
          _ -> False
        bind plicity name domain codomain next newColumns = do
          let level = depth scope
          resultType <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal level))
          go (extend scope name domain) resultType next ((level, plicity, domain) : inputs) (newColumns ++ columnNames)
        casesColumns rows = do
          (current, added, resultType) <- bindCaseInputs environment scope (rowArity rows) ty
          resolved <- matchRows environment names [Row (reverse columnNames ++ rowPatterns) rowBody | Row {..} <- rows]
          pure (Clauses current (reverse inputs ++ added) resultType resolved resolved [])
        finish resultType = do
          let columns = reverse columnNames
              unwrap = \case
                Lambda [] inner -> unwrap inner
                other -> other
          (rows, writtenRows, aliases) <- case unwrap source of
            Match scrutinees matchRows'
              | Just positions <- traverse (scrutineeColumn columns) scrutinees -> do
                  requireRowArity matchRows'
                  requireMatchArity scrutinees matchRows'
                  resolved <- matchRows environment names matchRows'
                  defaults <- traverse (resolvePattern environment names) columns
                  projected <- projectRows environment [[index | (index, input) <- zip [0 ..] positions, input == position] | position <- [0 .. length columns - 1]] defaults resolved
                  pure
                    ( projected,
                      resolved,
                      [(position, input) | position <- nub positions, Name input <- [columns !! position]]
                    )
            other -> do
              resolved <- matchRows environment names [Row columns other]
              pure (resolved, resolved, [])
          pure (Clauses scope (reverse inputs) resultType rows writtenRows aliases)
    scrutineeColumn columnNames = \case
      Name name -> lookup (Name name) (zip columnNames [0 :: Int ..]) >>= \position -> if name == "_" then Nothing else Just position
      _ -> Nothing

-- `let f:annotation ≔ body` whose body nameþ `f`. the recursion is compiled
-- to the eliminator of one structurally decreasing input.
elaborateRecursive :: ExpressionChecker -> K.Environment -> Names -> Scope -> String -> N.Value -> Expression -> Elaboration Term
elaborateRecursive checker environment names start name annotation body = do
  Clauses {..} <- gatherClauses checker environment names start annotation body
  let rows = [row {matchPatterns = [maybe pattern (`PNamed` pattern) (lookup position clauseAliases) | (position, pattern) <- zip [0 ..] (matchPatterns row)]} | row <- clauseRows]
  let explicitInputs = [(level, ty) | (level, Explicit, ty) <- clauseInputs]
      scope = clauseScope
  families <- traverse (familyOf environment . snd) explicitInputs
  let positions =
        [ position
        | (position, Just Split {splitInfo}) <- zip [0 ..] families,
          null (inductiveIndexPlicities splitInfo)
        ]
      -- candidate checking useþ the same local bindings and induction evidence
      -- as expression checking. failed trials cannot influence later choices.
      select previous [] = maybe (E.failure ("'" ++ name ++ "' needs a structurally decreasing input")) E.raise previous
      select previous ((position, deep) : rest) =
        E.trial (compile position deep) >>= \case
          Right (term, commit) -> commit >> pure term
          Left failure -> select (previous <|> Just failure) rest
      compile position deep = do
        let (structuralLevel, structuralType) = explicitInputs !! position
        dependencies <- freeIndices <$> quote environment scope structuralType
        when (any (\(level, plicity, _) -> plicity == Implicit && level > structuralLevel) clauseInputs) (E.failure "implicit inputs after the structural input are not supported")
        let fixed level plicity = level < structuralLevel && (plicity == Implicit || (depth scope - level - 1) `elem` dependencies)
            roles = [if level == structuralLevel then Structural else if fixed level Explicit then Fixed level else Quantified | (level, _) <- explicitInputs]
            quantified = [(level, plicity) | (level, plicity, _) <- clauseInputs, level /= structuralLevel, not (fixed level plicity)]
            columnOf level = length [() | (other, Explicit, _) <- clauseInputs, other < level]
        -- the motive rebindeþ quantified inputs in order after the matched value.
        resultMotive <- recursiveMotive environment scope annotation clauseInputs structuralLevel (map fst quantified)
        (motive, memo) <-
          if deep
            then do
              memoMotive <- memoisedMotive environment scope structuralType resultMotive
              memoValue <- eval environment scope memoMotive
              pure (memoMotive, Just (Memo memoValue []))
            else pure (resultMotive, Nothing)
        let columns = [Column level ty | (level, ty) <- explicitInputs]
            recursion = Recursion name roles [(columnOf level, plicity) | (level, plicity) <- quantified] [] memo
            enter current hypotheses = current {scopeRecursions = recursion {recursionHypotheses = hypotheses} : scopeRecursions current}
        (split, used) <- splitColumn checker environment names scope columns rows clauseResult position (Just (motive, enter))
        requireUsed clauseWrittenRows used
        let result = if deep then Project split "now" else split
            applied = foldl (\term (level, plicity) -> Apply plicity term (Local (depth scope - level - 1))) result quantified
        appliedType <- inferCore environment scope applied
        E.unify (globals environment) (scopeContext scope) appliedType clauseResult
        wrapInputs environment clauseInputs applied
  select Nothing [(position, deep) | deep <- [False, True], position <- positions]

-- walk the annotation again wiþ the matched input and quantified inputs
-- replaced by fresh binders; fixed inputs keep their outer locals.
recursiveMotive :: K.Environment -> Scope -> N.Value -> [(Int, Plicity, N.Value)] -> Int -> [Int] -> Elaboration Term
recursiveMotive environment scope annotation inputs structuralLevel quantified = do
  let outer = depth scope
      structuralBinder = outer
  (structuralDomain, binders, result) <- walk annotation inputs (structuralBinder + 1) Nothing []
  pure (Core.Lambda Explicit structuralDomain (foldr (\(plicity, domain) term -> Pi plicity domain term) result binders))
  where
    walk ty [] next domain binders = do
      result <- E.quote (globals environment) next ty
      case domain of
        Just structuralDomain -> pure (structuralDomain, reverse binders, result)
        Nothing -> E.failure "missing structural input"
    walk ty ((level, plicity, _) : rest) next domain binders =
      E.force (globals environment) ty >>= \case
        N.VPi _ inputDomain codomain
          | level == structuralLevel -> do
              domainTerm <- E.quote (globals environment) (depth scope) inputDomain
              continue <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal (depth scope)))
              walk continue rest next (Just domainTerm) binders
          | level `elem` quantified -> do
              domainTerm <- E.quote (globals environment) next inputDomain
              continue <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal next))
              walk continue rest (next + 1) domain ((plicity, domainTerm) : binders)
          | otherwise -> do
              continue <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal level))
              walk continue rest next domain binders
        _ -> E.failure "invalid recursive annotation"

-- `[x: T, r{below: Below x, now: P x}]`. `Below` eliminateþ into types: each
-- constructor's record holdeþ, per recursive field, þat field's own record.
-- function fields contribute no entry.
memoisedMotive :: K.Environment -> Scope -> N.Value -> Term -> Elaboration Term
memoisedMotive environment scope structuralType resultMotive = do
  Split {..} <- columnFamily environment structuralType
  domain <- quote environment scope structuralType
  universes <- maybe (E.failure "missing eliminator") (pure . definitionUniverses) (Map.lookup splitEliminator (globals environment))
  levels <- mapM (const E.freshLevel) [1 .. universes]
  belowLevel <- E.freshLevel
  parameterTerms <- traverse (quote environment scope) splitParameters
  let prefix = Apply Explicit (foldl (Apply Implicit) (Global splitEliminator levels) parameterTerms) (Core.Lambda Explicit domain (Sort belowLevel))
  prefixType <- inferCore environment scope prefix
  (applied, _) <-
    foldM
      ( \(term, termType) (_, fields) ->
          E.force (globals environment) termType >>= \case
            N.VPi Explicit methodType codomain -> do
              method <- belowMethod scope methodType fields []
              methodValue <- eval environment scope method
              next <- E.instantiate (globals environment) codomain methodValue
              pure (Apply Explicit term method, next)
            _ -> E.failure "invalid eliminator method type"
      )
      (prefix, prefixType)
      (inductiveConstructorInfo splitInfo)
  let below = Apply Explicit (shiftTerm 1 applied) (Local 0)
      now = Apply Explicit (shiftTerm 1 resultMotive) (Local 0)
  let motive = Core.Lambda Explicit domain (Core.RecordType [("below", below), ("now", now)])
  _ <- inferCore environment scope motive
  pure motive
  where
    -- bind þe fields and þeir type-valued hypotheses, þen build þe record.
    belowMethod current _ [] children = do
      entries <- forM (zip [0 :: Int ..] (reverse children)) \(index, (field, hypothesis)) -> do
        now <- applyResult (N.VNeutral (N.NLocal field))
        nowTerm <- quote environment current now
        pure (childName index, Core.RecordType [("below", Local (depth current - hypothesis - 1)), ("now", nowTerm)])
      pure (Core.RecordType entries)
    belowMethod current ty ((plicity, annotation, recursive) : rest) children =
      E.force (globals environment) ty >>= \case
        N.VPi actual domain codomain | actual == plicity -> do
          domainTerm <- quote environment current domain
          let fieldLevel = depth current
              afterField = extend current Nothing domain
          next <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal fieldLevel))
          if recursive
            then
              E.force (globals environment) next >>= \case
                N.VPi Explicit hypothesisDomain hypothesisCodomain -> do
                  hypothesisTerm <- quote environment afterField hypothesisDomain
                  let hypothesisLevel = depth afterField
                  next' <- E.instantiate (globals environment) hypothesisCodomain (N.VNeutral (N.NLocal hypothesisLevel))
                  -- only a direct recursive field haþ a record of its own.
                  let direct = case annotation of
                        Pi {} -> False
                        _ -> True
                  body <- belowMethod (extend afterField Nothing hypothesisDomain) next' rest (if direct then (fieldLevel, hypothesisLevel) : children else children)
                  pure (Core.Lambda plicity domainTerm (Core.Lambda Explicit hypothesisTerm body))
                _ -> E.failure "invalid induction hypothesis"
            else Core.Lambda plicity domainTerm <$> belowMethod afterField next rest children
        _ -> E.failure "invalid eliminator method"
    applyResult argument =
      eval environment scope resultMotive >>= \case
        N.VLambda _ _ closure -> E.instantiate (globals environment) closure argument
        _ -> E.failure "invalid recursive motive"

-- `children f arguments` becomeþ the hypothesis applied to quantified inputs.
recursiveCall :: ExpressionChecker -> K.Environment -> Scope -> Recursion -> [Argument] -> Elaboration (Term, N.Value)
recursiveCall checker environment scope Recursion {..} arguments = do
  unless (all ((== Explicit) . argumentPlicity) arguments) (E.failure "a recursive call cannot supply implicit arguments")
  let explicit = map argumentExpression arguments
  unless (length explicit >= length recursionRoles) (E.failure "a recursive call must supply every explicit input")
  passed <-
    fmap concat . sequence $
      [ case role of
          Structural -> pure []
          Quantified -> pure [Argument Explicit argument]
          Fixed level -> do
            value <- localLevel argument
            unless (value == Just level) (E.failure "a recursive call must pass fixed inputs unchanged")
            pure []
      | (role, argument) <- zip recursionRoles explicit
      ]
  let rest = passed ++ map (Argument Explicit) (drop (length recursionRoles) explicit)
      structural = [argument | (Structural, argument) <- zip recursionRoles explicit]
  case (recursionMemo, structural) of
    (Just memo, [argument]) -> do
      value <- inferStructural argument
      memoRecord environment scope memo value >>= \case
        Just record -> do
          recordType <- inferCore environment scope record
          E.force (globals environment) recordType >>= \case
            N.VRecordType [("below", _), ("now", now)] -> applyTerm checker scope (Project record "now") now rest []
            _ -> E.failure "invalid memoised motive"
        Nothing -> E.failure "a recursive call must pass a descendant of the matched input"
    _ -> directCall rest structural
  where
    inferStructural argument = do
      (term, _) <- inferTerm checker scope argument
      eval environment scope term >>= E.force (globals environment)
    directCall rest structural = do
      value <- case structural of
        [argument] -> inferStructural argument
        _ -> E.failure "invalid recursive call"
      (hypothesis, childArguments) <- case value of
        N.VNeutral neutral
          | (N.NLocal level, arguments) <- N.neutralSpine neutral,
            Just hypothesis <- lookup level recursionHypotheses ->
              pure (hypothesis, arguments)
        _ -> E.failure "a recursive call must pass a direct child of the matched input"
      -- a function child's hypothesis first takeþ þe child's inputs.
      arguments <- traverse (\(plicity, value) -> (plicity,) <$> quote environment scope value) childArguments
      let term = applyArguments (Local (depth scope - hypothesis - 1)) arguments
      ty <- inferCore environment scope term
      applyTerm checker scope term ty rest []
    localLevel argument =
      inferStructural argument <&> \case
        N.VNeutral (N.NLocal level) -> Just level
        _ -> Nothing
