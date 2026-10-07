-- | pattern matrices lowered to eliminators: coverage, splitting, and
-- literal rows.
module Tung.Dependent.Source.Pattern.Match
  ( constructorBinder,
    constructorNamed,
    resolvePattern,
    rowArity,
    matchRows,
    requireRowArity,
    requireMatchArity,
    projectRows,
    checkCases,
    wrapInputs,
    bindCaseInputs,
    checkMatch,
    requireUsed,
    splitColumn,
  )
where

import Control.Monad (filterM, foldM, forM, forM_, unless, when)
import Data.Bifunctor (first)
import Data.Foldable (foldrM)
import Data.Functor ((<&>))
import Data.List (nub, nubBy)
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
import Tung.Dependent.Source.Pattern.Common
import Tung.Dependent.Source.Pattern.Index
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core
import Tung.Identity (SymbolId (..))
import Tung.Primitive (naturalSuccessorId, naturalZeroId)

type Elaboration = E.Elaboration

-- the names a column pattern bindeth to the whole value, and the pattern beneath.
unnamed :: PatternTree -> ([String], PatternTree)
unnamed = \case
  PNamed name pattern -> let (names, inner) = unnamed pattern in (name : names, inner)
  pattern -> ([], pattern)

constructorBinder :: K.Environment -> Names -> Binder -> Bool
constructorBinder environment names Binder {binderPlicity = Explicit, binderName = Just name, binderAnnotation = Nothing} =
  maybe False (const True) (constructorNamed environment names name)
constructorBinder _ _ _ = False

constructorNamed :: K.Environment -> Names -> String -> Maybe SymbolId
constructorNamed environment names name = do
  identity <- lookupName name names >>= bindingSymbol
  Definition {definitionBody = DataConstructor _ _} <- Map.lookup identity (globals environment)
  pure identity

-- a name that is not a constructor bindeth a variable, even when it shadoweth
-- a local or global value.
resolvePattern :: K.Environment -> Names -> Expression -> Elaboration PatternTree
resolvePattern environment names = \case
  Name name | Just (AmbiguousName modules) <- lookupName name names -> E.failure (ambiguousName name modules)
  Wildcard -> pure (PVariable Nothing)
  -- a natural literal is `0` or the successor of its predecessor.
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
  -- a row bindeth each name once.
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

-- each group containeth all written columns that denote one input. their
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

-- explicit inputs become columns; an implicit product before them gaineth an
-- unnamed binder, as with an ordinary lambda.
checkCases :: ExpressionChecker -> Scope -> [Row] -> N.Value -> Elaboration Term
checkCases checker@ExpressionChecker {checkerEnvironment = environment, checkerNames = names} scope rows expected = do
  resolved <- matchRows environment names rows
  (current, inputs, resultType) <- bindCaseInputs scope (rowArity rows) expected
  let columns = [Column level domain | (level, Explicit, domain) <- inputs]
  (term, used) <- compileMatch checker current columns resolved resultType
  requireUsed resolved used
  wrapInputs inputs term

-- domains are quoted at their original binder depth after body checking,
-- so inferred holes need no parallel list of quoted annotations.
wrapInputs :: [(Int, Plicity, N.Value)] -> Term -> Elaboration Term
wrapInputs inputs term = foldrM wrap term inputs
  where
    wrap (level, plicity, domain) body = do
      annotation <- E.quote level domain
      pure (Core.Lambda plicity annotation body)

-- consume one product spine for ordinary and recursive case functions.
-- implicit inputs gain anonymous locals without consuming written patterns.
bindCaseInputs :: Scope -> Int -> N.Value -> Elaboration (Scope, [(Int, Plicity, N.Value)], N.Value)
bindCaseInputs start count expected = go start count expected []
  where
    go current 0 ty inputs = pure (current, reverse inputs, ty)
    go current remaining ty inputs =
      E.force ty >>= \case
        N.VPi plicity domain codomain -> do
          let level = depth current
              remaining' = if plicity == Explicit then remaining - 1 else remaining
          resultType <- E.instantiate codomain (N.VNeutral (N.NLocal level))
          go (extend current Nothing domain) remaining' resultType ((level, plicity, domain) : inputs)
        _ -> E.failure "a case function needs a function type with one input per pattern"

-- a scrutinee that is already a local is matched in place, so the result
-- type may depend on it. other scrutinees are bound first.
checkMatch :: ExpressionChecker -> Scope -> [Expression] -> [Row] -> N.Value -> Elaboration Term
checkMatch checker@ExpressionChecker {checkerEnvironment = environment, checkerNames = names} scope scrutinees rows expected = do
  resolved <- matchRows environment names rows
  requireMatchArity scrutinees rows
  bindScrutinees scope scrutinees [] expected \current columns goal -> do
    let distinct = nubBy (\left right -> columnLevel left == columnLevel right) columns
        levels = map columnLevel distinct
        groups = [[index | (index, column) <- zip [0 ..] columns, columnLevel column == level] | level <- levels]
    projected <- projectRows environment groups (map (const (PVariable Nothing)) distinct) resolved
    (term, used) <- compileMatch checker current distinct projected goal
    requireUsed resolved used
    pure term
  where
    bindScrutinees current [] columns goal continue = continue current (reverse columns) goal
    bindScrutinees current (scrutinee : remaining) columns goal continue = do
      (term, ty) <- inferTerm checker current scrutinee
      value <- eval current term >>= E.force
      annotation <- quote current ty
      let level = depth current
      case value of
        N.VNeutral (N.NLocal local) -> bindScrutinees current remaining (Column local ty : columns) goal continue
        _ ->
          generalise current value ty goal >>= \case
            -- the computed scrutinee becometh an input, so each row seeth its
            -- constructor in the goal, as agda's `with` doth.
            Just abstracted -> do
              body <- bindScrutinees (extend current Nothing ty) remaining (Column level ty : columns) abstracted continue
              pure (Apply Explicit (Core.Lambda Explicit annotation body) term)
            Nothing -> Let annotation term <$> bindScrutinees (define current Nothing value ty) remaining (Column level ty : columns) goal continue
    -- the goal over a new input in place of each occurrence of a stuck
    -- computation. constructors and literals are not abstracted, nor is a
    -- goal that doth not mention the value or would be ill-typed without it.
    -- occurrences match up to universe levels; reinstating the scrutinee
    -- equateth those levels and confirmeth that the goal is unchanged.
    generalise current value ty goal = do
      stuck <- computation value
      if not stuck
        then pure Nothing
        else do
          settleInstances checker
          pattern <- quote current value
          goalTerm <- quote current goal
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
          requireUniverse inner =<< inferCore inner abstracted
          reinstated <- eval (define current Nothing value ty) abstracted
          E.unify (scopeContext current) reinstated goal
          eval inner abstracted
    computation = \case
      N.VNeutral neutral -> case N.neutralSpine neutral of
        (N.NGlobal name _, _) | Just Definition {definitionBody = DataConstructor {}} <- Map.lookup name (globals environment) -> pure False
        _ -> pure True
      _ -> pure False

requireUsed :: [MatchRow] -> Set.Set Int -> Elaboration ()
requireUsed rows used = case [matchRowId row | row <- rows, matchRowId row `Set.notMember` used] of
  [] -> pure ()
  index : _ -> E.failure ("case " ++ show (index + 1) ++ " is redundant")

-- without rows, only a column of an empty family can still be split.
compileMatch :: ExpressionChecker -> Scope -> [Column] -> [MatchRow] -> N.Value -> Elaboration (Term, Set.Set Int)
compileMatch checker@ExpressionChecker {checkerEnvironment = environment} scope columns [] expected = do
  empty <- filterM (emptyColumn . columnType . snd) (zip [0 ..] columns)
  case empty of
    (index, _) : _ -> splitColumn checker scope columns [] expected index Nothing
    [] -> E.failure "the match is not exhaustive"
  where
    -- a column is empty when its family hath no constructor, or when its
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
compileMatch checker scope columns rows@(row : _) expected =
  case [(index, inner) | (index, pattern) <- zip [0 ..] (matchPatterns row), let inner = snd (unnamed pattern), refutable inner] of
    (index, PLiteral literal) : _ -> splitLiteral checker scope columns rows expected index literal
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
    (index, _) : _ -> splitColumn checker scope columns rows expected index Nothing
  where
    refutable = \case
      PConstructor {} -> True
      PLiteral _ -> True
      _ -> False
    bindAll current [] = checkTerm checker current (matchBody row) expected
    bindAll current ((name, value, ty) : rest) = do
      annotation <- quote current ty
      valueTerm <- quote current value
      Let annotation valueTerm <$> bindAll (define current (Just name) value ty) rest

-- a literal row splitteth its column in two: rows that accept the literal, and
-- rows that accept any other value. `literal_case` chooseth between them.
splitLiteral :: ExpressionChecker -> Scope -> [Column] -> [MatchRow] -> N.Value -> Int -> HostLiteral -> Elaboration (Term, Set.Set Int)
splitLiteral checker scope columns rows expected index literal = do
  let Column level ty = columns !! index
      literalTy = N.VNeutral (N.NGlobal (literalType literal) [])
      value = columnValue scope level
  E.unify (scopeContext scope) ty literalTy
  kind <- inferCore scope =<< quote scope expected
  resultLevel <- requireUniverse scope kind
  -- an accepting row's names bind the column; the column becometh a wildcard.
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
  (yes, yesUsed) <- compileMatch checker scope columns [accepted | Just accepted <- map accept rows] expected
  (no, noUsed) <- compileMatch checker scope columns (filter reject rows) expected
  result <- quote scope expected
  typeTerm <- quote scope ty
  let chosen = applyArguments (Global H.literalCaseSymbol [resultLevel]) [(Implicit, typeTerm), (Implicit, result), (Explicit, Local (depth scope - level - 1)), (Explicit, Core.Literal (literalType literal) literal), (Explicit, yes), (Explicit, no)]
  pure (chosen, Set.union yesUsed noUsed)

-- the motive abstracteth the split column from the expected type. recursion
-- supplieth its own motive and records induction hypotheses for children.
splitColumn :: ExpressionChecker -> Scope -> [Column] -> [MatchRow] -> N.Value -> Int -> Maybe (Term, Scope -> [(Int, Int)] -> Scope) -> Elaboration (Term, Set.Set Int)
splitColumn checker@ExpressionChecker {checkerEnvironment = environment} scope columns rows expected index recursive = do
  let Column level ty = columns !! index
  Split {..} <- columnFamily environment ty
  levels <- E.freshUniverses splitEliminator
  parameterTerms <- traverse (quote scope) splitParameters
  -- indices that are distinct locals are abstracted in place. otherwise each
  -- index is a constructor pattern over distinct locals, unified by large
  -- elimination: the motive computeth the goal where the constructors agree.
  patterns <- traverse (indexPattern environment) splitIndices
  parameterLevels <- concat <$> traverse (\parameter -> map (\index -> depth scope - index - 1) . freeIndices <$> quote scope parameter) splitParameters
  let simple = [indexLevel | Just (IndexVariable indexLevel) <- patterns]
      inPlace = length simple == length splitIndices && length (nub simple) == length simple && level `notElem` simple
  unified <-
    if inPlace
      then pure Nothing
      else case sequence patterns of
        Nothing -> E.failure "matching needs each index of an indexed family to be a variable or a constructor applied to variables"
        Just indexPatterns -> do
          let leaves = concatMap patternLeaves indexPatterns
          unless (length (nub leaves) == length leaves && level `notElem` leaves) (E.failure "matching needs the variables in the indices of an indexed family to be distinct")
          bound <- allM (\leaf -> E.force (columnValue scope leaf) <&> \case N.VNeutral (N.NLocal same) -> same == leaf; _ -> False) leaves
          unless bound (E.failure "matching needs the variables in the indices of an indexed family to be inputs")
          when (maybe False (const True) recursive) (E.failure "recursion cannot yet match a value whose indices are constructors")
          pure (Just indexPatterns)
  let indexLevels = maybe simple (concatMap patternLeaves) unified
  -- an index variable that a parameter also useth would need axiom K, which
  -- stayeth unprovable.
  when (any (`elem` parameterLevels) indexLevels) (E.failure "matching would equate an index with a parameter, which needeth axiom K")
  generalised <- case recursive of
    Nothing -> fmap catMaybes . forM (scopeRecursions scope) $ \Recursion {..} -> case recursionMemo of
      Just memo -> memoRecord scope memo (columnValue scope level) <&> fmap (recursionName,memo,)
      Nothing -> pure Nothing
    Just _ -> pure []
  -- inputs whose types mention the indices or the value are reverted into the
  -- motive and rebound in each branch at their refined types, as `known` in
  -- `{yea, known ^ ...}` with `known: (x p) = b` seeth `(x p) = yea`. a split
  -- that also carrieth course-of-values records revertth nothing.
  dependents <-
    if maybe False (const True) recursive || (null indexLevels && not (null generalised))
      then pure []
      else
        foldM
          ( \found candidate -> do
              let candidateType = K.contextTypes (scopeContext scope) !! (depth scope - candidate - 1)
              mentioned <- map (\index -> depth scope - index - 1) . freeIndices <$> quote scope candidateType
              bound <-
                E.force (columnValue scope candidate) <&> \case
                  N.VNeutral (N.NLocal same) -> same == candidate
                  _ -> False
              pure (if bound && any (`elem` (indexLevels ++ [level] ++ found)) mentioned then found ++ [candidate] else found)
          )
          []
          [candidate | candidate <- [0 .. depth scope - 1], candidate `notElem` (level : indexLevels), candidate > minimum (level : indexLevels)]
  motive <- case recursive of
    Just (motive, _) -> pure motive
    Nothing -> do
      domain <- quote scope ty
      -- the motive keepeth definitions by name, so each branch goal still
      -- nameth them.
      result <- quoteFolded scope expected
      if maybe False (const True) unified
        then do
          unless (null generalised) (E.failure "course-of-values recursion cannot match an indexed family")
          unifiedMotive environment scope level Split {..} levels parameterTerms (maybe [] id unified) dependents expected
        else
          if not (null indexLevels && null dependents)
            then do
              indexDomains <- forM indexLevels \indexLevel -> quote scope (K.contextTypes (scopeContext scope) !! (depth scope - indexLevel - 1))
              dependentDomains <- forM dependents \dependent -> quote scope (K.contextTypes (scopeContext scope) !! (depth scope - dependent - 1))
              let binders = indexLevels ++ [level] ++ dependents
                  abstracted = abstractLevels (depth scope) binders result
                  domains = zipWith (\position term -> abstractLevels (depth scope) (take position binders) term) [0 ..] (indexDomains ++ [domain] ++ dependentDomains)
                  (lambdaDomains, piDomains) = splitAt (length indexLevels + 1) domains
                  plicities = inductiveIndexPlicities splitInfo ++ [Explicit]
              unless (null generalised) (E.failure "course-of-values recursion cannot match an indexed family")
              pure (foldr (\(plicity, binderDomain) -> Core.Lambda plicity binderDomain) (foldr (Pi Explicit) abstracted piDomains) (zip plicities lambdaDomains))
            else do
              let abstracted = abstractLevels (depth scope) [level] result
              -- every enclosing recursion whose memo containeth the matched value
              -- contributeth a record binder; nested recursion needeth all of them.
              let bindRecords _ [] = pure (shiftTerm (length generalised) abstracted)
                  bindRecords current ((_, memo, _) : rest) = do
                    record <- applyMemo current memo (N.VNeutral (N.NLocal (depth scope)))
                    recordType <- eval current record
                    Pi Explicit record <$> bindRecords (extend current Nothing recordType) rest
              Core.Lambda Explicit domain <$> bindRecords (extend scope Nothing ty) generalised
  let prefix = Apply Explicit (foldl (Apply Implicit) (Global splitEliminator levels) parameterTerms) motive
  prefixType <- inferCore scope prefix
  ((applied, appliedType), used) <-
    foldM
      ( \(partial, used) (constructor, fields) ->
          fmap (Set.union used) <$> applyMethod scope partial \methodType ->
            constructorMethod unified generalised dependents constructor fields methodType ty Split {..}
      )
      ((prefix, prefixType), Set.empty)
      (inductiveConstructorInfo splitInfo)
  -- the eliminator taketh the indices, then the matched value.
  let indexTargets = case unified of
        Just _ -> zip (inductiveIndexPlicities splitInfo) splitIndices
        Nothing -> zip (inductiveIndexPlicities splitInfo) (map (columnValue scope) indexLevels)
      targets = indexTargets ++ [(Explicit, columnValue scope level)] ++ [(Explicit, columnValue scope dependent) | dependent <- dependents]
  (target, targetType) <-
    foldM
      ( \(term, termType) (plicity, targetValue) ->
          E.force termType >>= \case
            N.VPi actual _ codomain
              | actual == plicity -> do
                  targetTerm <- quote scope targetValue
                  (Apply plicity term targetTerm,) <$> E.instantiate codomain targetValue
            _ -> E.failure "invalid eliminator target type"
      )
      (applied, appliedType)
      targets
  (term, resultType) <-
    foldM
      ( \(term, ty) (_, _, record) -> do
          recordValue <- eval scope record
          E.force ty >>= \case
            N.VPi Explicit _ codomain -> (Apply Explicit term record,) <$> E.instantiate codomain recordValue
            _ -> E.failure "invalid generalised motive"
      )
      (target, targetType)
      generalised
  case recursive of
    Nothing -> E.unify (scopeContext scope) resultType expected
    Just _ -> pure ()
  -- written index targets carry their own universe holes; checking the whole
  -- application relateth them to the family's parameters.
  when (maybe False (const True) unified) (() <$ inferCore scope term)
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
          then -- the motive computeth the trivial `[goal, goal]` here.
            E.force branchType >>= \case
              N.VPi Explicit trivial _ -> do
                trivialTerm <- quote current trivial
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
                -- recursion rebindeth quantified inputs after the fields. their
                -- columns move by the number of fields that replaced the split column.
                let inner = enter current hypotheses
                    moved position = if position < index then position else position + length fields - 1
                    quantified = case scopeRecursions inner of
                      recursion : _ -> recursionQuantified recursion
                      [] -> []
                    rebind entered ty = bindQuantified entered ty [(moved position, plicity) | (position, plicity) <- quantified] columns' rows'
                case scopeRecursions inner of
                  Recursion {recursionName, recursionMemo = Just _} : _ -> do
                    now <-
                      E.force branchType >>= \case
                        N.VRecordType [("below", _), ("now", now)] -> pure now
                        _ -> E.failure "invalid memoised motive"
                    let entries = [(N.VNeutral (N.NLocal field), (hypothesis, [])) | (field, hypothesis) <- directHypotheses]
                    (body, used) <- rebind (remember recursionName entries inner) now
                    let below = Record [(childName child, Local (depth current - hypothesis - 1)) | (child, (_, hypothesis)) <- zip [0 ..] directHypotheses]
                    pure (Record [("below", below), ("now", body)], used)
                  _ -> rebind inner branchType
              Nothing -> case generalised of
                [] -> revert current branchType dependents columns' rows'
                -- the carried record of the split value now nameth the record of
                -- each recursive field.
                records ->
                  let bindRecords entered ty [] = compileMatch checker entered columns' rows' ty
                      bindRecords entered ty ((name, _, _) : rest) =
                        E.force ty >>= \case
                          N.VPi Explicit recordType codomain -> do
                            recordTerm <- quote entered recordType
                            let recordLevel = depth entered
                                afterRecord = extend entered Nothing recordType
                                entries =
                                  (constructed, (recordLevel, []))
                                    : [(N.VNeutral (N.NLocal field), (recordLevel, ["below", childName child])) | (child, (field, _)) <- zip [0 ..] directHypotheses]
                            resultType <- E.instantiate codomain (N.VNeutral (N.NLocal recordLevel))
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
    -- column that was that input followeth it.
    revert current ty [] columns' rows' = compileMatch checker current columns' rows' ty
    revert current ty (dependent : rest) columns' rows' = do
      let name = scopeNames scope !! (depth scope - dependent - 1)
      (domainTerm, domain, inner, resultType) <- bindInput "invalid reverted motive" Explicit name current ty
      let moved = [if columnLevel == dependent then Column (depth current) domain else column | column@(Column columnLevel _) <- columns']
      first (Core.Lambda Explicit domainTerm) <$> revert inner resultType rest moved rows'
    bindQuantified current ty [] columns' rows' = compileMatch checker current columns' rows' ty
    bindQuantified current ty ((column, plicity) : rest) columns' rows' = do
      (domainTerm, domain, inner, resultType) <- bindInput "invalid recursive motive" plicity Nothing current ty
      -- the column index shifteth when the split column became fields.
      let replaced = [if position == column then Column (depth current) domain else existing | (position, existing) <- zip [0 ..] columns']
      first (Core.Lambda plicity domainTerm) <$> bindQuantified inner resultType rest replaced rows'
    fieldPlicity (plicity, _, _) = plicity
    bindFields current ty [] levels hypotheses continue = continue current (reverse levels) (reverse hypotheses) ty
    bindFields current ty (field : rest) levels hypotheses continue = do
      (fieldLevel, hypothesis, inner, next, wrap) <- methodField current ty field
      first wrap <$> bindFields inner next rest (fieldLevel : levels) (maybe hypotheses (\level -> (fieldLevel, level) : hypotheses) hypothesis) continue
    expandRow fields constructed columnTy row@MatchRow {..} = do
      let (aliases, pattern) = unnamed (matchPatterns !! index)
      (subpatterns, bound) <- case pattern of
        PConstructor _ subpatterns -> (,aliases) <$> assignFields fields subpatterns
        PVariable name -> pure (map (const (PVariable Nothing)) fields, aliases ++ maybe [] pure name)
        _ -> E.failure "a literal pattern cannot match an inductive type"
      pure row {matchPatterns = take index matchPatterns ++ subpatterns ++ drop (index + 1) matchPatterns, matchBindings = matchBindings ++ [(binding, constructed, columnTy) | binding <- bound]}
