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
    unnamed,
    refutable,
  )
where

import Control.Monad (filterM, foldM, forM, forM_, unless, when)
import Data.Bifunctor (first)
import Data.Foldable (foldrM)
import Data.Functor ((<&>))
import Data.List (elemIndex, nub, nubBy)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe, isJust)
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
import Tung.Identity (SymbolId (..), inducedFamily)
import Tung.Primitive (naturalSuccessorId, naturalZeroId)

type Elaboration = E.Elaboration

-- the names a column pattern bindeth to the whole value, and the pattern beneath.
unnamed :: PatternTree -> ([String], PatternTree)
unnamed = \case
  PNamed name pattern -> let (names, inner) = unnamed pattern in (name : names, inner)
  pattern -> ([], pattern)

-- a pattern that only some values match, which a split must inspect.
refutable :: PatternTree -> Bool
refutable = \case
  PConstructor {} -> True
  PLiteral _ -> True
  _ -> False

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
-- a local or global value. an ambiguous name is rejected only when one of its
-- meanings is a constructor; otherwise it can only bind.
resolvePattern :: K.Environment -> Names -> Expression -> Elaboration PatternTree
resolvePattern environment names = \case
  Name name
    | Just (AmbiguousName modules) <- lookupName name names,
      any (\space -> isJust (constructorNamed environment names (space ++ "~" ++ name))) modules ->
        E.failure (ambiguousName name modules)
    | Just (AmbiguousName _) <- lookupName name names -> pure (PVariable (bindingName (Just name)))
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
assignFields :: [(Plicity, Term, Maybe SymbolId)] -> [(Plicity, PatternTree)] -> Elaboration [PatternTree]
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
  let columns = [Column level domain Nothing | (level, Explicit, domain) <- inputs]
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
          (inner, resultType) <- bindDomain current Nothing domain codomain
          go inner remaining' resultType ((level, plicity, domain) : inputs)
        _ -> E.failure "a case function needs a function type with one input per pattern"

-- a scrutinee that is already a local is matched in place, so the result
-- type may depend on it. other scrutinees are bound first.
checkMatch :: ExpressionChecker -> Scope -> [Expression] -> [Row] -> N.Value -> Elaboration Term
checkMatch checker@ExpressionChecker {checkerEnvironment = environment, checkerNames = names} scope scrutinees rows expected = do
  written <- matchRows environment names rows
  -- a local scrutinee is rebound in each row to the value matched there, so
  -- a branch seeth it at its refined type, as `nil` in `match v { nil ^ v }`.
  -- only an indexed family's value changeth type in a branch.
  localNames <- forM scrutinees \scrutinee -> case unlocated scrutinee of
    Name name
      | Just position <- elemIndex (Just name) (scopeNames scope) ->
          familyOf environment (K.contextTypes (scopeContext scope) !! position) <&> \case
            Just Split {splitIndices = _ : _} -> Just name
            _ -> Nothing
    _ -> pure Nothing
  let resolved = [row {matchPatterns = [maybe pattern (`PNamed` pattern) local | (local, pattern) <- zip localNames (matchPatterns row)]} | row <- written]
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
        N.VNeutral (N.NLocal local) -> bindScrutinees current remaining (Column local ty Nothing : columns) goal continue
        _ -> do
          records <- memoRecords current value
          generalise current value ty goal >>= \case
            Nothing | null records -> Let annotation term <$> bindScrutinees (define current Nothing value ty) remaining (Column level ty Nothing : columns) goal continue
            -- the computed scrutinee becometh an input, so each row seeth its
            -- constructor in the goal, as agda's `with` doth. carried records
            -- need this input even when the ordinary goal stayeth constant.
            abstracted -> do
              -- a fresh value needeth records at that value, not at the old
              -- computation. bind both, then apply them to the checked pair.
              let fresh = N.VNeutral (N.NLocal level)
                  bindRecords inner [] = bindScrutinees inner remaining (Column level ty Nothing : columns) (fromMaybe goal abstracted) continue
                  bindRecords inner ((name, memo, target, _) : rest) = do
                    recordType <- applyMemo inner memo target fresh
                    domain <- eval inner recordType
                    let recordLevel = depth inner
                        entered = remember name [(fresh, (target, recordLevel, []))] (extend inner Nothing domain)
                    Core.Lambda Explicit recordType <$> bindRecords entered rest
              body <- bindRecords (extend current Nothing ty) records
              pure (foldl (Apply Explicit) (Apply Explicit (Core.Lambda Explicit annotation body) term) [record | (_, _, _, record) <- records])
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
  -- a column's type may wait on a known dictionary before its indices
  -- compute through the selected operations.
  settleInstances checker
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
compileMatch checker@ExpressionChecker {checkerEnvironment = environment} scope columns rows@(row : _) expected =
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
    (index, _) : _ ->
      case columnConstructor (columns !! index) of
        Nothing -> splitColumn checker scope columns rows expected index Nothing
        Just (constructor, values) -> do
          let Column level ty _ = columns !! index
          records <- memoRecords scope (columnValue scope level)
          if not (null records)
            -- a carried recursion record must be split with the value so its
            -- descendants retain their respective induction hypotheses.
            then splitColumn checker scope columns rows expected index Nothing
            else do
              Split {splitInfo} <- columnFamily environment ty
              fields <- maybe (E.failure "missing constructor fields") pure (lookup constructor (inductiveConstructorInfo splitInfo))
              let selected = [candidate | candidate <- rows, case snd (unnamed (matchPatterns candidate !! index)) of PConstructor name _ -> name == constructor; _ -> True]
              rows' <- traverse (expandConstructorRow index fields (columnValue scope level) ty) selected
              bindKnown scope values [] \current fieldColumns ->
                compileMatch checker current (take index columns ++ fieldColumns ++ drop (index + 1) columns) rows' expected
  where
    bindAll current [] = checkTerm checker current (matchBody row) expected
    bindAll current ((name, value, ty) : rest) = do
      annotation <- quote current ty
      valueTerm <- quote current value
      Let annotation valueTerm <$> bindAll (define current (Just name) value ty) rest
    -- transparent constructor columns already have known fields. decomposing
    -- them needeth no eliminator and cannot introduce unreachable cases.
    bindKnown current [] fields continue = continue current (reverse fields)
    bindKnown current (value : rest) fields continue = do
      term <- quote current value
      ty <- inferCore current term
      annotation <- quote current ty
      let level = depth current
      known <- constructorView environment value
      first (Let annotation term) <$> bindKnown (define current Nothing value ty) rest (Column level ty known : fields) continue

-- every enclosing recursive definition may carry evidence for this value.
memoRecords :: Scope -> N.Value -> Elaboration [(String, Memo, SymbolId, Term)]
memoRecords scope value = fmap catMaybes . forM (scopeRecursions scope) $ \Recursion {..} -> case recursionMemo of
  Just memo -> memoRecord scope memo value <&> fmap (\(target, record) -> (recursionName, memo, target, record))
  Nothing -> pure Nothing

-- each enclosing recursion retaineth its own checked descendant projections.
remember :: String -> [(N.Value, (SymbolId, Int, [String]))] -> Scope -> Scope
remember name entries current =
  current {scopeRecursions = [if recursionName recursion == name then recursion {recursionMemo = (\memo -> memo {memoEntries = entries ++ memoEntries memo}) <$> recursionMemo recursion} else recursion | recursion <- scopeRecursions current]}

expandConstructorRow :: Int -> [(Plicity, Term, Maybe SymbolId)] -> N.Value -> N.Value -> MatchRow -> Elaboration MatchRow
expandConstructorRow index fields constructed columnTy row@MatchRow {..} = do
  let (aliases, pattern) = unnamed (matchPatterns !! index)
  (subpatterns, bound) <- case pattern of
    PConstructor _ subpatterns -> (,aliases) <$> assignFields fields subpatterns
    PVariable name -> pure (map (const (PVariable Nothing)) fields, aliases ++ maybe [] pure name)
    _ -> E.failure "a literal pattern cannot match an inductive type"
  pure row {matchPatterns = take index matchPatterns ++ subpatterns ++ drop (index + 1) matchPatterns, matchBindings = matchBindings ++ [(binding, constructed, columnTy) | binding <- bound]}

-- a literal row splitteth its column in two: rows that accept the literal, and
-- rows that accept any other value. `literal_case` chooseth between them.
splitLiteral :: ExpressionChecker -> Scope -> [Column] -> [MatchRow] -> N.Value -> Int -> HostLiteral -> Elaboration (Term, Set.Set Int)
splitLiteral checker scope columns rows expected index literal = do
  let Column level ty _ = columns !! index
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
splitColumn :: ExpressionChecker -> Scope -> [Column] -> [MatchRow] -> N.Value -> Int -> Maybe (Term, Maybe Memo, Scope -> [(Int, Int)] -> Scope) -> Elaboration (Term, Set.Set Int)
splitColumn checker@ExpressionChecker {checkerEnvironment = environment} scope columns rows expected index recursive = do
  let Column level ty _ = columns !! index
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
          pure (Just indexPatterns)
  let indexLevels = maybe simple (concatMap patternLeaves) unified
  -- an index variable that a parameter also useth would need axiom K, which
  -- stayeth unprovable.
  when (any (`elem` parameterLevels) indexLevels) (E.failure "matching would equate an index with a parameter, which needeth axiom K")
  generalised <- case recursive of
    Nothing -> memoRecords scope (columnValue scope level)
    Just _ -> pure []
  -- indexed matches revert inputs that depend on their indices or value.
  -- carried records form the inner telescope, after those reverted inputs.
  dependents <-
    if maybe False (const True) recursive || (null indexLevels && not (null generalised))
      then pure []
      else dependentInputs scope (level : indexLevels)
  motive <- case recursive of
    Just (motive, _, _) -> pure motive
    Nothing -> do
      -- every enclosing recursion whose memo containeth the matched value
      -- contributeth a checked record binder. index abstraction then refineth
      -- that same telescope with the ordinary goal.
      let bindRecords current [] = quoteFolded current expected
          bindRecords current ((_, memo, target, _) : rest) = do
            record <- applyMemo current memo target (columnValue current level)
            recordType <- eval current record
            Pi Explicit record <$> bindRecords (extend current Nothing recordType) rest
      result <- bindRecords scope generalised >>= eval scope
      unifiedMotive environment scope level Split {..} levels parameterTerms (maybe (map IndexVariable simple) id unified) dependents result
  let memo = case recursive of
        Just (_, memo, _) -> memo
        Nothing -> Nothing
  (prefix, prefixType) <- eliminatorPrefix scope Split {..} levels parameterTerms motive (columnValue scope level) memo
  methods <- E.fromEither (inductiveMethods (globals environment) splitInfo)
  ((applied, appliedType), used) <-
    foldM
      ( \(partial, used) (constructor, fields) ->
          fmap (Set.union used) <$> applyMethod scope partial \methodType ->
            if constructor `elem` map fst (inductiveConstructorInfo splitInfo)
              then constructorMethod unified generalised dependents indexLevels constructor fields methodType ty Split {..}
              else
                (,Set.empty) <$> case memo of
                  Just _ -> memoMethod scope methodType fields []
                  Nothing -> trivialMethod scope methodType fields
      )
      ((prefix, prefixType), Set.empty)
      methods
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
      ( \(term, ty) (_, _, _, record) -> do
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
  -- the complete application relateth motive and method universes to the
  -- family's parameters, including the reverted record telescope.
  _ <- inferCore scope term
  pure (term, used)
  where
    -- each record carrieth the direct child records in their field order.
    memoResult current hypotheses now =
      Record [("below", Record [(childName child, Local (depth current - hypothesis - 1)) | (child, hypothesis) <- zip [0 ..] hypotheses]), ("now", now)]
    memoNow ty =
      E.force ty >>= \case
        N.VRecordType [("below", _), ("now", now)] -> pure now
        _ -> E.failure "invalid memoised motive"
    -- peer methods retain descendant records but compute no source result.
    memoMethod current _ [] hypotheses = pure (memoResult current (reverse hypotheses) (Record []))
    memoMethod current ty (field : rest) hypotheses = do
      (_, hypothesis, inner, next, wrap) <- methodField current ty field
      wrap <$> memoMethod inner next rest (maybe hypotheses (: hypotheses) hypothesis)
    constructorMethod unified generalised dependents indexLevels constructor fields methodType columnTy Split {..} = do
      let selected = [row | row <- rows, keeps row]
          keeps row = case snd (unnamed (matchPatterns row !! index)) of
            PConstructor name _ -> name == constructor
            PLiteral _ -> False
            _ -> True
      forced <- case unified of
        Nothing -> pure Map.empty
        Just indexPatterns -> do
          let fieldValues = [N.VNeutral (N.NLocal (depth scope + position)) | position <- [0 .. length fields - 1]]
          constructorFit environment Split {..} indexPatterns constructor fieldValues >>= \case
            IndexFits forced -> pure forced
            IndexImpossible forced -> pure forced
            IndexUndecidable -> E.failure ("matching cannot decide whether " ++ symbolName constructor ++ " fiteth the indices")
      let fieldPatterns = [Map.lookup (depth scope + position) forced | position <- [0 .. length fields - 1]]
      bindFields scope methodType fields fieldPatterns [] [] \current fieldLevels hypotheses branchType -> do
        let fieldValues = map (columnValue current) fieldLevels
            recursiveFields = [field | field@(_, _, Just _) <- fields]
            childHypotheses = [(target, field, hypothesis) | ((_, _, Just target), (field, hypothesis)) <- zip recursiveFields hypotheses]
            memoBody = memoResult current [hypothesis | (_, _, hypothesis) <- childHypotheses]
        possible <- case unified of
          Just indexPatterns -> constructorPossible environment Split {..} indexPatterns constructor fieldValues
          Nothing -> pure True
        if not possible
          then do
            -- off-domain records retain their descendants; only `now` is
            -- trivial. a deeper descendant may re-enter the declared domain.
            now <- case recursive of
              Just (_, Just _, _) -> memoNow branchType
              _ -> pure branchType
            trivial <-
              E.force now >>= \case
                N.VPi Explicit domain _ -> do
                  annotation <- quote current domain
                  pure (Core.Lambda Explicit annotation (Local 0))
                _ -> E.failure "invalid impossible case"
            pure (case recursive of Just (_, Just _, _) -> memoBody trivial; _ -> trivial, Set.empty)
          else do
            when (null selected) (E.failure ("the match is not exhaustive: missing " ++ symbolName constructor))
            let constructed = constructorValue constructor splitLevels splitParameters (zip (map fieldPlicity fields) fieldValues)
            -- the constructed value's own type carrieth its refined indices.
            constructedType <-
              if null indexLevels
                then pure columnTy
                else quote current constructed >>= inferCore current
            -- each index input named in scope seeth the constructor's index.
            refinedIndices <- case unified of
              Nothing
                | not (null indexLevels) ->
                    familyOf environment constructedType <&> \case
                      Just Split {splitIndices = refined} -> zip indexLevels refined
                      Nothing -> []
              Just indexPatterns -> matchedIndexBindings environment Split {..} indexPatterns constructor fieldValues
              _ -> pure []
            -- a later index's type may itself depend on an earlier index.
            -- infer the refined value's type rather than retain its old domain.
            refinements <- forM [(name, value) | (indexLevel, value) <- refinedIndices, Just name <- [scopeNames scope !! (depth scope - indexLevel - 1)]] \(name, value) -> do
              ty <- inferCore current =<< quote current value
              pure (name, value, ty)
            rows' <- map (\row -> row {matchBindings = matchBindings row ++ refinements}) <$> traverse (expandConstructorRow index fields constructed constructedType) selected
            fieldColumns <- forM fieldLevels \fieldLevel -> do
              known <- constructorView environment (columnValue current fieldLevel)
              pure (Column fieldLevel (K.contextTypes (scopeContext current) !! (depth current - fieldLevel - 1)) known)
            let columns' = take index columns ++ fieldColumns ++ drop (index + 1) columns
            case recursive of
              Just (_, _, enter) -> do
                -- peer hypotheses serve joint induction. a source function
                -- can recurse only on children of its own structural family.
                let ownHypotheses =
                      [ hypothesis
                      | ((_, _, target), hypothesis) <- zip recursiveFields hypotheses,
                        target == inducedFamily splitEliminator
                      ]
                -- recursion rebindeth quantified inputs after the fields. their
                -- columns move by the number of fields that replaced the split column.
                let inner = enter current ownHypotheses
                    moved position = if position < index then position else position + length fields - 1
                    quantified = case scopeRecursions inner of
                      recursion : _ -> recursionQuantified recursion
                      [] -> []
                    rebind entered ty = bindQuantified entered ty [(moved position, plicity) | (position, plicity) <- quantified] columns' rows'
                case scopeRecursions inner of
                  Recursion {recursionName, recursionMemo = Just _} : _ -> do
                    now <- memoNow branchType
                    let entries = [(N.VNeutral (N.NLocal field), (target, hypothesis, [])) | (target, field, hypothesis) <- childHypotheses]
                    (body, used) <- rebind (remember recursionName entries inner) now
                    pure (memoBody body, used)
                  _ -> rebind inner branchType
              Nothing ->
                revert current branchType dependents columns' rows' ((columnLevel (columns !! index), constructed) : refinedIndices) \entered result moved refined replacements ->
                  let bindRecords inner ty [] = compileMatch checker inner moved refined ty
                      bindRecords inner ty ((name, _, target, _) : rest) = do
                        -- specialised metadata retaineth children beneath an
                        -- ordinary container whose eliminator hath no such IH.
                        info <- E.fromEither (inductiveInfo (globals environment) target)
                        specialised <- maybe (E.failure "missing memo constructor") pure (lookup constructor (inductiveConstructorInfo info))
                        let children = [(childTarget, field) | ((_, _, Just childTarget), field) <- zip specialised fieldLevels]
                        E.force ty >>= \case
                          N.VPi Explicit recordType codomain -> do
                            recordTerm <- quote inner recordType
                            let recordLevel = depth inner
                                known =
                                  (constructed, (target, recordLevel, []))
                                    : [(columnValue current field, (childTarget, recordLevel, ["below", childName child])) | (child, (childTarget, field)) <- zip [0 ..] children]
                            entries <- forM known \(value, place) -> (,place) <$> refineValue inner replacements value
                            (afterRecord, resultType) <- bindDomain inner Nothing recordType codomain
                            (body, used) <- bindRecords (remember name entries afterRecord) resultType rest
                            pure (Core.Lambda Explicit recordTerm body, used)
                          _ -> E.failure "invalid generalised motive"
                   in bindRecords entered result generalised
    -- each reverted input and its direct-child evidence move together. old
    -- context slots stay captured; visible definitions are rebuilt with checked
    -- lets after the new telescope is bound, so aliases see the refined fields.
    revert current ty [] columns' rows' replacements continue = do
      refined <- forM rows' \row -> do
        bindings <- forM (matchBindings row) \(name, value, annotation) ->
          (name,,) <$> refineValue current replacements value <*> refineValue current replacements annotation
        pure row {matchBindings = bindings}
      recursions <- forM (scopeRecursions current) \recursion -> do
        memo <- traverse (refineMemo current replacements) (recursionMemo recursion)
        pure recursion {recursionMemo = memo}
      refineAliases current {scopeRecursions = recursions} replacements \inner -> continue inner ty columns' refined replacements
    revert current ty (dependent : rest) columns' rows' replacements continue = do
      let name = scopeNames scope !! (depth scope - dependent - 1)
      (domainTerm, domain, inner, resultType) <- bindInput "invalid reverted motive" Explicit name current ty
      let level = depth current
          moved = [if columnLevel == dependent then Column level domain Nothing else column | column@(Column columnLevel _ _) <- columns']
          move old = if old == dependent then level else old
          entered = inner {scopeRecursions = [recursion {recursionHypotheses = [(move field, move hypothesis) | (field, hypothesis) <- recursionHypotheses recursion]} | recursion <- scopeRecursions inner]}
      first (Core.Lambda Explicit domainTerm) <$> revert entered resultType rest moved rows' ((dependent, N.VNeutral (N.NLocal level)) : replacements) continue
    -- a reverted hidden record moveth with its descendant. quoted values are
    -- substituted together, so aliases cannot retain stale index locals.
    refineMemo current replacements memo@Memo {memoEntries} = do
      entries <- forM memoEntries \(value, (target, level, path)) -> do
        refined <- refineValue current replacements value
        let moved = case lookup level replacements of
              Just (N.VNeutral (N.NLocal new)) -> new
              _ -> level
        pure (refined, (target, moved, path))
      pure memo {memoEntries = entries}
    refineAliases current replacements continue = bindAliases current aliases
      where
        aliases =
          [ (name, value)
          | (position, (Just name, value)) <- zip [0 ..] (zip (scopeNames scope) (K.contextValues (scopeContext scope))),
            name `notElem` catMaybes (take position (scopeNames scope)),
            case value of
              N.VNeutral (N.NLocal same) -> same /= depth scope - position - 1
              _ -> True
          ]
        bindAliases entered [] = continue entered
        bindAliases entered ((name, value) : rest) = do
          original <- quote entered value
          let mentioned = map (\index -> depth entered - index - 1) (freeIndices original)
          if not (any (`elem` map fst replacements) mentioned)
            then bindAliases entered rest
            else do
              refined <- refineValue entered replacements value
              term <- quote entered refined
              ty <- inferCore entered term
              annotation <- quote entered ty
              first (Let annotation term) <$> bindAliases (define entered (Just name) refined ty) rest
    refineValue current replacements value = do
      term <- quote current value
      let values = [maybe (columnValue current old) id (lookup old replacements) | old <- reverse [0 .. depth current - 1]]
      E.evaluate (K.Context values (K.contextTypes (scopeContext current))) term
    bindQuantified current ty [] columns' rows' = compileMatch checker current columns' rows' ty
    bindQuantified current ty ((column, plicity) : rest) columns' rows' = do
      (domainTerm, domain, inner, resultType) <- bindInput "invalid recursive motive" plicity Nothing current ty
      -- the column index shifteth when the split column became fields.
      let replaced = [if position == column then Column (depth current) domain Nothing else existing | (position, existing) <- zip [0 ..] columns']
      first (Core.Lambda plicity domainTerm) <$> bindQuantified inner resultType rest replaced rows'
    fieldPlicity (plicity, _, _) = plicity
    -- a constrained field is split before its later fields and hypothesis,
    -- so the remaining method type refineth their domains by ordinary beta
    -- reduction. the rebuilt field is a transparent column for written rows.
    bindFields current ty [] _ levels hypotheses continue = continue current (reverse levels) (reverse hypotheses) ty
    bindFields current ty (field@(plicity, _, recursive) : rest) patterns levels hypotheses continue =
      case patterns of
        Just pattern@IndexConstructor {} : remaining -> do
          (domainTerm, domain, afterField, next) <- bindInput "invalid eliminator method" plicity Nothing current ty
          (body, used) <- splitField afterField (depth current) next pattern \inner value resultType -> do
            annotation <- quote inner domain
            term <- quote inner value
            let fieldLevel = depth inner
                rebound = define inner Nothing value domain
            (entered, next', hypothesis, wrap) <-
              if isJust recursive
                then do
                  (hypothesisTerm, _, entered, next') <- bindInput "invalid induction hypothesis" Explicit Nothing rebound resultType
                  pure (entered, next', Just (depth rebound), Core.Lambda Explicit hypothesisTerm)
                else pure (rebound, resultType, Nothing, id)
            first (Let annotation term . wrap) <$> bindFields entered next' rest remaining (fieldLevel : levels) (maybe hypotheses (\level -> (fieldLevel, level) : hypotheses) hypothesis) continue
          pure (Core.Lambda plicity domainTerm body, used)
        _ -> do
          (fieldLevel, hypothesis, inner, next, wrap) <- methodField current ty field
          first wrap <$> bindFields inner next rest (drop 1 patterns) (fieldLevel : levels) (maybe hypotheses (\level -> (fieldLevel, level) : hypotheses) hypothesis) continue
    splitField current target result (IndexConstructor wanted subpatterns) continue = do
      let domain = K.contextTypes (scopeContext current) !! (depth current - target - 1)
      Split {..} <- columnFamily environment domain
      unless (null splitIndices) (E.failure "an index pattern cannot match a value of an indexed family")
      levels <- E.freshUniverses splitEliminator
      parameterTerms <- traverse (quote current) splitParameters
      annotation <- quote current domain
      resultTerm <- quoteFolded current result
      let motive = Core.Lambda Explicit annotation (abstractLevels (depth current) [target] resultTerm)
      (prefix, prefixType) <- eliminatorPrefix current Split {..} levels parameterTerms motive (columnValue current target) Nothing
      methods <- E.fromEither (inductiveMethods (globals environment) splitInfo)
      ((applied, _), used) <-
        foldM
          ( \(partial, used) (constructor, fields) ->
              fmap (Set.union used) <$> applyMethod current partial \methodType ->
                if constructor `elem` map fst (inductiveConstructorInfo splitInfo)
                  then
                    let patterns = if constructor == wanted then map Just subpatterns else []
                     in bindFields current methodType fields patterns [] [] \inner fieldLevels _ branchType ->
                          continue inner (constructorValue constructor splitLevels splitParameters (zip (map fieldPlicity fields) (map (columnValue inner) fieldLevels))) branchType
                  else (,Set.empty) <$> trivialMethod current methodType fields
          )
          ((prefix, prefixType), Set.empty)
          methods
      pure (Apply Explicit applied (Local (depth current - target - 1)), used)
    splitField _ _ _ IndexVariable {} _ = E.failure "invalid forced index field"
