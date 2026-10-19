-- | pattern matrices and total recursion lower to dependent eliminators.
-- this module lowereth structural and course-of-values recursion and
-- re-exporteth the match api from `Pattern.Match`. general expressions are
-- delegated to the supplied checking operations.
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
import Control.Monad (foldM, forM, forM_, unless, when)
import Data.Bifunctor (second)
import Data.Functor ((<&>))
import Data.List (elemIndex, nub)
import Data.Maybe (catMaybes, fromMaybe, isJust)
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Host (deedInputs)
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Environment (globals)
import Tung.Dependent.Source.Pattern.Common
import Tung.Dependent.Source.Pattern.Index (indexBindings, indexPattern, patternLeaves, unifiedMotive)
import Tung.Dependent.Source.Pattern.Match
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core
import Tung.Identity (inducedFamily, inductionSymbol)

type Elaboration = E.Elaboration

gatherClauses :: ExpressionChecker -> Scope -> N.Value -> Expression -> Elaboration Clauses
gatherClauses checker@ExpressionChecker {checkerEnvironment = environment, checkerNames = names} start annotation body = go start annotation body [] []
  where
    go scope ty source inputs columnNames =
      E.force ty >>= \case
        N.VPi plicity domain codomain
          | Lambda (Binder {..} : rest) inner <- source,
            binderPlicity == plicity -> do
              forM_ binderAnnotation \annotation -> do
                written <- annotationType checker scope annotation
                E.unify (scopeContext scope) written domain
              bind plicity binderName domain codomain (Lambda rest inner) [maybe Wildcard Name binderName | plicity == Explicit]
          | Lambda [] inner <- source -> go scope ty inner inputs columnNames
          -- an unwritten implicit input belongeth to a following lambda or case
          -- function. a match keepeth the rest of the type as its result.
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
          (current, resultType) <- bindDomain scope name domain codomain
          go current resultType next ((level, plicity, domain) : inputs) (newColumns ++ columnNames)
        casesColumns rows = do
          (current, added, resultType) <- bindCaseInputs scope (rowArity rows) ty
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
      Name name | name /= "_" -> elemIndex (Name name) columnNames
      _ -> Nothing

-- `let f:annotation ≔ body` whose body nameth `f`. the recursion is compiled
-- to the eliminator of one structurally decreasing input.
elaborateRecursive :: ExpressionChecker -> Scope -> String -> N.Value -> Expression -> Elaboration Term
elaborateRecursive checker@ExpressionChecker {checkerEnvironment = environment} start name annotation body = do
  Clauses {..} <- gatherClauses checker start annotation body
  let rows = [row {matchPatterns = [maybe pattern (`PNamed` pattern) (lookup position clauseAliases) | (position, pattern) <- zip [0 ..] (matchPatterns row)]} | row <- clauseRows]
  let explicitInputs = [(level, ty) | (level, Explicit, ty) <- clauseInputs]
      scope = clauseScope
  loops <- isJust . deedInputs <$> quote scope clauseResult
  families <- traverse (familyOf environment . snd) explicitInputs
  -- index patterns have distinct leaf inputs, bound before the structural
  -- input and unused by parameters. their shape stayeth part of the function's
  -- domain even when induction abstracteth the whole index.
  indexed <- forM (zip [0 ..] families) \case
    (position, Just Split {splitIndices, splitParameters}) -> do
      patterns <- traverse (indexPattern environment) splitIndices
      let structuralLevel = fst (explicitInputs !! position)
      parameterLevels <- concat <$> traverse (fmap (mentionedLevels scope) . quote scope) splitParameters
      pure case sequence patterns of
        Just patterns
          | let leaves = concatMap patternLeaves patterns,
            length (nub leaves) == length leaves,
            all (\level -> level < structuralLevel && level `notElem` parameterLevels && level `elem` [input | (input, _, _) <- clauseInputs]) leaves ->
              Just (position, patterns)
        _ -> Nothing
    _ -> pure Nothing
  let positions = [position | Just (position, _) <- indexed]
      patternsAt position = fromMaybe [] (lookup position (catMaybes indexed))
      -- candidate checking useth the same local bindings and induction evidence
      -- as expression checking. failed trials cannot influence later choices.
      select previous [] = maybe (recursionFailure loops ("'" ++ name ++ "' needs a structurally decreasing input")) E.raise previous
      select previous ((position, deep) : rest) =
        E.trial (compile position deep) >>= \case
          Right (term, commit) -> commit >> pure term
          Left failure -> select (previous <|> Just failure) rest
      compile position deep = do
        let (structuralLevel, structuralType) = explicitInputs !! position
        dependencies <- freeIndices <$> quote scope structuralType
        when (any (\(level, plicity, _) -> plicity == Implicit && level > structuralLevel) clauseInputs) (E.failure "implicit inputs after the structural input are not supported")
        let indexPatterns = patternsAt position
            indexLevels = concatMap patternLeaves indexPatterns
            fixed level plicity = level < structuralLevel && level `notElem` indexLevels && (plicity == Implicit || (depth scope - level - 1) `elem` dependencies)
            role level
              | level == structuralLevel = Structural
              | level `elem` indexLevels = Index level
              | fixed level Explicit = Fixed level
              | otherwise = Quantified
            roles = map (role . fst) explicitInputs
            quantified = [(level, plicity) | (level, plicity, _) <- clauseInputs, level /= structuralLevel, level `notElem` indexLevels, not (fixed level plicity)]
            -- an explicit index input is no column: the structural input
            -- determineth it, and each branch nameth its refined value.
            dropped = [inputPosition | (inputPosition, (level, _)) <- zip [0 ..] explicitInputs, level `elem` indexLevels]
            columnOf level = length [() | (other, Explicit, _) <- clauseInputs, other < level, other `notElem` indexLevels]
        -- matching and recursion share index abstraction and the quantified
        -- input telescope; no second annotation walk is needed.
        split@Split {..} <- columnFamily environment structuralType
        levels <- E.freshUniverses splitEliminator
        parameters <- traverse (quote scope) splitParameters
        resultMotive <- unifiedMotive environment scope structuralLevel split levels parameters indexPatterns (map fst quantified) clauseResult
        (motive, memo) <-
          if deep
            then second Just <$> memoisedMotive environment scope structuralType resultMotive
            else pure (resultMotive, Nothing)
        forM_ rows \row -> forM_ dropped \inputPosition -> case unnamed (matchPatterns row !! inputPosition) of
          (_, PVariable _) -> pure ()
          _ -> E.failure "an index input of the structural input must be matched by a variable"
        let columns = [Column level ty Nothing | (level, ty) <- explicitInputs, level `notElem` indexLevels]
            keptRows = [row {matchPatterns = [pattern | (inputPosition, pattern) <- zip [0 ..] (matchPatterns row), inputPosition `notElem` dropped]} | row <- rows]
            structuralColumn = columnOf structuralLevel
            recursion = Recursion name roles indexPatterns [(columnOf level, plicity) | (level, plicity) <- quantified] [] memo loops
            enter current hypotheses = current {scopeRecursions = recursion {recursionHypotheses = hypotheses} : scopeRecursions current}
        (split, used) <- splitColumn checker scope columns keptRows clauseResult structuralColumn (Just (motive, memo, enter))
        requireUsed clauseWrittenRows used
        let result = if deep then Project split "now" else split
            applied = applyArguments result [(plicity, localTerm scope level) | (level, plicity) <- quantified]
        appliedType <- inferCore scope applied
        E.unify (scopeContext scope) appliedType clauseResult
        wrapInputs clauseInputs applied
  -- inputs the first row matcheth come first: the case tree then splitteth
  -- where the definition's first row sayeth, as `m, 0 ^ m` maketh `x ∸ 0`
  -- reduce to `x` for any `x`, and a failure nameth the matched input.
  let demanded = [position | row <- take 1 rows, (position, pattern) <- zip [0 ..] (matchPatterns row), refutable (snd (unnamed pattern))]
      ordered = filter (`elem` demanded) positions ++ filter (`notElem` demanded) positions
  select Nothing [(position, deep) | deep <- [False, True], position <- ordered]

-- `[indices, x: T indices, r{below: Below indices x, now: P indices x}]`.
-- `Below` eliminateth into types: each
-- constructor's record holdeth, per recursive field, that field's own record.
-- joint targets retain records through nested containers, but only the chosen
-- root hath a result; the other targets' `now` is empty. function fields
-- retain their checked input telescope before each child's record.
memoisedMotive :: K.Environment -> Scope -> N.Value -> Term -> Elaboration (Term, Memo)
memoisedMotive environment scope structuralType resultMotive = do
  Split {..} <- columnFamily environment structuralType
  root <- maybe (E.failure "missing structural family") pure (inducedFamily splitEliminator)
  targets <- case inductiveFamilies splitInfo of
    [family] -> pure [(family, splitInfo)]
    families -> forM families \family -> (family,) <$> E.fromEither (inductiveInfo (globals environment) family)
  levels <- E.freshUniverses splitEliminator
  belowLevel <- E.freshLevel
  parameterTerms <- traverse (quote scope) splitParameters
  let parameterPrefix = foldl (Apply Implicit) (Global splitEliminator levels) parameterTerms
  parameterType <- inferCore scope parameterPrefix
  ((prefix, prefixType), domains) <- foldM (supplySort belowLevel) ((parameterPrefix, parameterType), []) targets
  result <- eval scope resultMotive
  (applied, _) <-
    foldM
      ( \partial (_, fields) ->
          fmap fst . applyMethod scope partial $ \methodType -> (,()) <$> belowMethod root (inductiveIndexPlicities splitInfo) result scope methodType fields []
      )
      (prefix, prefixType)
      (concatMap (inductiveConstructorInfo . snd) targets)
  let (_, arguments) = termSpine applied
  motives <- forM domains \(target, plicities, motiveType) -> do
    motive <- telescope scope motiveType [] \current inputs -> do
      let shift = depth current - depth scope
          prefix = [(plicity, shiftTerm shift argument) | (plicity, argument) <- arguments]
          below = applyArguments (Global (inductionSymbol target) levels) (prefix ++ inputs)
          now = if target == root then applyArguments (shiftTerm shift resultMotive) inputs else Core.RecordType []
      pure (Core.RecordType [("below", below), ("now", now)])
    _ <- inferCore scope motive
    value <- eval scope motive
    pure (target, motive, (plicities, value))
  motive <- maybe (E.failure "missing structural motive") pure (lookup root [(target, term) | (target, term, _) <- motives])
  pure (motive, Memo root [(target, value) | (target, _, value) <- motives] [])
  where
    -- motive domains include each target's own dependent index telescope.
    -- walking the checked type preserveth both its domains and plicities.
    telescope current ty inputs finish =
      E.force ty >>= \case
        N.VPi plicity domain codomain -> do
          annotation <- quote current domain
          (inner, next) <- bindDomain current Nothing domain codomain
          Core.Lambda plicity annotation <$> telescope inner next (inputs ++ [(plicity, depth current)]) finish
        N.VSort _ -> finish current [(plicity, localTerm current level) | (plicity, level) <- inputs]
        _ -> E.failure "invalid course-of-values motive telescope"
    supplySort level ((term, ty), domains) (target, info) =
      E.force ty >>= \case
        N.VPi Explicit motiveType codomain -> do
          motive <- telescope scope motiveType [] \_ _ -> pure (Sort level)
          inferred <- inferCore scope motive
          E.unify (scopeContext scope) inferred motiveType
          next <- eval scope motive >>= E.instantiate codomain
          pure ((Apply Explicit term motive, next), domains ++ [(target, inductiveIndexPlicities info, motiveType)])
        _ -> E.failure "invalid inductive motive ilk"
    -- bind the fields and their type-valued hypotheses, then build the record.
    belowMethod root plicities result current _ [] children = do
      entries <- forM (zip [0 :: Int ..] (reverse children)) \(index, (target, field, hypothesis)) -> do
        let fieldTerm = localTerm current field
            hypothesisTerm = localTerm current hypothesis
        fieldType <- inferCore current fieldTerm
        record <- childRecord root plicities result target current fieldType fieldTerm hypothesisTerm
        pure (childName index, record)
      pure (Core.RecordType entries)
    belowMethod root plicities result current ty (field@(_, _, target) : rest) children = do
      (fieldLevel, hypothesis, inner, next, wrap) <- methodField current ty field
      wrap <$> belowMethod root plicities result inner next rest ([(family, fieldLevel, level) | Just family <- [target], Just level <- [hypothesis]] ++ children)
    -- a function child's record taketh the field's own dependent arguments.
    -- its type-valued hypothesis and result motive see the same applications.
    childRecord root plicities result target current ty field hypothesis =
      E.force ty >>= \case
        N.VPi plicity domain codomain -> do
          annotation <- quote current domain
          (inner, next) <- bindDomain current Nothing domain codomain
          let apply term = Apply plicity (shiftTerm 1 term) (Local 0)
          Pi plicity annotation <$> childRecord root plicities result target inner next (apply field) (apply hypothesis)
        _ -> do
          now <-
            if target == root
              then eval current field >>= applyIndexedMotive current plicities result >>= quote current
              else pure (Core.RecordType [])
          pure (Core.RecordType [("below", hypothesis), ("now", now)])

-- `children f arguments` becometh the hypothesis applied to quantified inputs.
recursiveCall :: ExpressionChecker -> Scope -> Recursion -> [Argument] -> Elaboration (Term, N.Value)
recursiveCall checker scope Recursion {..} arguments = do
  unless (all ((== Explicit) . argumentPlicity) arguments) (refuse "a recursive call cannot supply implicit arguments")
  let explicit = map argumentExpression arguments
  unless (all (== Quantified) (drop (length explicit) recursionRoles)) (refuse "a recursive call must supply its structural, fixed, and index inputs")
  passed <- fmap concat . forM (zip recursionRoles explicit) $ \(role, argument) ->
    case role of
      Structural -> pure []
      Index _ -> pure []
      Quantified -> pure [Argument Explicit argument]
      Fixed level -> do
        value <- localLevel argument
        unless (value == Just level) (refuse "a recursive call must pass fixed inputs unchanged")
        pure []
  let rest = passed ++ map (Argument Explicit) (drop (length recursionRoles) explicit)
      structural = [argument | (Structural, argument) <- zip recursionRoles explicit]
  case (recursionMemo, structural) of
    (Just memo, [argument]) -> do
      value <- inferStructural argument
      memoRecord scope memo value >>= \case
        Just (target, record) | target == memoRoot memo -> do
          checkIndices value
          recordType <- inferCore scope record
          E.force recordType >>= \case
            N.VRecordType [("below", _), ("now", now)] -> applyTerm checker scope (Project record "now") now rest []
            _ -> E.failure "invalid memoised motive"
        _ -> refuse "a recursive call must pass a descendant of the matched input"
    _ -> directCall rest structural
  where
    refuse = recursionFailure recursionLoops
    inferStructural argument = do
      (term, _) <- inferTerm checker scope argument
      eval scope term >>= E.force
    directCall rest structural = do
      value <- case structural of
        [argument] -> inferStructural argument
        _ -> E.failure "invalid recursive call"
      (hypothesis, childArguments) <- case value of
        N.VNeutral neutral
          | (N.NLocal level, arguments) <- N.neutralSpine neutral,
            Just hypothesis <- lookup level recursionHypotheses ->
              pure (hypothesis, arguments)
        _ -> refuse "a recursive call must pass a direct child of the matched input"
      checkIndices value
      -- a function child's hypothesis first taketh the child's inputs.
      arguments <- traverse (traverse (quote scope)) childArguments
      let term = applyArguments (localTerm scope hypothesis) arguments
      ty <- inferCore scope term
      applyTerm checker scope term ty rest []
    -- both kinds of evidence require the declaration's entire index shape.
    -- a supplied leaf denoteth the matched part, not the full index.
    checkIndices value =
      unless (null recursionIndices) do
        childTerm <- quote scope value
        childType <- inferCore scope childTerm
        indices <-
          familyOf (checkerEnvironment checker) childType
            >>= maybe (refuse "a recursive call must pass a child of the indexed family") (pure . splitIndices)
        bindings <- indexBindings (checkerEnvironment checker) recursionIndices indices
        forM_ [(leaf, argument) | (Index leaf, argument) <- zip recursionRoles (map argumentExpression arguments)] \(leaf, argument) -> do
          (term, _) <- inferTerm checker scope argument
          written <- eval scope term
          matched <- maybe (E.failure "missing recursive index leaf") pure (lookup leaf bindings)
          E.unify (scopeContext scope) written matched
    localLevel argument =
      inferStructural argument <&> \case
        N.VNeutral (N.NLocal level) -> Just level
        _ -> Nothing
