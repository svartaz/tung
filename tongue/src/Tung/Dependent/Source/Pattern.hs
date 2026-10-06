-- | pattern matrices and total recursion lower to dependent eliminators.
-- this module lowereþ structural and course-of-values recursion and
-- re-exporteþ þe match api from `Pattern.Match`. general expressions are
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
import Data.Functor ((<&>))
import Data.List (nub)
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Pattern.Common
import Tung.Dependent.Source.Pattern.Match
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core

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
          resultType <- E.instantiate codomain (N.VNeutral (N.NLocal level))
          go (extend scope name domain) resultType next ((level, plicity, domain) : inputs) (newColumns ++ columnNames)
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
      Name name -> lookup (Name name) (zip columnNames [0 :: Int ..]) >>= \position -> if name == "_" then Nothing else Just position
      _ -> Nothing

-- `let f:annotation ≔ body` whose body nameþ `f`. the recursion is compiled
-- to the eliminator of one structurally decreasing input.
elaborateRecursive :: ExpressionChecker -> Scope -> String -> N.Value -> Expression -> Elaboration Term
elaborateRecursive checker@ExpressionChecker {checkerEnvironment = environment} start name annotation body = do
  Clauses {..} <- gatherClauses checker start annotation body
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
        dependencies <- freeIndices <$> quote scope structuralType
        when (any (\(level, plicity, _) -> plicity == Implicit && level > structuralLevel) clauseInputs) (E.failure "implicit inputs after the structural input are not supported")
        let fixed level plicity = level < structuralLevel && (plicity == Implicit || (depth scope - level - 1) `elem` dependencies)
            roles = [if level == structuralLevel then Structural else if fixed level Explicit then Fixed level else Quantified | (level, _) <- explicitInputs]
            quantified = [(level, plicity) | (level, plicity, _) <- clauseInputs, level /= structuralLevel, not (fixed level plicity)]
            columnOf level = length [() | (other, Explicit, _) <- clauseInputs, other < level]
        -- the motive rebindeþ quantified inputs in order after the matched value.
        resultMotive <- recursiveMotive scope annotation clauseInputs structuralLevel (map fst quantified)
        (motive, memo) <-
          if deep
            then do
              memoMotive <- memoisedMotive environment scope structuralType resultMotive
              memoValue <- eval scope memoMotive
              pure (memoMotive, Just (Memo memoValue []))
            else pure (resultMotive, Nothing)
        let columns = [Column level ty | (level, ty) <- explicitInputs]
            recursion = Recursion name roles [(columnOf level, plicity) | (level, plicity) <- quantified] [] memo
            enter current hypotheses = current {scopeRecursions = recursion {recursionHypotheses = hypotheses} : scopeRecursions current}
        (split, used) <- splitColumn checker scope columns rows clauseResult position (Just (motive, enter))
        requireUsed clauseWrittenRows used
        let result = if deep then Project split "now" else split
            applied = foldl (\term (level, plicity) -> Apply plicity term (Local (depth scope - level - 1))) result quantified
        appliedType <- inferCore scope applied
        E.unify (scopeContext scope) appliedType clauseResult
        wrapInputs clauseInputs applied
  select Nothing [(position, deep) | deep <- [False, True], position <- positions]

-- walk the annotation again wiþ the matched input and quantified inputs
-- replaced by fresh binders; fixed inputs keep their outer locals.
recursiveMotive :: Scope -> N.Value -> [(Int, Plicity, N.Value)] -> Int -> [Int] -> Elaboration Term
recursiveMotive scope annotation inputs structuralLevel quantified = do
  let outer = depth scope
      structuralBinder = outer
  (structuralDomain, binders, result) <- walk annotation inputs (structuralBinder + 1) Nothing []
  pure (Core.Lambda Explicit structuralDomain (foldr (\(plicity, domain) term -> Pi plicity domain term) result binders))
  where
    walk ty [] next domain binders = do
      result <- E.quote next ty
      case domain of
        Just structuralDomain -> pure (structuralDomain, reverse binders, result)
        Nothing -> E.failure "missing structural input"
    walk ty ((level, plicity, _) : rest) next domain binders =
      E.force ty >>= \case
        N.VPi _ inputDomain codomain
          | level == structuralLevel -> do
              domainTerm <- E.quote (depth scope) inputDomain
              continue <- E.instantiate codomain (N.VNeutral (N.NLocal (depth scope)))
              walk continue rest next (Just domainTerm) binders
          | level `elem` quantified -> do
              domainTerm <- E.quote next inputDomain
              continue <- E.instantiate codomain (N.VNeutral (N.NLocal next))
              walk continue rest (next + 1) domain ((plicity, domainTerm) : binders)
          | otherwise -> do
              continue <- E.instantiate codomain (N.VNeutral (N.NLocal level))
              walk continue rest next domain binders
        _ -> E.failure "invalid recursive annotation"

-- `[x: T, r{below: Below x, now: P x}]`. `Below` eliminateþ into types: each
-- constructor's record holdeþ, per recursive field, þat field's own record.
-- function fields contribute no entry.
memoisedMotive :: K.Environment -> Scope -> N.Value -> Term -> Elaboration Term
memoisedMotive environment scope structuralType resultMotive = do
  Split {..} <- columnFamily environment structuralType
  domain <- quote scope structuralType
  levels <- E.freshUniverses splitEliminator
  belowLevel <- E.freshLevel
  parameterTerms <- traverse (quote scope) splitParameters
  let prefix = Apply Explicit (foldl (Apply Implicit) (Global splitEliminator levels) parameterTerms) (Core.Lambda Explicit domain (Sort belowLevel))
  prefixType <- inferCore scope prefix
  (applied, _) <-
    foldM
      ( \(term, termType) (_, fields) ->
          fmap fst . applyMethod scope (term, termType) $ \methodType -> (,()) <$> belowMethod scope methodType fields []
      )
      (prefix, prefixType)
      (inductiveConstructorInfo splitInfo)
  let below = Apply Explicit (shiftTerm 1 applied) (Local 0)
      now = Apply Explicit (shiftTerm 1 resultMotive) (Local 0)
  let motive = Core.Lambda Explicit domain (Core.RecordType [("below", below), ("now", now)])
  _ <- inferCore scope motive
  pure motive
  where
    -- bind þe fields and þeir type-valued hypotheses, þen build þe record.
    belowMethod current _ [] children = do
      entries <- forM (zip [0 :: Int ..] (reverse children)) \(index, (field, hypothesis)) -> do
        now <- applyResult (N.VNeutral (N.NLocal field))
        nowTerm <- quote current now
        pure (childName index, Core.RecordType [("below", Local (depth current - hypothesis - 1)), ("now", nowTerm)])
      pure (Core.RecordType entries)
    belowMethod current ty (field@(_, annotation, _) : rest) children = do
      (fieldLevel, hypothesis, inner, next, wrap) <- methodField current ty field
      -- only a direct recursive field haþ a record of its own.
      let direct = case annotation of
            Pi {} -> False
            _ -> True
      wrap <$> belowMethod inner next rest ([(fieldLevel, level) | Just level <- [hypothesis], direct] ++ children)
    applyResult argument =
      eval scope resultMotive >>= \case
        N.VLambda _ _ closure -> E.instantiate closure argument
        _ -> E.failure "invalid recursive motive"

-- `children f arguments` becomeþ the hypothesis applied to quantified inputs.
recursiveCall :: ExpressionChecker -> Scope -> Recursion -> [Argument] -> Elaboration (Term, N.Value)
recursiveCall checker scope Recursion {..} arguments = do
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
      memoRecord scope memo value >>= \case
        Just record -> do
          recordType <- inferCore scope record
          E.force recordType >>= \case
            N.VRecordType [("below", _), ("now", now)] -> applyTerm checker scope (Project record "now") now rest []
            _ -> E.failure "invalid memoised motive"
        Nothing -> E.failure "a recursive call must pass a descendant of the matched input"
    _ -> directCall rest structural
  where
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
        _ -> E.failure "a recursive call must pass a direct child of the matched input"
      -- a function child's hypothesis first takeþ þe child's inputs.
      arguments <- traverse (\(plicity, value) -> (plicity,) <$> quote scope value) childArguments
      let term = applyArguments (Local (depth scope - hypothesis - 1)) arguments
      ty <- inferCore scope term
      applyTerm checker scope term ty rest []
    localLevel argument =
      inferStructural argument <&> \case
        N.VNeutral (N.NLocal level) -> Just level
        _ -> Nothing
