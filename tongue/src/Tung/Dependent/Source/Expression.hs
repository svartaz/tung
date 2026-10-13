-- | bidirectional checking of source expressions: application, fields,
-- matches, local definitions, and recursion.
module Tung.Dependent.Source.Expression
  ( inferExpression,
    checkExpression,
    inferDefinition,
  )
where

import Control.Monad (forM_, unless)
import Data.Functor ((<&>))
import Data.List (elemIndex, partition)
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, isNothing)
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Host qualified as H
import Tung.Dependent.Literal (literalType)
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Instance (classFamily, implicitArgument, settleAnnotation, solveDeterminedInstances)
import Tung.Dependent.Source.Pattern qualified as Patterns
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core
import Tung.Identity (inductionSymbol)

-- universe holes are fresh across the complete declaration, including its
-- annotation and every occurrence of a universe-polymorphic global.
type Elaboration = E.Elaboration

-- the pattern compiler reuseth these operations for row bodies and scrutinees.
patternChecker :: K.Environment -> Names -> Patterns.ExpressionChecker
patternChecker environment names =
  Patterns.ExpressionChecker environment names (inferExpression environment names) (\scope annotation -> snd <$> inferAnnotation environment names scope annotation) (checkExpression environment names) (\scope -> applyTo environment names scope Nothing) (solveDeterminedInstances environment names)

holes :: Term -> Bool
holes = \case
  Meta {} -> True
  term -> any (holes . snd) (children term)

inferAnnotation :: K.Environment -> Names -> Scope -> Expression -> Elaboration (Term, N.Value)
inferAnnotation environment names scope expression = do
  (term, kind) <- inferExpression environment names scope expression
  requireUniverse scope kind
  (term,) <$> eval scope term

inferExpression :: K.Environment -> Names -> Scope -> Expression -> Elaboration (Term, N.Value)
inferExpression environment names scope@Scope {scopeContext = context, scopeNames = locals} = \case
  Located span inner -> E.located span do
    result@(_, ty) <- inferExpression environment names scope inner
    case inner of
      Sorry -> E.recordHole (E.HoleSite (Just span) context locals ty)
      _ -> pure ()
    pure result
  Name name -> do
    term <- case elemIndex (Just name) locals of
      Just index -> pure (Local index)
      Nothing
        | Just _ <- recursiveBinding name scope ->
            E.failure ("a recursive reference to '" ++ name ++ "' must only be called")
        | otherwise -> case lookupName name names of
            Just (FreshName identity universes) -> Global identity <$> E.freshLevels universes
            Just (FixedName identity levels) -> pure (Global identity levels)
            Just (AmbiguousName modules) -> E.failure (ambiguousName name modules)
            Nothing -> E.failure ("unknown name '" ++ name ++ "'")
    (term,) <$> inferCore scope term
  Induce name -> do
    family <- case lookupName name names of
      Just (AmbiguousName modules) -> E.failure (ambiguousName name modules)
      Just binding | Just family <- bindingSymbol binding -> pure family
      _ -> E.failure ("unknown name '" ++ name ++ "'")
    term <- case Map.lookup (inductionSymbol family) (globals environment) of
      Just Definition {definitionUniverses, definitionBody = Eliminator _} ->
        Global (inductionSymbol family) <$> E.freshLevels definitionUniverses
      _ -> E.failure ("'" ++ name ++ "' is not an ilk or flock, so it cannot be unbuilt")
    (term,) <$> inferCore scope term
  Universe -> do
    level <- E.freshLevel
    pure (Sort level, N.VSort (LSucc level))
  Product parameters result -> productTerm scope parameters
    where
      productTerm current [] = inferExpression environment names current result
      productTerm current (Parameter {..} : remaining) = do
        (domain, domainType) <- inferExpression environment names current parameterType
        domainLevel <- requireUniverse current domainType
        domainValue <- eval current domain
        (codomain, codomainType) <- productTerm (extend current parameterName domainValue) remaining
        codomainLevel <- requireUniverse (extend current parameterName domainValue) codomainType
        pure (Pi parameterPlicity domain codomain, N.VSort (K.universeNormalise (LMax domainLevel codomainLevel)))
  Lambda binders _
    | any (Patterns.constructorBinder environment names) binders ->
        E.failure "a function matching constructors needs a type annotation"
  Lambda [] body -> inferExpression environment names scope body
  Lambda (Binder {..} : remaining) body -> do
    (domain, domainValue) <- case binderAnnotation of
      Nothing -> do
        level <- E.freshLevel
        E.newMeta context (N.VSort level)
      Just domainExpression -> do
        (domain, kind) <- inferExpression environment names scope domainExpression
        requireUniverse scope kind
        (domain,) <$> eval scope domain
    let current = extend scope binderName domainValue
    (bodyTerm, bodyType) <- inferExpression environment names current (Lambda remaining body)
    codomain <- quote current bodyType
    pure (Core.Lambda binderPlicity domain bodyTerm, N.VPi binderPlicity domainValue (N.Closure (K.contextValues context) codomain))
  Application (Name name) arguments
    | Nothing <- elemIndex (Just name) locals,
      Just recursion <- recursiveBinding name scope ->
        Patterns.recursiveCall (patternChecker environment names) scope recursion arguments
  Application function arguments -> inferApplication environment names scope Nothing function arguments
  Ascription expression annotation -> do
    (_, expected) <- inferAnnotation environment names scope annotation
    term <- checkExpression environment names scope expression expected
    pure (term, expected)
  Block declarations result -> localDefinitions environment names scope declarations (\current -> inferExpression environment names current result)
  LiteralExpression value -> do
    let term = Core.Literal (literalType value) value
    (term,) <$> inferCore scope term
  -- `sorry` is the primitive assumption at a type inferred from its use.
  Sorry -> do
    level <- E.freshLevel
    (ty, tyValue) <- E.newMeta context (N.VSort level)
    pure (Apply Implicit (Global H.sorrySymbol [level]) ty, tyValue)
  -- `value.field` applieth the accessor its ilk declared, found by the
  -- value's type.
  Projection record name -> do
    (term, ty) <- inferExpression environment names scope record
    accessor <-
      E.force ty >>= \case
        N.VNeutral neutral
          | (N.NGlobal family _, _) <- N.neutralSpine neutral,
            let accessor = K.SymbolId (K.symbolModule family) (K.symbolName family ++ "." ++ name),
            Just definition <- Map.lookup accessor (globals environment) ->
              pure (accessor, definition)
        _ -> E.failure ("the value hath no field '" ++ name ++ "'")
    levels <- E.freshLevels (definitionUniverses (snd accessor))
    let function = Global (fst accessor) levels
    functionType <- inferCore scope function
    value <- eval scope term
    let project applied current =
          E.force current >>= \case
            N.VPi Implicit domain codomain -> do
              (hole, holeValue) <- E.newMeta (scopeContext scope) domain
              E.instantiate codomain holeValue >>= project (Apply Implicit applied hole)
            N.VPi Explicit domain codomain -> do
              E.unify (scopeContext scope) domain ty
              (Apply Explicit applied term,) <$> E.instantiate codomain value
            _ -> E.failure "a field accessor requireth its value"
    project function functionType
  -- `_` only discardeth an input; it is no term or type.
  Wildcard -> E.failure "`_` discardeth an input and is not a term"
  Inferred -> do
    level <- E.freshLevel
    (term, _) <- E.newMeta (scopeContext scope) (N.VSort level)
    pure (term, N.VSort level)
  Cases _ -> E.failure "a case function needs a type annotation"
  -- without an expected type, every row shareth one inferred result type.
  Match scrutinees rows -> do
    level <- E.freshLevel
    let matched = [length locals - index - 1 | Name name <- scrutinees, Just index <- [elemIndex (Just name) locals]]
    (_, resultType) <- E.newMetaWithout (scopeContext scope) matched (N.VSort level)
    term <- Patterns.checkMatch (patternChecker environment names) scope scrutinees rows resultType
    pure (term, resultType)

-- a recursive call is applied through its hypothesis instead.
recursiveApplication :: Scope -> Expression -> Bool
recursiveApplication scope = \case
  Name name -> isNothing (elemIndex (Just name) (scopeNames scope)) && isJust (recursiveBinding name scope)
  _ -> False

inferApplication :: K.Environment -> Names -> Scope -> Maybe N.Value -> Expression -> [Argument] -> Elaboration (Term, N.Value)
inferApplication environment names scope goal function arguments = do
  (term, ty) <- inferExpression environment names scope function
  let (implicit, explicit) = partition ((== Implicit) . argumentPlicity) arguments
  applyTo environment names scope goal term ty explicit implicit

-- caller placement doth not select an implicit parameter: the checked Pi
-- spine consumeth separate queues in declaration order, including values.
-- given the expected type of the application, a function whose result applieth
-- its own type family meeteth that type before the inputs that mention the
-- family are checked; see 'motiveInputs'.
applyTo :: K.Environment -> Names -> Scope -> Maybe N.Value -> Term -> N.Value -> [Argument] -> [Argument] -> Elaboration (Term, N.Value)
applyTo environment names scope@Scope {scopeContext = context} goal function functionType explicitArguments implicitArguments = do
  motive <- case goal of
    Just _ -> motiveInputs names scope functionType (length explicitArguments)
    Nothing -> pure Nothing
  (term, ty, deferred) <- go motive False 0 function functionType explicitArguments implicitArguments []
  let (late, early) = partition (\(_, _, _, afterGoal) -> afterGoal) (reverse deferred)
  -- a postponed case function is checked once later arguments have fixed
  -- its input type, then filleth the hole that stood for it.
  forM_ early checkDeferred
  unless (null late) do
    forM_ goal (E.unify context ty)
    forM_ late checkDeferred
  pure (term, ty)
  where
    checkDeferred (expression, domain, hole, _) = do
      checked <- checkExpression environment names scope expression domain
      value <- eval scope checked
      E.unify context hole value
    -- after the written arguments, a pending requirement is still searched.
    go _ _ _ term ty [] [] deferred =
      E.force ty >>= \case
        N.VPi Implicit domain codomain ->
          classFamily names domain >>= \case
            Just _ -> do
              (argumentTerm, argumentValue) <- implicitArgument names (scopeContext scope) domain
              resultType <- E.instantiate codomain argumentValue
              go Nothing False 0 (Apply Implicit term argumentTerm) resultType [] [] deferred
            Nothing -> pure (term, ty, deferred)
        _ -> pure (term, ty, deferred)
    go motive open position term ty explicit implicit deferred =
      E.force ty >>= \case
        N.VPi plicity domain codomain -> do
          -- a written `@x` filleth the next implicit input that instance search
          -- doth not fill.
          requirement <- if plicity == Implicit then maybe False (const True) <$> classFamily names domain else pure False
          let afterGoal = plicity == Explicit && open && maybe False ((position `elem`) . snd) motive
          (argumentTerm, argumentValue, nextExplicit, nextImplicit, nextDeferred, omitted) <- case (plicity, explicit, implicit) of
            (Explicit, arg : rest, _) -> supplied domain arg afterGoal rest implicit deferred
            (Implicit, _, arg : rest) | not requirement -> supplied domain arg False explicit rest deferred
            (Implicit, _, _) -> do
              (argumentTerm, argumentValue) <- implicitArgument names (scopeContext scope) domain
              pure (argumentTerm, argumentValue, explicit, implicit, deferred, True)
            _ -> E.failure "explicit argument required before a later implicit argument"
          resultType <- E.instantiate codomain argumentValue
          -- only an omitted family is found from the goal.
          let opened = open || omitted && maybe False ((== position) . fst) motive
          go motive opened (position + 1) (Apply plicity term argumentTerm) resultType nextExplicit nextImplicit nextDeferred
        neutral@(N.VNeutral (N.NMeta _ _))
          | null implicit -> do
              (domain, codomain) <- E.ensurePi context Explicit neutral
              go Nothing False position term (N.VPi Explicit domain codomain) explicit implicit deferred
          | otherwise -> E.failure "implicit parameter order requireth a function annotation"
        _ -> E.failure "application requireth a function"
    supplied domain argument afterGoal explicit implicit deferred = do
      let expression = argumentExpression argument
      waiting <- if afterGoal then pure True else unknownCaseInput expression domain
      if waiting
        then do
          (term, value) <- E.newMeta context domain
          pure (term, value, explicit, implicit, (expression, domain, value, afterGoal) : deferred, False)
        else do
          term <- checkExpression environment names scope expression domain
          value <- evalArgument scope term
          pure (term, value, explicit, implicit, deferred, False)
    -- a case function cannot split an input whose type is still a hole.
    unknownCaseInput expression domain = case expression of
      Cases _ ->
        E.force domain >>= \case
          N.VPi _ input _ ->
            E.force input <&> \case
              N.VNeutral neutral | (N.NMeta _ _, _) <- N.neutralSpine neutral -> True
              _ -> False
          _ -> pure False
      _ -> pure False

-- a function whose result applieth one of its own implicit type families,
-- as `throughbear` applieth its property, is a motive function, as lean's
-- `elab_as_elim` nameth it. the explicit inputs whose types mention the family
-- are checked after the result meeteth the expected type, so occurrence
-- abstraction findeth the family in the goal rather than in an input. a family
-- that a requirement mentioneth is a flock carrier, found by instance search.
-- the result holdeth the family's position in the telescope and the positions
-- of those inputs.
motiveInputs :: Names -> Scope -> N.Value -> Int -> Elaboration (Maybe (Int, [Int]))
motiveInputs names scope functionType explicitCount = walk 0 explicitCount functionType [] Set.empty []
  where
    base = depth scope
    walk position remaining ty families carriers inputs =
      E.force ty >>= \case
        N.VPi plicity domain codomain -> do
          requirement <- if plicity == Implicit then isJust <$> classFamily names domain else pure False
          if remaining == 0 && (plicity == Explicit || not requirement)
            then pure Nothing
            else do
              mentioned <- if null families then pure Set.empty else mentions position domain
              family <- if plicity == Implicit && not requirement then isFamily position domain else pure False
              next <- E.instantiate codomain (N.VNeutral (N.NLocal (base + position)))
              walk
                (position + 1)
                (if plicity == Explicit then remaining - 1 else remaining)
                next
                ([position | family] ++ families)
                (if requirement then Set.union mentioned carriers else carriers)
                ([(position, mentioned) | plicity == Explicit] ++ inputs)
        N.VNeutral neutral
          | (N.NLocal level, _) <- N.neutralSpine neutral,
            let motive = level - base,
            motive `elem` families,
            Set.notMember motive carriers ->
              pure (Just (motive, reverse [position | (position, mentioned) <- inputs, Set.member motive mentioned]))
        _ -> pure Nothing
    -- the telescope positions a domain mentioneth.
    mentions position domain = do
      term <- E.quoteFolded (base + position) domain
      pure (Set.fromList [level - base | index <- freeIndices term, let level = base + position - 1 - index, level >= base])
    isFamily position domain =
      E.force domain >>= \case
        N.VPi {} -> endsInSort (base + position) domain
        _ -> pure False
    endsInSort level ty =
      E.force ty >>= \case
        N.VPi _ _ codomain -> E.instantiate codomain (N.VNeutral (N.NLocal level)) >>= endsInSort (level + 1)
        N.VSort _ -> pure True
        _ -> pure False

checkExpression :: K.Environment -> Names -> Scope -> Expression -> N.Value -> Elaboration Term
checkExpression environment names scope (Located span inner) expected = E.located span do
  case inner of
    Sorry -> E.recordHole (E.HoleSite (Just span) (scopeContext scope) (scopeNames scope) expected)
    _ -> pure ()
  checkExpression environment names scope inner expected
checkExpression environment names scope expression expected = E.force expected >>= check
  where
    check expected = case expression of
      -- `sorry` standeth for a settled expected type itself, without an
      -- inference hole.
      Sorry -> do
        ty <- quote scope expected
        if holes ty
          then inferred expected
          else do
            kind <- inferCore scope ty
            level <- requireUniverse scope kind
            pure (Apply Implicit (Global H.sorrySymbol [level]) ty)
      -- leading implicit binders keep their names; only the explicit binders
      -- after them form the pattern row.
      Lambda binders body
        | (implicits@(_ : _), explicits) <- span ((== Implicit) . binderPlicity) binders,
          any (Patterns.constructorBinder environment names) explicits ->
            checkExpression environment names scope (Lambda implicits (Lambda explicits body)) expected
        | any (Patterns.constructorBinder environment names) binders ->
            Patterns.checkCases (patternChecker environment names) scope [Row [maybe Wildcard Name (binderName binder) | binder <- binders] body] expected
      Lambda (Binder {..} : remaining) body -> case expected of
        N.VPi Implicit domain codomain | binderPlicity == Explicit -> introduceImplicit domain codomain
        N.VPi plicity domain codomain -> do
          unless (plicity == binderPlicity) (E.failure "implicit and explicit lambda arguments do not match")
          domainTerm <- quote scope domain
          case binderAnnotation of
            Nothing -> pure ()
            Just annotation -> do
              (_, actual) <- inferAnnotation environment names scope annotation
              E.unify (scopeContext scope) actual domain
          (current, resultType) <- bindDomain scope binderName domain codomain
          bodyTerm <- checkExpression environment names current (Lambda remaining body) resultType
          pure (Core.Lambda plicity domainTerm bodyTerm)
        _ -> inferred expected
      Lambda [] body -> checkExpression environment names scope body expected
      -- a written type with holes learnth from the expected type before the body
      -- is checked. a polymorphic annotation is specialised instead.
      Ascription body annotation -> checkAscription environment names scope body annotation expected (checkExpression environment names)
      Block declarations body -> fst <$> localDefinitions environment names scope declarations (\current -> (,expected) <$> checkExpression environment names current body expected)
      Cases rows -> Patterns.checkCases (patternChecker environment names) scope rows expected
      -- an unknown expected type would depend on the matched values; the
      -- match inferreth a result type without them instead.
      Match {} | flexible expected -> inferred expected
      Match scrutinees rows -> Patterns.checkMatch (patternChecker environment names) scope scrutinees rows expected
      -- an expected implicit input is introduced before any other expression is
      -- checked, so a polymorphic value meeteth a polymorphic type.
      _
        | N.VPi Implicit domain codomain <- expected -> introduceImplicit domain codomain
      _ -> inferred expected
    -- an omitted implicit binder shifteth the context but introduceth no name.
    introduceImplicit domain codomain = do
      domainTerm <- quote scope domain
      (current, resultType) <- bindDomain scope Nothing domain codomain
      Core.Lambda Implicit domainTerm <$> checkExpression environment names current expression resultType
    flexible = \case
      N.VNeutral neutral | (N.NMeta _ _, _) <- N.neutralSpine neutral -> True
      _ -> False
    inferred expected = do
      (term, actual) <- case expression of
        Application function arguments
          | not (recursiveApplication scope function) -> inferApplication environment names scope (Just expected) function arguments
        _ -> inferExpression environment names scope expression
      specialise names scope term actual expected

-- ordinary and recursive bodies share ascription checking. omitted implicit
-- binders enter the scope before an annotation is read; written holes learn
-- from the expected type. recursion must not discard a written annotation.
checkAscription :: K.Environment -> Names -> Scope -> Expression -> Expression -> N.Value -> (Scope -> Expression -> N.Value -> Elaboration Term) -> Elaboration Term
checkAscription environment names scope body annotation expected checkBody =
  E.force expected >>= \case
    N.VPi Implicit domain codomain | not (writtenImplicit annotation) -> do
      domainTerm <- quote scope domain
      (current, resultType) <- bindDomain scope Nothing domain codomain
      Core.Lambda Implicit domainTerm <$> checkAscription environment names current body annotation resultType checkBody
    expected -> do
      (_, annotationValue) <- inferAnnotation environment names scope annotation
      E.force annotationValue >>= \case
        -- a header whose slots leave their types to inference taketh them
        -- from the expected type when the two agree, so the body is checked
        -- against known slot types.
        written@(N.VPi Implicit _ _) ->
          E.attempt (E.unify (scopeContext scope) written expected) >>= \case
            Just () -> checkBody scope body expected
            Nothing -> do
              term <- checkBody scope body written
              specialise names scope term written expected
        written -> do
          E.unify (scopeContext scope) written expected
          checkBody scope body expected
  where
    writtenImplicit = \case
      Product (Parameter {parameterPlicity = Implicit} : _) _ -> True
      Located _ inner -> writtenImplicit inner
      _ -> False

specialise :: Names -> Scope -> Term -> N.Value -> N.Value -> Elaboration Term
specialise names scope = go
  where
    go term actual expected =
      E.force actual >>= \case
        N.VPi Implicit domain codomain
          | shouldSpecialise expected -> do
              (argumentTerm, argumentValue) <- implicitArgument names (scopeContext scope) domain
              resultType <- E.instantiate codomain argumentValue
              go (Apply Implicit term argumentTerm) resultType expected
        actual -> E.unify (scopeContext scope) actual expected >> pure term
    -- an unknown expected type receiveth an instance, as in hindley-milner.
    shouldSpecialise (N.VPi Implicit _ _) = False
    shouldSpecialise _ = True

localDefinitions :: K.Environment -> Names -> Scope -> [Declaration] -> (Scope -> Elaboration (Term, N.Value)) -> Elaboration (Term, N.Value)
localDefinitions _ _ scope [] body = body scope
localDefinitions _ _ _ (InductiveDeclaration {} : _) _ = E.failure "ilk declarations must be top-level"
localDefinitions _ _ _ (HostDeclaration {} : _) _ = E.failure "fremmed bindings must be top-level"
localDefinitions _ _ _ (AssumptionDeclaration {} : _) _ = E.failure "orsetting assumptions must be top-level"
localDefinitions _ _ _ (ImportDeclaration {} : _) _ = E.failure "use and show must be top-level"
localDefinitions _ _ _ (ShownDeclaration {} : _) _ = E.failure "use and show must be top-level"
localDefinitions _ _ _ (ReExportDeclaration {} : _) _ = E.failure "use and show must be top-level"
localDefinitions _ _ _ (FlockDeclaration {} : _) _ = E.failure "flock and bizen must be top-level"
localDefinitions _ _ _ (BizenDeclaration {} : _) _ = E.failure "flock and bizen must be top-level"
localDefinitions environment names scope (Declaration {..} : remaining) body = do
  (value, ty) <- inferDefinition environment names scope declarationName declarationAnnotation declarationBody
  annotation <- quote scope ty
  actual <- eval scope value
  (bodyTerm, resultType) <- localDefinitions environment names (define scope (Just declarationName) actual ty) remaining body
  pure (Let annotation value bodyTerm, resultType)

-- top-level and local lets share annotation and recursion checking. a visible
-- outer binding, including active recursion evidence, still referreth to it.
inferDefinition :: K.Environment -> Names -> Scope -> String -> Maybe Expression -> Expression -> Elaboration (Term, N.Value)
inferDefinition environment names scope name written body =
  -- a let's own name refereth to itself, shadowing an imported name, as
  -- every later reference doth; only a local binding hideth it.
  let visible = Just name `elem` scopeNames scope || isJust (recursiveBinding name scope)
      (annotated, source) = case (written, body) of
        (Nothing, Ascription inner annotation) -> (Just annotation, inner)
        _ -> (written, body)
      recursive = not visible && name `Set.member` referencedNames environment names source
   in case annotated of
        Nothing
          | recursive -> E.failure "a recursive definition needs a type annotation"
          | otherwise -> inferExpression environment names scope source
        Just annotation -> do
          (_, expected) <- inferAnnotation environment names scope annotation
          settleAnnotation environment names
          term <-
            if recursive
              then checkRecursiveExpression environment names scope name source expected
              else checkExpression environment names scope source expected
          pure (term, expected)

checkRecursiveExpression :: K.Environment -> Names -> Scope -> String -> Expression -> N.Value -> Elaboration Term
checkRecursiveExpression environment names scope name body expected = case body of
  Located span inner -> E.located span (checkRecursiveExpression environment names scope name inner expected)
  Ascription inner annotation -> checkAscription environment names scope inner annotation expected (\current -> checkRecursiveExpression environment names current name)
  _ -> Patterns.elaborateRecursive (patternChecker environment names) scope name expected body

-- recursion detection useth free names, respecting source binders.
referencedNames :: K.Environment -> Names -> Expression -> Set.Set String
referencedNames environment names = freeNames (isJust . Patterns.constructorNamed environment names) Set.empty
