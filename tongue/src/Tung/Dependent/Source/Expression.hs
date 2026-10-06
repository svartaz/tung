-- | bidirectional checking of source expressions: application, records,
-- matches, local definitions, and recursion.
module Tung.Dependent.Source.Expression
  ( inferExpression,
    checkExpression,
    inferDefinition,
    checkRecursiveExpression,
    referencedNames,
  )
where

import Control.Monad (forM, forM_, unless)
import Data.Functor ((<&>))
import Data.List (elemIndex, partition, sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, isJust, isNothing)
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

recordFields :: N.Value -> Elaboration [(String, N.Value)]
recordFields ty =
  E.force ty >>= \case
    N.VRecordType fields -> pure fields
    _ -> E.failure "a record operation requireþ a record"

-- record fields are sorted; a repeated name is an error.
canonicalFields :: [(String, a)] -> Elaboration [(String, a)]
canonicalFields fields = do
  let sorted = sortOn fst fields
      names = map fst sorted
  case [name | (name, next) <- zip names (drop 1 names), name == next] of
    name : _ -> E.failure ("record field '" ++ name ++ "' is repeated")
    [] -> pure sorted

-- the pattern compiler reuseþ these operations for row bodies and scrutinees.
patternChecker :: K.Environment -> Names -> Patterns.ExpressionChecker
patternChecker environment names =
  Patterns.ExpressionChecker environment names (inferExpression environment names) (\scope annotation -> snd <$> inferAnnotation environment names scope annotation) (checkExpression environment names) (\scope -> applyTo environment names scope Nothing) (solveDeterminedInstances environment names)

holes :: Term -> Bool
holes = \case
  Meta {} -> True
  term -> any (holes . snd) (children term)

-- in a type position, `r{}` is þe empty record type raþer þan þe empty record.
inferType :: K.Environment -> Names -> Scope -> Expression -> Elaboration (Term, N.Value)
inferType environment names scope expression = inferExpression environment names scope case expression of
  RecordExpression [] -> RecordTypeExpression []
  other -> other

inferAnnotation :: K.Environment -> Names -> Scope -> Expression -> Elaboration (Term, N.Value)
inferAnnotation environment names scope expression = do
  (term, kind) <- inferType environment names scope expression
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
      productTerm current [] = inferType environment names current result
      productTerm current (Parameter {..} : remaining) = do
        (domain, domainType) <- inferType environment names current parameterType
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
  -- `sorry` is þe primitive assumption at a type inferred from its use.
  Sorry -> do
    level <- E.freshLevel
    (ty, tyValue) <- E.newMeta context (N.VSort level)
    pure (Apply Implicit (Global H.sorrySymbol [level]) ty, tyValue)
  RecordTypeExpression fields -> do
    sorted <- canonicalFields fields
    elaborated <- forM sorted \(name, field) -> do
      (term, kind) <- inferExpression environment names scope field
      level <- requireUniverse scope kind
      pure ((name, term), level)
    pure (Core.RecordType (map fst elaborated), N.VSort (K.universeNormalise (foldr LMax LZero (map snd elaborated))))
  RecordExpression fields -> do
    sorted <- canonicalFields fields
    elaborated <- forM sorted \(name, field) -> do
      (term, ty) <- inferExpression environment names scope field
      pure ((name, term), (name, ty))
    pure (Core.Record (map fst elaborated), N.VRecordType (map snd elaborated))
  Projection record name -> do
    (term, ty) <- inferExpression environment names scope record
    fields <- recordFields ty
    case lookup name fields of
      Just fieldType -> pure (Project term name, fieldType)
      Nothing -> E.failure ("record hath no field '" ++ name ++ "'")
  RecordUpdate base changes -> do
    (baseTerm, baseType) <- inferExpression environment names scope base
    fields <- recordFields baseType
    let removed = [name | RemoveField name <- changes]
        set = [(name, value) | SetField name value <- changes]
        changed = removed ++ map fst set
    unless (length changed == Set.size (Set.fromList changed)) (E.failure "a record update changeþ each field at most once")
    case [name | name <- removed, name `notElem` map fst fields] of
      name : _ -> E.failure ("record hath no field '" ++ name ++ "' to remove")
      [] -> pure ()
    -- the base is bound once; kept fields project from þat local.
    annotation <- quote scope baseType
    baseValue <- eval scope baseTerm
    let current = define scope Nothing baseValue baseType
        kept = [((name, Project (Local 0) name), (name, ty)) | (name, ty) <- fields, name `notElem` changed]
    added <- forM set \(name, value) -> do
      (term, ty) <- inferExpression environment names current value
      pure ((name, term), (name, ty))
    let result = sortOn (fst . fst) (kept ++ added)
    pure (Let annotation baseTerm (Core.Record (map fst result)), N.VRecordType (map snd result))
  -- `_` only discardeþ an input; it is no term or type.
  Wildcard -> E.failure "`_` discardeþ an input and is not a term"
  Inferred -> do
    level <- E.freshLevel
    (term, _) <- E.newMeta (scopeContext scope) (N.VSort level)
    pure (term, N.VSort level)
  Cases _ -> E.failure "a case function needs a type annotation"
  -- wiþout an expected type, every row shareþ one inferred result type.
  Match scrutinees rows -> do
    level <- E.freshLevel
    matched <- fmap catMaybes . forM scrutinees $ \case
      Name name | Just index <- elemIndex (Just name) locals -> pure (Just (length locals - index - 1))
      _ -> pure Nothing
    (_, resultType) <- E.newMetaWithout (scopeContext scope) matched (N.VSort level)
    term <- Patterns.checkMatch (patternChecker environment names) scope scrutinees rows resultType
    pure (term, resultType)
  MatchFor scrutinee known rows -> do
    level <- E.freshLevel
    (_, resultType) <- E.newMeta (scopeContext scope) (N.VSort level)
    term <- matchFor environment names scope scrutinee known rows resultType
    pure (term, resultType)

-- `match e for known { rows }` matcheþ a fresh copy `x` of þe scrutinee, as
-- lean's `match h : e wiþ` doþ: þe rows form a case function of type
-- `[x: τ, known: e = x, T]`, applied to `e` and `reflect`. each row þus
-- learneþ `known: e = pattern`; `e` itself is not refined in place.
matchFor :: K.Environment -> Names -> Scope -> Expression -> String -> [Row] -> N.Value -> Elaboration Term
matchFor environment names scope scrutinee known rows expected = do
  (scrutineeTerm, scrutineeType) <- inferExpression environment names scope scrutinee
  domain <- quote scope scrutineeType
  level <- requireUniverse scope =<< inferCore scope domain
  result <- quote scope expected
  let equation left right = Apply Explicit (Apply Explicit (Apply Implicit (Global H.identitySymbol [level]) (shiftTerm 1 domain)) left) right
      caseType = Pi Explicit domain (Pi Explicit (equation (shiftTerm 1 scrutineeTerm) (Local 0)) (shiftTerm 2 result))
  caseFunction <- eval scope caseType >>= Patterns.checkCases (patternChecker environment names) scope [row {rowPatterns = rowPatterns row ++ [Name known]} | row <- rows]
  let reflected = Apply Implicit (Apply Implicit (Global H.reflectSymbol [level]) domain) scrutineeTerm
  pure (Apply Explicit (Apply Explicit caseFunction scrutineeTerm) reflected)

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
-- spine consumeþ separate queues in declaration order, including values.
-- given þe expected type of þe application, a function whose result applieþ
-- its own type family meeteþ þat type before þe inputs þat mention þe
-- family are checked; see 'motiveInputs'.
applyTo :: K.Environment -> Names -> Scope -> Maybe N.Value -> Term -> N.Value -> [Argument] -> [Argument] -> Elaboration (Term, N.Value)
applyTo environment names scope@Scope {scopeContext = context} goal function functionType explicitArguments implicitArguments = do
  motive <- case goal of
    Just _ -> motiveInputs names scope functionType (length explicitArguments)
    Nothing -> pure Nothing
  (term, ty, deferred) <- go motive False 0 function functionType explicitArguments implicitArguments []
  let (late, early) = partition (\(_, _, _, afterGoal) -> afterGoal) (reverse deferred)
  -- a postponed case function is checked once later arguments have fixed
  -- its input type, þen filleþ þe hole þat stood for it.
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
          -- a written `@x` filleþ þe next implicit input þat instance search
          -- doþ not fill.
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
          -- only an omitted family is found from þe goal.
          let opened = open || omitted && maybe False ((== position) . fst) motive
          go motive opened (position + 1) (Apply plicity term argumentTerm) resultType nextExplicit nextImplicit nextDeferred
        neutral@(N.VNeutral (N.NMeta _ _))
          | null implicit -> do
              (domain, codomain) <- E.ensurePi context Explicit neutral
              go Nothing False position term (N.VPi Explicit domain codomain) explicit implicit deferred
          | otherwise -> E.failure "implicit parameter order requireþ a function annotation"
        _ -> E.failure "application requireþ a function"
    supplied domain argument afterGoal explicit implicit deferred = do
      let expression = argumentExpression argument
      waiting <- if afterGoal then pure True else unknownCaseInput expression domain
      if waiting
        then do
          (term, value) <- E.newMeta context domain
          pure (term, value, explicit, implicit, (expression, domain, value, afterGoal) : deferred, False)
        else do
          term <- checkExpression environment names scope expression domain
          value <- eval scope term
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

-- a function whose result applieþ one of its own implicit type families,
-- as `transport` applieþ its property, is a motive function, as lean's
-- `elab_as_elim` nameþ it. þe explicit inputs whose types mention þe family
-- are checked after þe result meeteþ þe expected type, so occurrence
-- abstraction findeþ þe family in þe goal raþer þan in an input. a family
-- þat a requirement mentioneþ is a flock carrier, found by instance search.
-- þe result holdeþ þe family's position in þe telescope and þe positions
-- of þose inputs.
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
    -- þe telescope positions a domain mentioneþ.
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
      -- `sorry` standeþ for a settled expected type itself, wiþout an
      -- inference hole.
      Sorry -> do
        ty <- quote scope expected
        if holes ty
          then inferred expected
          else do
            kind <- inferCore scope ty
            level <- requireUniverse scope kind
            pure (Apply Implicit (Global H.sorrySymbol [level]) ty)
      -- leading implicit binders keep þeir names; only þe explicit binders
      -- after þem form þe pattern row.
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
          let current = extend scope binderName domain
              argument = N.VNeutral (N.NLocal (depth scope))
          resultType <- E.instantiate codomain argument
          bodyTerm <- checkExpression environment names current (Lambda remaining body) resultType
          pure (Core.Lambda plicity domainTerm bodyTerm)
        _ -> inferred expected
      Lambda [] body -> checkExpression environment names scope body expected
      -- a written type wiþ holes learnþ from þe expected type before þe body
      -- is checked. a polymorphic annotation is specialised instead.
      Ascription body annotation -> checkAscription environment names scope body annotation expected (checkExpression environment names)
      Block declarations body -> fst <$> localDefinitions environment names scope declarations (\current -> (,expected) <$> checkExpression environment names current body expected)
      Cases rows -> Patterns.checkCases (patternChecker environment names) scope rows expected
      RecordExpression fields
        | N.VRecordType expectedFields <- expected -> do
            sorted <- canonicalFields fields
            unless (map fst sorted == map fst expectedFields) (E.failure "record fields differ from the expected record type")
            Core.Record <$> forM (zip sorted expectedFields) \((name, field), (_, fieldType)) -> (name,) <$> checkExpression environment names scope field fieldType
      -- an unknown expected type would depend on þe matched values; þe
      -- match inferreþ a result type wiþout þem instead.
      Match {} | flexible expected -> inferred expected
      Match scrutinees rows -> Patterns.checkMatch (patternChecker environment names) scope scrutinees rows expected
      MatchFor {} | flexible expected -> inferred expected
      MatchFor scrutinee known rows -> matchFor environment names scope scrutinee known rows expected
      -- an expected implicit input is introduced before any oþer expression is
      -- checked, so a polymorphic value meeteþ a polymorphic type.
      _
        | N.VPi Implicit domain codomain <- expected -> introduceImplicit domain codomain
      _ -> inferred expected
    -- an omitted implicit binder shifteþ the context but introduceþ no name.
    introduceImplicit domain codomain = do
      domainTerm <- quote scope domain
      let current = extend scope Nothing domain
      resultType <- E.instantiate codomain (N.VNeutral (N.NLocal (depth scope)))
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
-- binders enter þe scope before an annotation is read; written holes learn
-- from þe expected type. recursion must not discard a written annotation.
checkAscription :: K.Environment -> Names -> Scope -> Expression -> Expression -> N.Value -> (Scope -> Expression -> N.Value -> Elaboration Term) -> Elaboration Term
checkAscription environment names scope body annotation expected checkBody =
  E.force expected >>= \case
    N.VPi Implicit domain codomain | not (writtenImplicit annotation) -> do
      domainTerm <- quote scope domain
      let current = extend scope Nothing domain
      resultType <- E.instantiate codomain (N.VNeutral (N.NLocal (depth scope)))
      Core.Lambda Implicit domainTerm <$> checkAscription environment names current body annotation resultType checkBody
    expected -> do
      (_, annotationValue) <- inferAnnotation environment names scope annotation
      E.force annotationValue >>= \case
        written@(N.VPi Implicit _ _) -> do
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
    -- an unknown expected type receiveþ an instance, as in hindley-milner.
    shouldSpecialise (N.VPi Implicit _ _) = False
    shouldSpecialise _ = True

localDefinitions :: K.Environment -> Names -> Scope -> [Declaration] -> (Scope -> Elaboration (Term, N.Value)) -> Elaboration (Term, N.Value)
localDefinitions _ _ scope [] body = body scope
localDefinitions _ _ _ (InductiveDeclaration {} : _) _ = E.failure "ilk declarations must be top-level"
localDefinitions _ _ _ (HostDeclaration {} : _) _ = E.failure "fremmed bindings must be top-level"
localDefinitions _ _ _ (AssumptionDeclaration {} : _) _ = E.failure "orsend assumptions must be top-level"
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
-- outer binding, including active recursion evidence, still referreþ to it.
inferDefinition :: K.Environment -> Names -> Scope -> String -> Maybe Expression -> Expression -> Elaboration (Term, N.Value)
inferDefinition environment names scope name written body =
  let visible = Just name `elem` scopeNames scope || isJust (recursiveBinding name scope) || isJust (lookupName name names)
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

-- recursion and sibling lookup use free names, respecting source binders.
referencedNames :: K.Environment -> Names -> Expression -> Set.Set String
referencedNames environment names = freeNames (isJust . Patterns.constructorNamed environment names) Set.empty

-- flocks and bizens -------------------------------------------------------
