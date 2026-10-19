{-# LANGUAGE ViewPatterns #-}

-- | checked inductive families and their generated induction principles.
-- nested fields are certified as specialised mutual families. public container
-- types and every generated computation rule are independently rechecked.
module Tung.Dependent.Inductive
  ( InductiveDeclaration (..),
    defineInductive,
    defineInductives,
    inferInductive,
    inferInductives,
  )
where

import Control.Monad (foldM, forM, forM_, unless, when, zipWithM)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (get, modify, runStateT)
import Data.Foldable (traverse_)
import Data.Functor.Identity (Identity (..))
import Data.List (elemIndex, find, nub)
import Data.Map.Strict qualified as Map
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Syntax
import Tung.Dependent.Universe qualified as U
import Tung.Identity (SymbolId (..), inductionSymbol)

data InductiveDeclaration = InductiveDeclaration
  { inductiveName :: SymbolId,
    inductiveEliminator :: SymbolId,
    inductiveParameters :: Int,
    inductiveUniverses :: Int,
    inductiveConstraints :: [Constraint],
    inductiveType :: Term,
    inductiveConstructors :: [(SymbolId, Term)]
  }
  deriving stock (Eq, Show)

type Telescope = [(Plicity, Term)]

data Constructor = Constructor
  { constructorName :: SymbolId,
    constructorFamily :: SymbolId,
    constructorType :: Term,
    constructorFields :: [(Plicity, Term, Maybe SymbolId)],
    constructorIndices :: [(Plicity, Term)]
  }

data Family = Family
  { familyDeclaration :: InductiveDeclaration,
    familyParameters :: Telescope,
    familyIndices :: Telescope,
    familySort :: Level
  }

-- rigid declarations must prove every obligation from their exported universe
-- constraints. insertion is atomic: no partly checked family is returned.
defineInductive :: K.Environment -> InductiveDeclaration -> Either String K.Environment
defineInductive environment declaration = defineInductives environment [declaration]

defineInductives :: K.Environment -> [InductiveDeclaration] -> Either String K.Environment
defineInductives environment [] = Right environment
defineInductives environment declarations = do
  traverse_ (\declaration -> validateSyntax (Just (inductiveUniverses declaration)) False declaration) declarations
  let constraints = nub (concatMap inductiveConstraints declarations)
  universes <- maybe (Left "inconsistent universe constraints") Right (U.satisfy constraints)
  (result, U.universeConstraints -> obligations) <- runStateT (build environment declarations) universes
  unless (U.entailsAll constraints (K.openObligations constraints obligations)) (Left "unproved universe constraint in inductive declaration")
  pure result

-- source staging useth one fixed vector of distinct universe placeholders for
-- self references. explicit universe arguments belong to 'defineInductive'.
-- joint generalisation can introduce constructor-only parameters, so each
-- placeholder vector is then widened to the group's complete canonical vector.
inferInductive :: K.Environment -> SymbolId -> SymbolId -> Int -> Term -> [(SymbolId, Term)] -> [Constraint] -> Either String K.Environment
inferInductive environment name eliminator parameters annotation constructors constraints =
  inferInductives environment [InductiveDeclaration name eliminator parameters 0 constraints annotation constructors]

inferInductives :: K.Environment -> [InductiveDeclaration] -> Either String K.Environment
inferInductives environment [] = Right environment
inferInductives environment raw@(first : _) = do
  traverse_ (validateSyntax Nothing True) raw
  let terms = concatMap signatures raw
      families = map inductiveName raw
  traverse_
    ( \family -> do
        let arguments = nub (concatMap (selfUniverses family) terms)
        unless (length arguments <= 1) (Left "recursive family universe arguments must remain uniform")
        traverse_ checkPlaceholders arguments
    )
    families
  (universes, assumptions, generalised) <- K.generaliseTerms terms (nub (concatMap inductiveConstraints raw))
  declarations <- assemble universes assumptions families raw generalised
  (K.Environment built, U.universeConstraints -> obligations) <- runStateT (build environment declarations) (U.universes assumptions)
  info <- inductiveInfo built (inductiveName first)
  let constraints = nub obligations
      auxiliary = drop (length declarations) (inductiveFamilies info)
      names = concatMap declaredNames declarations ++ concat [[target, inductionSymbol target] | target <- auxiliary]
      final = foldr (Map.adjust (\definition -> definition {definitionConstraints = constraints})) built names
  traverse_ (validateSyntax (Just universes) False . (\declaration -> declaration {inductiveConstraints = constraints})) declarations
  -- adding inferred assumptions cannot alter positivity or the generated
  -- eliminators. recheck final signatures rigidly, without rebuilding them.
  (_, U.universeConstraints -> rigid) <- runStateT (traverse_ (K.checkType final K.emptyContext . definitionType . (final Map.!)) names) (U.universes constraints)
  unless (U.entailsAll constraints (K.openObligations constraints rigid)) (Left "unproved universe constraint in inductive declaration")
  pure (K.Environment final)
  where
    signatures declaration = inductiveType declaration : map snd (inductiveConstructors declaration)
    assemble _ _ _ [] [] = Right []
    assemble universes assumptions families (declaration : rest) (family : remaining) = do
      let count = length (inductiveConstructors declaration)
          (constructors, following) = splitAt count remaining
          canonical = map LParam [0 .. universes - 1]
          replace = replaceFamilyUniverses families canonical
          updated = declaration {inductiveUniverses = universes, inductiveConstraints = assumptions, inductiveType = replace family, inductiveConstructors = zip (map fst (inductiveConstructors declaration)) (map replace constructors)}
      unless (length constructors == count) (Left "missing inductive constructor signature")
      (updated :) <$> assemble universes assumptions families rest following
    assemble _ _ _ _ _ = Left "missing inductive family signature"
    checkPlaceholders levels = do
      let identities = [identity | LMeta identity <- levels]
      unless (length identities == length levels && length identities == length (nub identities)) (Left "inductive self references requireth distinct inference placeholders")

declaredNames :: InductiveDeclaration -> [SymbolId]
declaredNames InductiveDeclaration {..} = inductiveName : inductiveEliminator : map fst inductiveConstructors

validateSyntax :: Maybe Int -> Bool -> InductiveDeclaration -> Either String ()
validateSyntax bound holes InductiveDeclaration {..} = do
  when (inductiveParameters < 0) (Left "negative inductive parameter count")
  when (inductiveUniverses < 0) (Left "negative inductive universe count")
  let signatures = inductiveType : map snd inductiveConstructors
  traverse_ K.rejectMetas signatures
  traverse_ (K.validLevel bound holes) (concatMap termLevels signatures ++ concatMap constraintLevels inductiveConstraints)
  unless (U.satisfiable inductiveConstraints) (Left "inconsistent universe constraints")

build :: K.Environment -> [InductiveDeclaration] -> K.Typing K.Environment
build = buildWithNested True

buildWithNested :: Bool -> K.Environment -> [InductiveDeclaration] -> K.Typing K.Environment
buildWithNested _ environment [] = pure environment
buildWithNested allowNested environment@(K.Environment globals) declarations@(first : _) = do
  let names = concatMap declaredNames declarations
      families = map inductiveName declarations
      universes = inductiveUniverses first
      constraints = nub (concatMap inductiveConstraints declarations)
  unless (length names == length (nub names) && all (`Map.notMember` globals) names) (K.failure "duplicate inductive declaration name")
  unless (all ((== universes) . inductiveUniverses) declarations) (K.failure "mutual inductive declarations require shared universe parameters")
  when (length declarations > 1) $
    unless (all (\declaration -> inductiveEliminator declaration == inductionSymbol (inductiveName declaration)) declarations) (K.failure "mutual inductive eliminators require canonical identities")
  headers <- forM declarations \declaration@InductiveDeclaration {..} -> do
    -- signatures are checked before any peer family entereth the environment;
    -- inductive-recursive kinds are outside this strictly positive fragment.
    when (containsFamilies families inductiveType) (K.failure "inductive family signatures cannot depend on their group")
    K.checkType globals K.emptyContext inductiveType
    normal <- lift (N.normalise globals 0 inductiveType)
    let (binders, result) = termTelescope normal
        (parameters, indices) = splitAt inductiveParameters binders
    unless (length parameters == inductiveParameters) (K.failure "inductive parameter count exceedeth family signature")
    target <- case result of
      Sort level -> pure level
      _ -> K.failure "inductive family signature must end in a universe"
    pure (Family (declaration {inductiveType = normal, inductiveConstraints = constraints}) parameters indices target)
  case headers of
    header : rest -> traverse_ (sharedParameters globals header) rest
    [] -> pure ()
  let staged = foldl (\environment family -> Map.insert (inductiveName (familyDeclaration family)) (familyDefinition families family [] []) environment) globals headers
      peers = Map.fromList [(inductiveName (familyDeclaration family), family) | family <- headers]
  if allowNested && any (potentialNested families . snd) (concatMap inductiveConstructors declarations)
    then do
      (translated, targets) <- specialiseNested staged peers headers
      if null targets
        then finishInductives globals headers staged peers
        else buildWithNested False environment (translated ++ map nestedDeclaration targets) >>= restoreNested globals headers targets
    else finishInductives globals headers staged peers

finishInductives :: Globals -> [Family] -> Globals -> Map.Map SymbolId Family -> K.Typing K.Environment
finishInductives _ headers@(header : _) staged peers = do
  let first = familyDeclaration header
      families = map (inductiveName . familyDeclaration) headers
      universes = inductiveUniverses first
      constraints = nub (concatMap (inductiveConstraints . familyDeclaration) headers)
      entry = Definition universes constraints
  checked <- forM headers \family@Family {familyDeclaration = InductiveDeclaration {inductiveConstructors}} ->
    traverse (checkConstructor staged peers family) inductiveConstructors
  let familyGlobals = foldl (\environment (family, own) -> Map.insert (inductiveName (familyDeclaration family)) (familyDefinition families family own []) environment) staged (zip headers checked)
      constructorGlobals = foldl insertConstructor familyGlobals (concatMap (zip [0 ..]) checked)
      insertConstructor environment (index, Constructor {..}) = Map.insert constructorName (entry constructorType (DataConstructor constructorFamily index)) environment
      constructors = concat checked
  recursors <- forM headers \family@Family {familyDeclaration = InductiveDeclaration {..}} -> do
    annotation <- lift (generateRecursor headers constructors family)
    K.checkType constructorGlobals K.emptyContext annotation
    pure (inductiveEliminator, Definition (universes + length families) constraints annotation (Eliminator inductiveName))
  rules <- lift (traverse (generateRule headers constructors) constructors)
  let withRules =
        foldl
          ( \environment (family, own) ->
              let name = inductiveName (familyDeclaration family)
                  ownRules = [rule | (constructor, rule) <- zip constructors rules, constructorFamily constructor == name]
               in Map.insert name (familyDefinition families family own ownRules) environment
          )
          constructorGlobals
          (zip headers checked)
  let final = foldr (uncurry Map.insert) withRules recursors
  checkRules final [(inductiveName (familyDeclaration family), inductiveEliminator (familyDeclaration family)) | family <- headers]
  pure (K.Environment final)
finishInductives globals [] _ _ = pure (K.Environment globals)

familyDefinition :: [SymbolId] -> Family -> [Constructor] -> [Term] -> Definition
familyDefinition families Family {familyDeclaration = InductiveDeclaration {..}, familyIndices} constructors rules =
  Definition
    inductiveUniverses
    inductiveConstraints
    inductiveType
    ( TypeConstructor
        ( InductiveInfo
            families
            inductiveParameters
            inductiveParameters
            (map fst familyIndices)
            [(constructorName constructor, constructorFields constructor) | constructor <- constructors]
            rules
        )
    )

-- an auxiliary target is a checked alias for an ordinary container application,
-- never a new public nominal type. its temporary constructors exist only while
-- the ordinary mutual checker certifieth positivity and termination.
data NestedTarget = NestedTarget
  { nestedDeclaration :: InductiveDeclaration,
    nestedCarrier :: Term,
    nestedParameterCount :: Int,
    nestedConstructors :: [(SymbolId, SymbolId, Term)]
  }

potentialNested :: [SymbolId] -> Term -> Bool
potentialNested families term =
  ( case termSpine term of
      (Global family _, arguments) | family `elem` families -> any (potentialNested families . snd) arguments
      (_, arguments@(_ : _)) -> any (containsFamilies families . snd) arguments
      _ -> False
  )
    || any (potentialNested families . snd) (children term)

specialiseNested :: Globals -> Map.Map SymbolId Family -> [Family] -> K.Typing ([InductiveDeclaration], [NestedTarget])
specialiseNested _ _ [] = pure ([], [])
specialiseNested globals peers families@(first : _) = do
  runStateT (traverse rewriteDeclaration families <* close 0) []
  where
    declaration = familyDeclaration first
    parameters = familyParameters first
    parameterCount = length parameters
    levels = map LParam [0 .. inductiveUniverses declaration - 1]
    rootNames = Map.keys peers
    wrap constructor body = foldr (\(_, domain) result -> constructor Implicit domain result) body parameters
    parameterContext = foldM (\context (_, domain) -> K.bind context <$> K.evaluate globals context domain) K.emptyContext parameters
    rewriteDeclaration family = do
      constructors <- forM (inductiveConstructors (familyDeclaration family)) \(name, annotation) -> do
        -- check the original signature before any parameter is specialised:
        -- an erased or phantom container parameter must not hide ill typing.
        lift (K.checkType globals K.emptyContext annotation)
        normal <- lift (lift (N.normalise globals 0 annotation))
        (name,) <$> rewrite 0 normal
      pure (familyDeclaration family) {inductiveConstructors = constructors}
    rewrite depth term = case termSpine term of
      (Global name _, _) | Just family <- Map.lookup name peers -> do
        -- every source-family application is saturated and uniform, even
        -- when hidden inside a fixed container argument.
        lift (validateOccurrence depth family term)
        pure term
      (Global container universeArguments, arguments)
        | any (containsFamilies rootNames . snd) arguments,
          Just Definition {definitionBody = TypeConstructor info} <- Map.lookup container globals -> do
            unless (null (inductiveIndexPlicities info)) (lift (K.failure "nested recursion in indexed containers is not supported"))
            unless (length arguments == inductiveParameterCount info) (lift (K.failure "nested container application must be saturated"))
            traverse_ (lift . validateRootArguments depth . snd) arguments
            carrier <- lift (lift (projectParameters depth term))
            targets <- get
            target <- case find ((== carrier) . nestedCarrier) targets of
              Just target -> pure (nestedDeclaration target)
              Nothing -> do
                -- specialise every peer with the same fixed parameter vector.
                forM_ [peer | peer <- inductiveFamilies info, Just Definition {definitionBody = TypeConstructor _} <- [Map.lookup peer globals]] \peer -> do
                  let candidate = applyArguments (Global peer universeArguments) (snd (termSpine carrier))
                  existing <- get
                  unless (any ((== candidate) . nestedCarrier) existing) (addTarget peer universeArguments candidate)
                created <- get
                maybe (lift (K.failure "missing nested target")) (pure . nestedDeclaration) (find ((== carrier) . nestedCarrier) created)
            pure (applyArguments (Global (inductiveName target) levels) [(plicity, Local (depth - position - 1)) | (position, (plicity, _)) <- zip [0 ..] parameters])
      _ -> mapChildren (\binders -> rewrite (depth + binders)) term
    validateRootArguments depth term = case termSpine term of
      (Global name _, _) | Just family <- Map.lookup name peers -> validateOccurrence depth family term
      _ -> traverse_ (\(binders, child) -> validateRootArguments (depth + binders) child) (children term)
    validateOccurrence depth family term = do
      let args = snd (termSpine term)
          expected = map fst (familyParameters family ++ familyIndices family)
      unless (map fst args == expected) (K.failure "inductive result requireth every parameter and index")
      when (any (containsFamilies rootNames . snd) args) (K.failure "inductive family cannot occur inside its arguments")
      unless (map snd (take parameterCount args) == [Local (depth - position - 1) | position <- [0 .. parameterCount - 1]]) (K.failure "nested recursive parameters must remain uniform")
      case fst (termSpine term) of
        Global _ actual -> do
          unless (length actual == length levels) (K.failure "wrong number of inductive universe arguments")
          traverse_ K.oblige (zipWith LevelEqual actual levels)
        _ -> K.failure "invalid nested family application"
    -- only the shared parameter telescope may appear in a specialisation key.
    -- constructor fields and function inputs cannot grow an infinite worklist.
    projectParameters depth = traverseScoped \bound term descend -> case term of
      Local index
        | index >= bound ->
            let level = depth - (index - bound) - 1
             in if level >= 0 && level < parameterCount
                  then pure (Local (parameterCount - level - 1 + bound))
                  else Left "nested container arguments cannot depend on constructor-local variables"
      _ -> descend
    addTarget container universeArguments carrier = do
      existing <- get
      let SymbolId owner root = inductiveName declaration
          label = SymbolId owner ("#nested_" ++ root ++ "_" ++ show (length existing))
          kind = foldr (uncurry Pi) (Sort (familySort first)) parameters
          args = snd (termSpine carrier)
      when (Map.member label globals) (lift (K.failure "duplicate nested target identity"))
      context <- lift parameterContext
      lift (K.inferTerm globals context carrier) >>= \case
        N.VSort sort -> lift (K.oblige (LevelEqual sort (familySort first)))
        _ -> lift (K.failure "nested container application must be an ilk")
      info <- lift (lift (inductiveInfo globals container))
      constructors <- forM (zip [0 :: Int ..] (inductiveConstructorInfo info)) \(index, (original, _)) -> do
        let temporary = SymbolId owner ("#nested_constructor_" ++ root ++ "_" ++ show (length existing) ++ "_" ++ show index)
            applied = applyArguments (Global original universeArguments) [(Implicit, argument) | (_, argument) <- args]
        fieldType <- lift (K.inferTerm globals context applied)
        annotation <- lift (lift (N.quote globals parameterCount fieldType))
        pure (temporary, original, wrap Lambda applied, wrap Pi annotation)
      let temporary = declaration {inductiveName = label, inductiveEliminator = inductionSymbol label, inductiveType = kind, inductiveConstructors = [(name, annotation) | (name, _, _, annotation) <- constructors]}
      modify (++ [NestedTarget temporary carrier (inductiveParameterCount info) [(name, original, body) | (name, original, body, _) <- constructors]])
    close position = do
      targets <- get
      case drop position targets of
        target : _ -> do
          constructors <- traverse (traverse (rewrite 0)) (inductiveConstructors (nestedDeclaration target))
          modify (zipWith (\index current -> if index == position then current {nestedDeclaration = (nestedDeclaration current) {inductiveConstructors = constructors}} else current) [0 ..])
          close (position + 1)
        [] -> pure ()

restoreNested :: Globals -> [Family] -> [NestedTarget] -> K.Environment -> K.Typing K.Environment
restoreNested _ [] _ certified = pure certified
restoreNested original families@(first : _) targets (K.Environment certified) = do
  let targetTable = Map.fromList [(inductiveName (nestedDeclaration target), target) | target <- targets]
      wrappers =
        Map.fromList
          ( [(inductiveName (nestedDeclaration target), foldr (uncurry Lambda) (nestedCarrier target) (familyParameters first)) | target <- targets]
              ++ [(temporary, body) | target <- targets, (temporary, _, body) <- nestedConstructors target]
          )
      constructorNames = Map.fromList [(temporary, actual) | target <- targets, (temporary, actual, _) <- nestedConstructors target]
      restore =
        runIdentity
          . traverseScoped
            ( \_ term descend -> case term of
                Global name _ | Just body <- Map.lookup name wrappers -> pure body
                _ -> descend
            )
      metadata info =
        info
          { inductiveConstructorInfo = [(Map.findWithDefault name name constructorNames, [(plicity, restore ty, recursive) | (plicity, ty, recursive) <- fields]) | (name, fields) <- inductiveConstructorInfo info],
            inductiveRules = map restore (inductiveRules info)
          }
      rewrite name definition@Definition {definitionBody} =
        definition
          { definitionType = restore (definitionType definition),
            definitionBody = case definitionBody of
              TypeConstructor info | Just target <- Map.lookup name targetTable -> EliminationTarget ((metadata info) {inductiveConstructorParameterCount = nestedParameterCount target}) (wrappers Map.! name)
              TypeConstructor info -> TypeConstructor (metadata info)
              body -> body
          }
      own = Map.mapWithKey rewrite (Map.difference certified original)
      public = foldr Map.delete own (Map.keys constructorNames)
      final = Map.union public original
      -- recursors are opaque during the independent rule check. the clone
      -- certificate justifieth recursion; typing alone doth not prove it.
      members = [(inductiveName declaration, inductiveEliminator declaration) | declaration <- map familyDeclaration families ++ map nestedDeclaration targets]
      opaque = opaqueRecursors final (map snd members)
  forM_ (Map.elems public) \definition@Definition {definitionType, definitionBody} -> do
    K.checkType opaque K.emptyContext definitionType
    case definitionBody of
      EliminationTarget _ body -> K.checkTerm opaque K.emptyContext body definitionType
      _ -> pure ()
    lift (traverse_ (K.validLevel (Just (definitionUniverses definition)) False) (termLevels definitionType))
  checkRules final members
  pure (K.Environment final)

opaqueRecursors :: Globals -> [SymbolId] -> Globals
opaqueRecursors = foldr (Map.adjust (\definition -> definition {definitionBody = Assumption}))

-- the native and restored rules use one check. motives and methods have the
-- common prefix; actual fields follow without hypothesis binders. a private
-- target's alias supplieth the original constructor parameters and universes.
checkRules :: Globals -> [(SymbolId, SymbolId)] -> K.Typing ()
checkRules _ [] = pure ()
checkRules globals members@((first, firstRecursor) : _) = do
  firstInfo <- lift (inductiveInfo globals first)
  methods <- lift (inductiveMethods globals firstInfo)
  recursor <- maybe (K.failure "missing inductive recursor") pure (Map.lookup firstRecursor globals)
  let parameters = inductiveParameterCount firstInfo
      count = parameters + length members + length methods
      prefix = take count (fst (termTelescope (definitionType recursor)))
      opaque = opaqueRecursors globals (map snd members)
  context <- foldM (\current (_, domain) -> K.bind current <$> K.evaluate opaque current domain) K.emptyContext prefix
  forM_ (zip [parameters ..] members) \(motive, (family, _)) -> do
    info <- lift (inductiveInfo globals family)
    definition <- maybe (K.failure "missing inductive target") pure (Map.lookup family globals)
    let levels = map LParam [0 .. definitionUniverses definition - 1]
    unless (length (inductiveConstructorInfo info) == length (inductiveRules info)) (K.failure "missing inductive computation rule")
    forM_ (zip (inductiveConstructorInfo info) (inductiveRules info)) \((constructor, fields), rule) -> do
      fieldContext <-
        foldM
          ( \current (_, annotation, _) -> do
              let preceding = K.contextDepth current - count
              moved <- lift (renameTerm ([0 .. parameters - 1] ++ [count .. count + preceding - 1]) (count + preceding) annotation)
              K.bind current <$> K.evaluate opaque current moved
          )
          context
          fields
      let depth = K.contextDepth fieldContext
          shared = [(Implicit, localAt depth index) | index <- [0 .. parameters - 1]]
          values = [(plicity, localAt depth (count + position)) | (position, (plicity, _, _)) <- zip [0 ..] fields]
      value <- case definitionBody definition of
        EliminationTarget _ _ -> do
          let visibility = map fst (take parameters (fst (termTelescope (definitionType definition))))
              application = applyArguments (Global family levels) (zip visibility (map snd shared))
          carrier <- K.evaluate opaque fieldContext application >>= lift . N.quote opaque depth
          case termSpine carrier of
            (Global _ actualLevels, arguments) -> pure (applyArguments (Global constructor actualLevels) ([(Implicit, argument) | (_, argument) <- arguments] ++ values))
            _ -> K.failure "invalid nested target carrier"
        _ -> pure (applyArguments (Global constructor levels) (shared ++ values))
      resultType <- K.inferTerm opaque fieldContext value >>= lift . N.quote opaque depth
      let indices = drop (inductiveConstructorParameterCount info) (snd (termSpine resultType))
          expected = applyArguments (localAt depth motive) (indices ++ [(Explicit, value)])
      K.checkTerm opaque fieldContext rule expected

sharedParameters :: Globals -> Family -> Family -> K.Typing ()
sharedParameters globals left right = do
  unless (length (familyParameters left) == length (familyParameters right)) (K.failure "mutual inductive families require shared parameters")
  compareDomains K.emptyContext (familyParameters left) (familyParameters right)
  K.oblige (LevelEqual (familySort left) (familySort right))
  where
    compareDomains _ [] [] = pure ()
    compareDomains context ((plicity, domain) : rest) ((other, annotation) : remaining) = do
      unless (plicity == other) (K.failure "mutual inductive parameter visibility must agree")
      expected <- K.evaluate globals context domain
      actual <- K.evaluate globals context annotation
      K.convert globals context actual expected
      compareDomains (K.bind context expected) rest remaining
    compareDomains _ _ _ = K.failure "mutual inductive families require shared parameters"

checkConstructor :: Globals -> Map.Map SymbolId Family -> Family -> (SymbolId, Term) -> K.Typing Constructor
checkConstructor globals peers family@Family {familyDeclaration = InductiveDeclaration {..}, familyParameters = parameters, familySort = targetLevel} (name, annotation) = do
  K.checkType globals K.emptyContext annotation
  normal <- lift (N.normalise globals 0 annotation)
  let (binders, result) = termTelescope normal
      (inherited, fields) = splitAt inductiveParameters binders
  unless (length inherited == inductiveParameters) (K.failure "constructor is missing uniform parameters")
  parameterContext <- inherit K.emptyContext parameters inherited
  (fieldContext, classified) <- checkFields parameterContext fields
  resultIndices <- familyApplication globals peers family fieldContext result
  pure (Constructor name inductiveName normal classified resultIndices)
  where
    inherit context [] [] = pure context
    inherit context ((_, expected) : remaining) ((plicity, actual) : rest) = do
      unless (plicity == Implicit) (K.failure "constructor uniform parameters must be implicit")
      expectedValue <- K.evaluate globals context expected
      actualValue <- K.evaluate globals context actual
      K.convert globals context actualValue expectedValue
      inherit (K.bind context actualValue) remaining rest
    inherit _ _ _ = K.failure "constructor uniform parameters do not match family"
    checkFields context [] = pure (context, [])
    checkFields context ((plicity, domain) : rest) = do
      level <- K.checkType globals context domain
      K.oblige (LevelBelow level targetLevel)
      -- a recursive field endeth in one group family, directly or after
      -- function inputs that mention no group family: strictly positive.
      recursive <-
        if containsFamilies (Map.keys peers) domain
          then do
            let (inputs, result) = termTelescope domain
            when (any (containsFamilies (Map.keys peers) . snd) inputs) (K.failure "inductive occurrence must be strictly positive")
            inputContext <- foldM (\current (_, input) -> K.bind current <$> K.evaluate globals current input) context inputs
            peer <- case fst (termSpine result) of
              Global name _ | Just member <- Map.lookup name peers -> pure member
              _ -> K.failure "inductive occurrence must be a direct saturated family application"
            familyApplication globals peers peer inputContext result
            let Family {familyDeclaration = InductiveDeclaration {inductiveName = target}} = peer
            pure (Just target)
          else pure Nothing
      value <- K.evaluate globals context domain
      (ending, remaining) <- checkFields (K.bind context value) rest
      pure (ending, (plicity, domain, recursive) : remaining)

-- a family occurrence is a saturated application of the family, never inside
-- its own parameters or indices.
familyApplication :: Globals -> Map.Map SymbolId Family -> Family -> K.Context -> Term -> K.Typing [(Plicity, Term)]
familyApplication globals peers Family {familyDeclaration = InductiveDeclaration {..}, familyParameters = parameters, familyIndices = indices} context term = do
  let (headTerm, arguments) = termSpine term
      expectedPlicities = map fst (parameters ++ indices)
  levels <- case headTerm of
    Global name universeArguments | name == inductiveName -> pure universeArguments
    _ -> K.failure "inductive occurrence must be a direct saturated family application"
  unless (length levels == inductiveUniverses) (K.failure "wrong number of inductive universe arguments")
  traverse_ K.oblige (zipWith LevelEqual levels (map LParam [0 .. inductiveUniverses - 1]))
  unless (length arguments == length expectedPlicities && map fst arguments == expectedPlicities) (K.failure "inductive result requireth every parameter and index")
  when (any (containsFamilies (Map.keys peers) . snd) arguments) (K.failure "inductive family cannot occur inside its arguments")
  let (actualParameters, resultIndices) = splitAt inductiveParameters arguments
  forM_ (zip [0 ..] actualParameters) \(position, (_, argument)) -> do
    actual <- K.evaluate globals context argument
    expected <- K.evaluate globals context (Local (K.contextDepth context - position - 1))
    K.convert globals context actual expected
  pure resultIndices

-- generated signatures use stable binder levels while construction proceeds.
-- original constructor levels map to field levels; induction hypotheses add
-- extra binders without appearing in that map. quotation back to indices is
-- explicit below, so later dependent fields retain their original references.
generateRecursor :: [Family] -> [Constructor] -> Family -> Either String Term
generateRecursor families constructors target@Family {familyDeclaration = InductiveDeclaration {inductiveUniverses}, familyParameters = parameters, familyIndices = indices} = do
  motiveTypes <- zipWithM (\depth family -> motiveType family depth parameterLevels (familyIndices family)) [parameterCount ..] families
  let methodDepth = parameterCount + length families
  methods <- zipWithM methodType [methodDepth ..] constructors
  inner <- indexBinders (methodDepth + length constructors) parameterLevels indices
  pure (foldr (Pi Implicit . snd) (foldr (Pi Explicit) inner (motiveTypes ++ methods)) parameters)
  where
    parameterCount = length parameters
    levels = map LParam [0 .. inductiveUniverses - 1]
    motives = Map.fromList [(inductiveName (familyDeclaration family), (parameterCount + index, LParam (inductiveUniverses + index))) | (index, family) <- zip [0 ..] families]
    parameterLevels = [0 .. parameterCount - 1]
    motiveType family depth mapping [] = do
      self <- familyTerm family depth mapping
      (_, resultLevel) <- motiveOf (inductiveName (familyDeclaration family))
      pure (Pi Explicit self (Sort resultLevel))
    motiveType family depth mapping ((plicity, domain) : rest) = do
      moved <- renameTerm mapping depth domain
      Pi plicity moved <$> motiveType family (depth + 1) (mapping ++ [depth]) rest
    methodType depth Constructor {..} = fields depth parameterLevels constructorFields
      where
        fields current mapping [] = do
          (motiveLevel, _) <- motiveOf constructorFamily
          resultIndices <- traverse (moveArgument mapping current) constructorIndices
          let values = zipWith (\(plicity, _, _) level -> (plicity, localAt current level)) constructorFields (drop parameterCount mapping)
              inherited = [(Implicit, localAt current level) | level <- parameterLevels]
              self = applyArguments (Global constructorName levels) (inherited ++ values)
          pure (applyArguments (localAt current motiveLevel) (resultIndices ++ [(Explicit, self)]))
        fields current mapping ((plicity, domain, recursive) : remaining) = do
          moved <- renameTerm mapping current domain
          let extended = mapping ++ [current]
          remainder <- case recursive of
            Just family -> do
              -- the hypothesis for a function field `k` is `[inputs, motive (inputs k)]`.
              movedField <- renameTerm mapping (current + 1) domain
              let (inputs, result) = termTelescope movedField
                  inputCount = length inputs
                  familyArguments = snd (termSpine result)
                  applied = applyArguments (Local inputCount) [(plicity, Local (inputCount - position - 1)) | (position, (plicity, _)) <- zip [0 ..] inputs]
              (motiveLevel, _) <- motiveOf family
              let conclusion = applyArguments (localAt (current + 1 + inputCount) motiveLevel) (drop parameterCount familyArguments ++ [(Explicit, applied)])
                  hypothesis = foldr (uncurry Pi) conclusion inputs
              Pi Explicit hypothesis <$> fields (current + 2) extended remaining
            Nothing -> fields (current + 1) extended remaining
          pure (Pi plicity moved remainder)
    indexBinders depth mapping [] = do
      (motiveLevel, _) <- motiveOf (inductiveName (familyDeclaration target))
      self <- familyTerm target depth mapping
      let indexValues = zipWith (\(plicity, _) level -> (plicity, localAt (depth + 1) level)) indices (drop parameterCount mapping)
          result = applyArguments (localAt (depth + 1) motiveLevel) (indexValues ++ [(Explicit, Local 0)])
      pure (Pi Explicit self result)
    indexBinders depth mapping ((plicity, domain) : rest) = do
      moved <- renameTerm mapping depth domain
      Pi plicity moved <$> indexBinders (depth + 1) (mapping ++ [depth]) rest
    familyTerm family depth mapping =
      pure (applyArguments (Global (inductiveName (familyDeclaration family)) levels) (zipWith (\(plicity, _) level -> (plicity, localAt depth level)) (familyParameters family ++ familyIndices family) mapping))
    motiveOf family = maybe (Left "missing inductive family motive") Right (Map.lookup family motives)
    moveArgument mapping depth = traverse (renameTerm mapping depth)

-- a rule is scoped over the shared prefix and the actual constructor fields.
-- its recursive calls are ordinary checked core terms, reused by both evaluators.
generateRule :: [Family] -> [Constructor] -> Constructor -> Either String Term
generateRule [] _ _ = Left "missing inductive group"
generateRule families@(firstFamily : _) constructors Constructor {..} = do
  methodIndex <- maybe (Left "missing inductive method") pure (elemIndex constructorName (map constructorNameOf constructors))
  arguments <- fmap concat $ forM (zip [0 ..] constructorFields) \(position, (plicity, domain, recursive)) -> do
    let field = localAt depth (prefixCount + position)
        mapping = parameterLevels ++ [prefixCount .. prefixCount + position - 1]
    case recursive of
      Nothing -> pure [(plicity, field)]
      Just target -> do
        family <- maybe (Left "missing recursive target") pure (Map.lookup target peers)
        moved <- renameTerm mapping depth domain
        let (inputs, result) = termTelescope moved
            inputCount = length inputs
            current = depth + inputCount
            child = applyArguments (localAt current (prefixCount + position)) [(visibility, Local (inputCount - index - 1)) | (index, (visibility, _)) <- zip [0 ..] inputs]
            indices = drop parameterCount (snd (termSpine result))
            common = [(if level < parameterCount then Implicit else Explicit, localAt current level) | level <- [0 .. prefixCount - 1]]
            call = applyArguments (Global (inductiveEliminator (familyDeclaration family)) recursorLevels) (common ++ indices ++ [(Explicit, child)])
            hypothesis = foldr (uncurry Lambda) call inputs
        pure [(plicity, field), (Explicit, hypothesis)]
  pure (applyArguments (localAt depth (parameterCount + length families + methodIndex)) arguments)
  where
    first = familyDeclaration firstFamily
    parameterCount = inductiveParameters first
    prefixCount = parameterCount + length families + length constructors
    depth = prefixCount + length constructorFields
    parameterLevels = [0 .. parameterCount - 1]
    recursorLevels = map LParam [0 .. inductiveUniverses first + length families - 1]
    peers = Map.fromList [(inductiveName (familyDeclaration family), family) | family <- families]
    constructorNameOf Constructor {constructorName = name} = name

localAt :: Int -> Int -> Term
localAt depth level = Local (depth - level - 1)

renameTerm :: [Int] -> Int -> Term -> Either String Term
renameTerm mapping depth = traverseScoped renameLocal
  where
    renameLocal bound (Local index) _
      | index < 0 = Left "negative inductive local index"
      | index < bound = pure (Local index)
      | otherwise = case drop (length mapping - (index - bound) - 1) mapping of
          level : _ | index - bound < length mapping -> pure (Local (depth - level - 1 + bound))
          _ -> Left "inductive term outside its telescope"
    renameLocal _ Meta {} _ = Left "unresolved term inference hole in inductive declaration"
    renameLocal _ _ descend = descend

containsFamilies :: [SymbolId] -> Term -> Bool
containsFamilies names = \case
  Global name _ | name `elem` names -> True
  term -> any (containsFamilies names . snd) (children term)

selfUniverses :: SymbolId -> Term -> [[Level]]
selfUniverses name = \case
  Global identity levels | identity == name -> [levels]
  term -> concatMap (selfUniverses name . snd) (children term)

replaceFamilyUniverses :: [SymbolId] -> [Level] -> Term -> Term
replaceFamilyUniverses families levels = runIdentity . traverseScoped replace
  where
    replace _ (Global identity _) _ | identity `elem` families = pure (Global identity levels)
    replace _ _ descend = descend
