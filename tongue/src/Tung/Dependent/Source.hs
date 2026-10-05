-- | the dependent source boundary useþ one syntax and namespace for types and
-- values. only closed, kernel-checked definitions enter a source program.
module Tung.Dependent.Source
  ( SourceProgram,
    sourceEnvironment,
    sourceDefinitions,
    sourceGlobal,
    compileSource,
    compileProject,
    compileProjectWith,
    compileModules,
    compileImports,
    compileYieldWith,
    CompileFailure (..),
    FailureKind (..),
    compileProjectDetailed,
    compileImportsDetailed,
    compileYieldDetailed,
    typeOfName,
    sorryAssumptions,
    Hole (..),
    sourceHoles,
    sourceExports,
    sourceImportPaths,
    inferSourceExpression,
    normaliseSourceExpression,
    Expression,
    Parameter (..),
    Binder (..),
    Argument (..),
    Declaration (..),
    ConstructorDeclaration (..),
    Row (..),
    parseSource,
    parseProgram,
    sketch,
    parseExpression,
  )
where

import Control.Monad (foldM, forM, forM_, unless, when)
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity (..))
import Data.List (elemIndex, isPrefixOf, nub, nubBy, partition, sortOn)
import Data.Map.Strict qualified as Map
import Data.Maybe (catMaybes, fromMaybe, isJust, isNothing)
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Host qualified as H
import Tung.Dependent.Inductive qualified as I
import Tung.Dependent.Literal (literalType)
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Render (renderTermWith)
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Error (CompileFailure (..), FailureKind (..))
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Source.Instance (classFamily, implicitArgument, resolveInstance, sameInstance, settleAnnotation, solveDeterminedInstances, solveInstances)
import Tung.Dependent.Source.Module (sourceImportPaths)
import Tung.Dependent.Source.Module qualified as Modules
import Tung.Dependent.Source.Parse (parseExpression, parseProgram, parseSource)
import Tung.Dependent.Source.Pattern qualified as Patterns
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core
import Tung.Identity (ModuleId (..), SymbolId (..), inductionSymbol)
import Tung.Token (SourceFailure (..))

-- universe holes are fresh across the complete declaration, including its
-- annotation and every occurrence of a universe-polymorphic global.
type Elaboration = E.Elaboration

compileSource :: ModuleId -> String -> Either String SourceProgram
compileSource owner source = compileProject owner source Map.empty

-- imported sources are keyed by þeir `use` paths. each is checked once, in
-- dependency order; a cycle is an error.
compileProject :: ModuleId -> String -> Map.Map String String -> Either String SourceProgram
compileProject = compileProjectWith Map.empty

-- modules already compiled, keyed by `use` path, are reused unchanged.
compileProjectWith :: Map.Map String SourceProgram -> ModuleId -> String -> Map.Map String String -> Either String SourceProgram
compileProjectWith compiled owner source modules = Error.compileString (compileProjectDetailed compiled owner source modules)

compileProjectDetailed :: Map.Map String SourceProgram -> ModuleId -> String -> Map.Map String String -> Either CompileFailure SourceProgram
compileProjectDetailed compiled owner source modules = fst <$> compileYieldDetailed compiled owner source modules

-- like 'compileProjectWith', for a root þat may end in `yield`. þe yielded
-- expression is checked against þe finished module.
compileYieldWith :: Map.Map String SourceProgram -> ModuleId -> String -> Map.Map String String -> Either String (SourceProgram, Maybe K.Inferred)
compileYieldWith compiled owner source modules = Error.compileString (compileYieldDetailed compiled owner source modules)

compileYieldDetailed :: Map.Map String SourceProgram -> ModuleId -> String -> Map.Map String String -> Either CompileFailure (SourceProgram, Maybe K.Inferred)
compileYieldDetailed compiled owner source modules = do
  (program, yielded) <- Modules.compileProject insertDeclaration compiled owner source modules
  (program,) <$> traverse (Error.compilationFailure CheckFailure . inferIn program) yielded

-- compile þe named modules and everyþing þey use.
compileModules :: Map.Map String String -> [String] -> Either String (Map.Map String SourceProgram)
compileModules = compileImports Map.empty

compileImports :: Map.Map String SourceProgram -> Map.Map String String -> [String] -> Either String (Map.Map String SourceProgram)
compileImports compiled modules = Error.compileString . compileImportsDetailed compiled modules

compileImportsDetailed :: Map.Map String SourceProgram -> Map.Map String String -> [String] -> Either CompileFailure (Map.Map String SourceProgram)
compileImportsDetailed = Modules.compileImports insertDeclaration

-- a shown declaration exporteþ every name it introduceþ.
insertDeclaration :: ModuleId -> SourceProgram -> Declaration -> Either SourceFailure SourceProgram
insertDeclaration owner program = \case
  ImportDeclaration {} -> pure program
  declaration@FlockDeclaration {} -> insertClass owner program declaration
  declaration@BizenDeclaration {} -> insertInstance owner program declaration
  ShownDeclaration declaration -> exportIntroduced program <$> insertDeclaration owner program declaration
  ReExportDeclaration names -> reexportNames program names
  declaration@InductiveDeclaration {} -> insertInductive owner program declaration
  -- a law statement nameþ itself "law flock rule".
  Declaration {..} -> Error.inContext (maybe ("in let '" ++ declarationName ++ "': ") (\law -> "in law '" ++ law ++ "': ") (lawOf declarationName)) do
    let SourceProgram {..} = program
        identity = SymbolId owner declarationName
    unless (declarationName /= "_") (Error.failure "top-level definitions require a name")
    repeated localNames [declarationName]
    (result, (), holes) <- elaborateHoles True program ((\(term, ty) -> (term, ty, ())) <$> inferDefinition sourceEnvironment globalNames emptyScope declarationName declarationAnnotation declarationBody)
    environment <- Error.fromString (K.defineInferred sourceEnvironment identity result)
    pure (bindLocal declarationName (FreshName identity (K.inferredUniverses result)) program {sourceEnvironment = environment, checkedDefinitions = (identity, result) : checkedDefinitions, sourceHoles = reverse holes ++ sourceHoles})
  HostDeclaration {..} -> Error.inContext ("in let '" ++ hostName ++ "': ") do
    let SourceProgram {..} = program
        identity = SymbolId owner hostName
    unless (hostName /= "_") (Error.failure "top-level definitions require a name")
    repeated localNames [hostName]
    signature <- elaborate program do
      result@(_, kind) <- inferExpression sourceEnvironment globalNames emptyScope hostAnnotation
      requireUniverse sourceEnvironment emptyScope kind
      pure result
    environment <- Error.fromString (H.defineHost sourceEnvironment identity hostKey signature)
    let universes = maybe 0 definitionUniverses (Map.lookup identity (globals environment))
    pure (bindLocal hostName (FreshName identity universes) program {sourceEnvironment = environment})

recordFields :: K.Environment -> N.Value -> Elaboration [(String, N.Value)]
recordFields environment ty =
  E.force (globals environment) ty >>= \case
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

insertInductive :: ModuleId -> SourceProgram -> Declaration -> Either SourceFailure SourceProgram
insertInductive owner program@SourceProgram {..} InductiveDeclaration {..} = Error.inContext ("in ilk '" ++ inductiveName ++ "': ") do
  let family = SymbolId owner inductiveName
      eliminator = inductionSymbol family
      members = inductiveName : map constructorName inductiveConstructors
      uniform = uniformParameters inductiveName inductiveConstructors inductiveSignature
  unless (all (/= "_") members) (Error.failure "ilk and constructor declarations require names")
  repeated localNames members
  signature <- elaborate program do
    result@(_, kind) <- inferExpression sourceEnvironment globalNames emptyScope inductiveSignature
    requireUniverse sourceEnvironment emptyScope kind
    pure result
  Error.fromString (K.validate sourceEnvironment signature)
  normalSignature <- Error.fromString (N.normalise (globals sourceEnvironment) 0 (K.inferredTerm signature))
  let info = InductiveInfo (length uniform) (drop (length uniform) (productPlicities normalSignature)) []
      provisionalDefinition = Definition (K.inferredUniverses signature) (K.inferredConstraints signature) (K.inferredTerm signature) (TypeConstructor info)
      provisional = K.Environment (Map.insert family provisionalDefinition (globals sourceEnvironment))
  ((rawSignature, constructors), constraints) <- E.runElaboration (displayName globalNames) do
    levels <- mapM (const E.freshLevel) [1 .. K.inferredUniverses signature]
    rawSignature <- E.fromEither (instantiateLevels levels (K.inferredTerm signature))
    let names = insertName inductiveName (FixedName family levels) globalNames
    -- the staged family template is checked before entering this private
    -- scope. every self-reference shareþ one universe vector; final insertion
    -- generaliseþ and independently checkeþ the complete constructor group.
    inferCore provisional emptyScope (Global family levels)
    (scope, domains) <- bindUniform provisional emptyScope uniform rawSignature
    constructors <- mapM (elaborateConstructor provisional names scope domains) inductiveConstructors
    rawSignature <- E.zonk (globals provisional) rawSignature
    constructors <- mapM (\(name, ty) -> (name,) <$> E.zonk (globals provisional) ty) constructors
    pure (rawSignature, constructors)
  environment <- Error.fromString (I.inferInductive sourceEnvironment family eliminator (length uniform) rawSignature constructors constraints)
  let definitions = globals environment
      register current name = case Map.lookup (SymbolId owner name) definitions of
        Just definition -> pure (bindLocal name (FreshName (SymbolId owner name) (definitionUniverses definition)) current)
        Nothing -> Error.failure "inductive checker omitted a declared member"
  foldM register program {sourceEnvironment = environment} members
  where
    elaborateConstructor environment names scope domains ConstructorDeclaration {..} = do
      (annotation, kind) <- inferExpression environment names scope constructorAnnotation
      requireUniverse environment scope kind
      pure (SymbolId owner constructorName, foldr (Pi Implicit) annotation domains)
insertInductive _ _ _ = Error.failure "expected ilk declaration"

-- named header inputs are parameters while every constructor's written
-- result passeþ þem unchanged; þe rest are indices, as in a GADT.
uniformParameters :: String -> [ConstructorDeclaration] -> Expression -> [Parameter]
uniformParameters family constructors (Product parameters _) =
  [parameter | (_, parameter) <- takeWhile uniform (zip [0 ..] parameters)]
  where
    uniform (index, Parameter {parameterPlicity, parameterName = Just name}) =
      let position = length [() | Parameter {parameterPlicity = earlier} <- take index parameters, earlier == parameterPlicity]
       in all (passes parameterPlicity position name . result . constructorAnnotation) constructors
    uniform _ = False
    result = \case
      Product _ codomain -> result codomain
      other -> other
    -- each slot is compared wiþ þe written argument of its plicity.
    passes plicity position name = \case
      Application (Name head) arguments
        | head == family,
          written <- [argument | Argument actual argument <- arguments, actual == plicity],
          length written > position ->
            case written !! position of
              Name given -> given == name
              _ -> False
      -- an unrecognised result keepeþ þe header's reading.
      _ -> True
uniformParameters _ _ _ = []

productPlicities :: Term -> [Plicity]
productPlicities (Pi plicity _ body) = plicity : productPlicities body
productPlicities _ = []

bindUniform :: K.Environment -> Scope -> [Parameter] -> Term -> Elaboration (Scope, [Term])
bindUniform environment = go
  where
    go scope [] _ = pure (scope, [])
    go scope (Parameter {parameterName} : remaining) signature = do
      value <- eval environment scope signature >>= E.force (globals environment)
      case value of
        N.VPi _ domain codomain -> do
          domainTerm <- quote environment scope domain
          let current = extend scope parameterName domain
              argument = N.VNeutral (N.NLocal (depth scope))
          result <- E.instantiate (globals environment) codomain argument >>= quote environment current
          (scope, domains) <- go current remaining result
          pure (scope, domainTerm : domains)
        _ -> E.failure "uniform inductive parameters requireþ a product signature"

inferSourceExpression :: SourceProgram -> String -> Either String K.Inferred
inferSourceExpression program source = parseExpression source >>= Error.toString . inferIn program

inferIn :: SourceProgram -> Expression -> Either SourceFailure K.Inferred
inferIn program@SourceProgram {..} expression = do
  result <- elaborate program (inferExpression sourceEnvironment globalNames emptyScope expression)
  Error.fromString (K.validate sourceEnvironment result)
  pure result

normaliseSourceExpression :: SourceProgram -> String -> Either String Term
normaliseSourceExpression program@SourceProgram {..} source = do
  result <- inferSourceExpression program source
  -- source inference recheckeþ the generalised term before raw NBE can see it.
  N.normalise (globals sourceEnvironment) 0 (K.inferredTerm result)

-- the caller checkeþ this result at the insertion or expression boundary.
elaborate :: SourceProgram -> Elaboration (Term, N.Value) -> Either SourceFailure K.Inferred
elaborate = elaborateWith False

-- a top-level let is generalised: each type hole still open becomeþ a leading
-- implicit input, and each bizen requirement still waiting on þem an implicit
-- instance input after þem, as hindley-milner generalisation doþ.
elaborateWith :: Bool -> SourceProgram -> Elaboration (Term, N.Value) -> Either SourceFailure K.Inferred
elaborateWith generalising program action =
  fst <$> elaborateResult generalising program do
    (term, ty) <- action
    pure (term, ty, ())

-- metadata, such as law obligations, travel beside þe elaborated result; they
-- do not alter metavariable solving or universe generalisation.
elaborateResult :: Bool -> SourceProgram -> Elaboration (Term, N.Value, a) -> Either SourceFailure (K.Inferred, a)
elaborateResult generalising program action = (\(result, metadata, _) -> (result, metadata)) <$> elaborateHoles generalising program action

-- like 'elaborateResult', wiþ þe goal of each `sorry`, rendered once þe
-- declaration's instances are chosen.
elaborateHoles :: Bool -> SourceProgram -> Elaboration (Term, N.Value, a) -> Either SourceFailure (K.Inferred, a, [Hole])
elaborateHoles generalising SourceProgram {..} action = do
  ((term, annotation, metadata, holes), constraints) <- E.runElaboration (displayName globalNames) do
    (term, ty, metadata) <- action
    solveInstances sourceEnvironment globalNames
    -- a `sorry` under two located wrappers is recorded twice.
    holes <- nubBy (\left right -> holeSpan left == holeSpan right) <$> (E.takeHoles >>= traverse (renderHole (globals sourceEnvironment) (briefName globalNames)))
    remaining <- E.takeInstanceGoals
    let base = globals sourceEnvironment
    (extended, placeholders) <-
      if generalising
        then generaliseHoles base remaining
        else do
          unless (null remaining) (E.failure "a bizen requirement hath a type þat is still unknown; add an annotation")
          pure (base, [])
    annotation <- E.quote extended 0 ty
    term <- E.zonk extended term
    annotation <- E.zonk extended annotation
    (term, annotation) <- abstractPlaceholders placeholders term annotation
    pure (term, annotation, metadata, holes)
  result <- Error.fromString (K.generalise term annotation constraints)
  pure (result, metadata, holes)

-- a hole's goal and its named locals, outermost first. generated locals,
-- whose names start wiþ `#`, are omitted.
-- þe text is built lazily from a snapshot of þe hole solutions, so a goal
-- þat is never printed, such as one in an imported module, costeþ noþing.
renderHole :: Globals -> (SymbolId -> String) -> E.HoleSite -> Elaboration Hole
renderHole base display E.HoleSite {..} = do
  resolve <- E.resolver
  let depthNow = length holeNames
      -- a pattern variable is a named alias of an unnamed field local.
      aliases = Map.fromList [(field, name) | (Just name, N.VNeutral (N.NLocal field)) <- zip holeNames (K.contextValues holeContext)]
      names = [fromMaybe (Map.findWithDefault "_" (depthNow - position - 1) aliases) name | (position, name) <- zip [0 ..] holeNames]
      shown depth bound value = either (const "?") (renderTermWith display bound) (N.quoteDisplayWith resolve base depth value)
      goal = shown depthNow names holeGoal
      context = [(name, shown (depthNow - position - 1) (drop (position + 1) names) (K.contextTypes holeContext !! position)) | (position, name) <- zip [0 ..] holeNames]
  pure (Hole holeSpan goal [(name, ty) | (Just name, ty) <- reverse context, take 1 name /= "#"])

-- each open hole is assigned a placeholder constant, a type or an instance,
-- known only while þis declaration is finished.
generaliseHoles :: Globals -> [E.InstanceGoal] -> Elaboration (Globals, [(SymbolId, Term)])
generaliseHoles base goals = do
  let decompose = E.approximateFlexible base >>= \progressed -> when progressed decompose
  decompose
  holes <- E.unsolved base
  evidence <- forM goals \E.InstanceGoal {goalHole} ->
    E.force base goalHole <&> \case
      N.VNeutral neutral | (N.NMeta identity _, _) <- N.neutralSpine neutral -> identity
      _ -> -1
  -- a hole for a type or a closed type function, such as `[*, *]`.
  let sorted = \case
        Sort _ -> True
        Pi _ _ codomain -> sorted codomain
        _ -> False
      types = [(identity, ty) | (identity, ty) <- holes, sorted ty, null (freeIndices ty), identity `notElem` evidence]
      typeSymbol identity = SymbolId PrimitiveModule ("#type" ++ show identity)
      withTypes = foldr (\(identity, ty) -> Map.insert (typeSymbol identity) (placeholder ty)) base types
  forM_ types \(identity, ty) -> E.assignConstant withTypes identity (Global (typeSymbol identity) (holeLevels ty))
  -- requirements wiþ one type share one instance input.
  requirements <- forM goals \E.InstanceGoal {..} -> do
    ty <- E.quote withTypes (length (K.contextTypes goalContext)) goalType
    unless (null (freeIndices ty)) (E.failure "a bizen requirement dependeþ on a local; add an annotation")
    pure (goalHole, ty)
  let distinct = nub (map snd requirements)
      evidenceSymbol index = SymbolId PrimitiveModule ("#evidence" ++ show index)
      instances = [(evidenceSymbol index, ty) | (index, ty) <- zip [0 :: Int ..] distinct]
      extended = foldr (\(symbol, ty) -> Map.insert symbol (placeholder ty)) withTypes instances
  forM_ requirements \(hole, ty) ->
    E.force extended hole >>= \case
      N.VNeutral neutral
        | (N.NMeta identity _, _) <- N.neutralSpine neutral,
          Just index <- elemIndex ty distinct ->
            E.assignConstant extended identity (Global (evidenceSymbol index) (holeLevels ty))
      _ -> pure ()
  pure (extended, [(typeSymbol identity, ty) | (identity, ty) <- types] ++ instances)
  where
    -- a definition's type cannot hold universe holes, so a placeholder is
    -- polymorphic over þose its type mentioneþ.
    holeLevels ty = nub [LMeta index | level <- termLevels ty, index <- levelHoles level]
    levelHoles = \case
      LMeta index -> [index]
      LSucc level -> levelHoles level
      LMax left right -> levelHoles left ++ levelHoles right
      _ -> []
    placeholder ty =
      let holes = [index | LMeta index <- holeLevels ty]
          parameter = \case
            LMeta index | Just position <- elemIndex index holes -> LParam position
            LSucc level -> LSucc (parameter level)
            LMax left right -> LMax (parameter left) (parameter right)
            level -> level
       in Definition (length holes) [] (mapLevels parameter ty) (Host "#generalised")

-- placeholders become leading implicit inputs: types in order of first use in
-- þe type, þen instances. an unused type hole is still an error.
abstractPlaceholders :: [(SymbolId, Term)] -> Term -> Term -> Elaboration (Term, Term)
abstractPlaceholders [] term annotation = pure (term, annotation)
abstractPlaceholders placeholders term annotation = do
  let instances = [placeholder | placeholder@(SymbolId _ name, _) <- placeholders, "#evidence" `isPrefixOf` name]
      used = nub (concatMap mentioned (annotation : map snd instances))
      types = [placeholder | symbol <- used, Just ty <- [lookup symbol placeholders], let placeholder = (symbol, ty), placeholder `notElem` instances]
      binders = types ++ instances
  when (any (\(symbol, _) -> symbol `notElem` map fst binders) placeholders) (E.failure "unsolved implicit argument or lambda domain")
  let total = length binders
      positions = Map.fromList (zip (map fst binders) [0 ..])
      -- under `outer` binders of þe prefix, þen `bound` more.
      replace outer = go 0
        where
          go bound = \case
            Global symbol _ | Just position <- Map.lookup symbol positions -> Local (bound + outer - 1 - position)
            other -> runIdentity (mapChildren (\binders' -> Identity . go (bound + binders')) other)
      domains = [replace position ty | (position, (_, ty)) <- zip [0 ..] binders]
  pure
    ( foldr (Core.Lambda Implicit) (replace total term) domains,
      foldr (Pi Implicit) (replace total annotation) domains
    )
  where
    mentioned = \case
      Global symbol@(SymbolId PrimitiveModule name) _ | "#" `isPrefixOf` name -> [symbol]
      other -> concat [mentioned child | (_, child) <- children other]

-- the pattern compiler reuseþ these operations for row bodies and scrutinees.
patternChecker :: K.Environment -> Names -> Patterns.ExpressionChecker
patternChecker environment names =
  Patterns.ExpressionChecker (inferExpression environment names) (\scope annotation -> snd <$> inferAnnotation environment names scope annotation) (checkExpression environment names) (\scope -> applyTo environment names scope Nothing) (solveDeterminedInstances environment names)

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
  requireUniverse environment scope kind
  (term,) <$> eval environment scope term

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
            Just (FreshName identity universes) -> Global identity <$> mapM (const E.freshLevel) [1 .. universes]
            Just (FixedName identity levels) -> pure (Global identity levels)
            Just (AmbiguousName modules) -> E.failure (ambiguousName name modules)
            Nothing -> E.failure ("unknown name '" ++ name ++ "'")
    (term,) <$> inferCore environment scope term
  Induce name -> do
    family <- case lookupName name names of
      Just (AmbiguousName modules) -> E.failure (ambiguousName name modules)
      Just binding | Just family <- bindingSymbol binding -> pure family
      _ -> E.failure ("unknown name '" ++ name ++ "'")
    term <- case Map.lookup (inductionSymbol family) (globals environment) of
      Just Definition {definitionUniverses, definitionBody = Eliminator _} ->
        Global (inductionSymbol family) <$> mapM (const E.freshLevel) [1 .. definitionUniverses]
      _ -> E.failure ("'" ++ name ++ "' is not an ilk or flock, so it cannot be induced")
    (term,) <$> inferCore environment scope term
  Universe -> do
    level <- E.freshLevel
    pure (Sort level, N.VSort (LSucc level))
  Product parameters result -> productTerm scope parameters
    where
      productTerm current [] = inferType environment names current result
      productTerm current (Parameter {..} : remaining) = do
        (domain, domainType) <- inferType environment names current parameterType
        domainLevel <- requireUniverse environment current domainType
        domainValue <- eval environment current domain
        (codomain, codomainType) <- productTerm (extend current parameterName domainValue) remaining
        codomainLevel <- requireUniverse environment (extend current parameterName domainValue) codomainType
        pure (Pi parameterPlicity domain codomain, N.VSort (K.universeNormalise (LMax domainLevel codomainLevel)))
  Lambda binders _
    | any (Patterns.constructorBinder environment names) binders ->
        E.failure "a function matching constructors needs a type annotation"
  Lambda [] body -> inferExpression environment names scope body
  Lambda (Binder {..} : remaining) body -> do
    (domain, domainValue) <- case binderAnnotation of
      Nothing -> do
        level <- E.freshLevel
        E.newMeta (globals environment) context (N.VSort level)
      Just domainExpression -> do
        (domain, kind) <- inferExpression environment names scope domainExpression
        requireUniverse environment scope kind
        (domain,) <$> eval environment scope domain
    let current = extend scope binderName domainValue
    (bodyTerm, bodyType) <- inferExpression environment names current (Lambda remaining body)
    codomain <- quote environment current bodyType
    pure (Core.Lambda binderPlicity domain bodyTerm, N.VPi binderPlicity domainValue (N.Closure (K.contextValues context) codomain))
  Application (Name name) arguments
    | Nothing <- elemIndex (Just name) locals,
      Just recursion <- recursiveBinding name scope ->
        Patterns.recursiveCall (patternChecker environment names) environment scope recursion arguments
  Application function arguments -> inferApplication environment names scope Nothing function arguments
  Ascription expression annotation -> do
    (_, expected) <- inferAnnotation environment names scope annotation
    term <- checkExpression environment names scope expression expected
    pure (term, expected)
  Block declarations result -> localDefinitions environment names scope declarations (\current -> inferExpression environment names current result)
  LiteralExpression value -> do
    let term = Core.Literal (literalType value) value
    (term,) <$> inferCore environment scope term
  -- `sorry` is þe primitive assumption at a type inferred from its use.
  Sorry -> do
    level <- E.freshLevel
    (ty, tyValue) <- E.newMeta (globals environment) context (N.VSort level)
    pure (Apply Implicit (Global H.sorrySymbol [level]) ty, tyValue)
  RecordTypeExpression fields -> do
    sorted <- canonicalFields fields
    elaborated <- forM sorted \(name, field) -> do
      (term, kind) <- inferExpression environment names scope field
      level <- requireUniverse environment scope kind
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
    fields <- recordFields environment ty
    case lookup name fields of
      Just fieldType -> pure (Project term name, fieldType)
      Nothing -> E.failure ("record hath no field '" ++ name ++ "'")
  RecordUpdate base changes -> do
    (baseTerm, baseType) <- inferExpression environment names scope base
    fields <- recordFields environment baseType
    let removed = [name | RemoveField name <- changes]
        set = [(name, value) | SetField name value <- changes]
        changed = removed ++ map fst set
    unless (length changed == Set.size (Set.fromList changed)) (E.failure "a record update changeþ each field at most once")
    case [name | name <- removed, name `notElem` map fst fields] of
      name : _ -> E.failure ("record hath no field '" ++ name ++ "' to remove")
      [] -> pure ()
    -- the base is bound once; kept fields project from þat local.
    annotation <- quote environment scope baseType
    baseValue <- eval environment scope baseTerm
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
    (term, _) <- E.newMeta (globals environment) (scopeContext scope) (N.VSort level)
    pure (term, N.VSort level)
  Cases _ -> E.failure "a case function needs a type annotation"
  -- wiþout an expected type, every row shareþ one inferred result type.
  Match scrutinees rows -> do
    level <- E.freshLevel
    matched <- fmap catMaybes . forM scrutinees $ \case
      Name name | Just index <- elemIndex (Just name) locals -> pure (Just (length locals - index - 1))
      _ -> pure Nothing
    (_, resultType) <- E.newMetaWithout (globals environment) (scopeContext scope) matched (N.VSort level)
    term <- Patterns.checkMatch (patternChecker environment names) environment names scope scrutinees rows resultType
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
-- spine consumeþ separate queues in declaration order, including values.
-- given þe expected type of þe application, a function whose result applieþ
-- its own type family meeteþ þat type before þe inputs þat mention þe
-- family are checked; see 'motiveInputs'.
applyTo :: K.Environment -> Names -> Scope -> Maybe N.Value -> Term -> N.Value -> [Argument] -> [Argument] -> Elaboration (Term, N.Value)
applyTo environment names scope@Scope {scopeContext = context} goal function functionType explicitArguments implicitArguments = do
  motive <- case goal of
    Just _ -> motiveInputs environment names scope functionType (length explicitArguments)
    Nothing -> pure Nothing
  (term, ty, deferred) <- go motive False 0 function functionType explicitArguments implicitArguments []
  let (late, early) = partition (\(_, _, _, afterGoal) -> afterGoal) (reverse deferred)
  -- a postponed case function is checked once later arguments have fixed
  -- its input type, þen filleþ þe hole þat stood for it.
  forM_ early checkDeferred
  unless (null late) do
    forM_ goal (E.unify (globals environment) context ty)
    forM_ late checkDeferred
  pure (term, ty)
  where
    checkDeferred (expression, domain, hole, _) = do
      checked <- checkExpression environment names scope expression domain
      value <- eval environment scope checked
      E.unify (globals environment) context hole value
    -- after the written arguments, a pending requirement is still searched.
    go _ _ _ term ty [] [] deferred =
      E.force (globals environment) ty >>= \case
        N.VPi Implicit domain codomain ->
          classFamily environment names domain >>= \case
            Just _ -> do
              (argumentTerm, argumentValue) <- implicitArgument environment names (scopeContext scope) domain
              resultType <- E.instantiate (globals environment) codomain argumentValue
              go Nothing False 0 (Apply Implicit term argumentTerm) resultType [] [] deferred
            Nothing -> pure (term, ty, deferred)
        _ -> pure (term, ty, deferred)
    go motive open position term ty explicit implicit deferred =
      E.force (globals environment) ty >>= \case
        N.VPi plicity domain codomain -> do
          -- a written `@x` filleþ þe next implicit input þat instance search
          -- doþ not fill.
          requirement <- if plicity == Implicit then maybe False (const True) <$> classFamily environment names domain else pure False
          let afterGoal = plicity == Explicit && open && maybe False ((position `elem`) . snd) motive
          (argumentTerm, argumentValue, nextExplicit, nextImplicit, nextDeferred, omitted) <- case (plicity, explicit, implicit) of
            (Explicit, arg : rest, _) -> supplied domain arg afterGoal rest implicit deferred
            (Implicit, _, arg : rest) | not requirement -> supplied domain arg False explicit rest deferred
            (Implicit, _, _) -> do
              (argumentTerm, argumentValue) <- implicitArgument environment names (scopeContext scope) domain
              pure (argumentTerm, argumentValue, explicit, implicit, deferred, True)
            _ -> E.failure "explicit argument required before a later implicit argument"
          resultType <- E.instantiate (globals environment) codomain argumentValue
          -- only an omitted family is found from þe goal.
          let opened = open || omitted && maybe False ((== position) . fst) motive
          go motive opened (position + 1) (Apply plicity term argumentTerm) resultType nextExplicit nextImplicit nextDeferred
        neutral@(N.VNeutral (N.NMeta _ _))
          | null implicit -> do
              (domain, codomain) <- E.ensurePi (globals environment) context Explicit neutral
              go Nothing False position term (N.VPi Explicit domain codomain) explicit implicit deferred
          | otherwise -> E.failure "implicit parameter order requireþ a function annotation"
        _ -> E.failure "application requireþ a function"
    supplied domain argument afterGoal explicit implicit deferred = do
      let expression = argumentExpression argument
      waiting <- if afterGoal then pure True else unknownCaseInput expression domain
      if waiting
        then do
          (term, value) <- E.newMeta (globals environment) context domain
          pure (term, value, explicit, implicit, (expression, domain, value, afterGoal) : deferred, False)
        else do
          term <- checkExpression environment names scope expression domain
          value <- eval environment scope term
          pure (term, value, explicit, implicit, deferred, False)
    -- a case function cannot split an input whose type is still a hole.
    unknownCaseInput expression domain = case expression of
      Cases _ ->
        E.force (globals environment) domain >>= \case
          N.VPi _ input _ ->
            E.force (globals environment) input <&> \case
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
motiveInputs :: K.Environment -> Names -> Scope -> N.Value -> Int -> Elaboration (Maybe (Int, [Int]))
motiveInputs environment names scope functionType explicitCount = walk 0 explicitCount functionType [] Set.empty []
  where
    base = depth scope
    walk position remaining ty families carriers inputs =
      E.force (globals environment) ty >>= \case
        N.VPi plicity domain codomain -> do
          requirement <- if plicity == Implicit then isJust <$> classFamily environment names domain else pure False
          if remaining == 0 && (plicity == Explicit || not requirement)
            then pure Nothing
            else do
              mentioned <- if null families then pure Set.empty else mentions position domain
              family <- if plicity == Implicit && not requirement then isFamily position domain else pure False
              next <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal (base + position)))
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
      term <- E.quoteFolded (globals environment) (base + position) domain
      pure (Set.fromList [level - base | index <- freeIndices term, let level = base + position - 1 - index, level >= base])
    isFamily position domain =
      E.force (globals environment) domain >>= \case
        N.VPi {} -> endsInSort (base + position) domain
        _ -> pure False
    endsInSort level ty =
      E.force (globals environment) ty >>= \case
        N.VPi _ _ codomain -> E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal level)) >>= endsInSort (level + 1)
        N.VSort _ -> pure True
        _ -> pure False

checkExpression :: K.Environment -> Names -> Scope -> Expression -> N.Value -> Elaboration Term
checkExpression environment names scope (Located span inner) expected = E.located span do
  case inner of
    Sorry -> E.recordHole (E.HoleSite (Just span) (scopeContext scope) (scopeNames scope) expected)
    _ -> pure ()
  checkExpression environment names scope inner expected
checkExpression environment names scope expression expected = E.force (globals environment) expected >>= check
  where
    check expected = case expression of
      -- `sorry` standeþ for a settled expected type itself, wiþout an
      -- inference hole.
      Sorry -> do
        ty <- quote environment scope expected
        if holes ty
          then inferred expected
          else do
            kind <- inferCore environment scope ty
            level <- requireUniverse environment scope kind
            pure (Apply Implicit (Global H.sorrySymbol [level]) ty)
      -- leading implicit binders keep þeir names; only þe explicit binders
      -- after þem form þe pattern row.
      Lambda binders body
        | (implicits@(_ : _), explicits) <- span ((== Implicit) . binderPlicity) binders,
          any (Patterns.constructorBinder environment names) explicits ->
            checkExpression environment names scope (Lambda implicits (Lambda explicits body)) expected
        | any (Patterns.constructorBinder environment names) binders ->
            Patterns.checkCases (patternChecker environment names) environment names scope [Row [maybe Wildcard Name (binderName binder) | binder <- binders] body] expected
      Lambda (Binder {..} : remaining) body -> case expected of
        N.VPi Implicit domain codomain | binderPlicity == Explicit -> introduceImplicit domain codomain
        N.VPi plicity domain codomain -> do
          unless (plicity == binderPlicity) (E.failure "implicit and explicit lambda arguments do not match")
          domainTerm <- quote environment scope domain
          case binderAnnotation of
            Nothing -> pure ()
            Just annotation -> do
              (_, actual) <- inferAnnotation environment names scope annotation
              E.unify (globals environment) (scopeContext scope) actual domain
          let current = extend scope binderName domain
              argument = N.VNeutral (N.NLocal (depth scope))
          resultType <- E.instantiate (globals environment) codomain argument
          bodyTerm <- checkExpression environment names current (Lambda remaining body) resultType
          pure (Core.Lambda plicity domainTerm bodyTerm)
        _ -> inferred expected
      Lambda [] body -> checkExpression environment names scope body expected
      -- a written type wiþ holes learnþ from þe expected type before þe body
      -- is checked. a polymorphic annotation is specialised instead.
      Ascription body annotation -> checkAscription environment names scope body annotation expected (checkExpression environment names)
      Block declarations body -> fst <$> localDefinitions environment names scope declarations (\current -> (,expected) <$> checkExpression environment names current body expected)
      Cases rows -> Patterns.checkCases (patternChecker environment names) environment names scope rows expected
      RecordExpression fields
        | N.VRecordType expectedFields <- expected -> do
            sorted <- canonicalFields fields
            unless (map fst sorted == map fst expectedFields) (E.failure "record fields differ from the expected record type")
            Core.Record <$> forM (zip sorted expectedFields) \((name, field), (_, fieldType)) -> (name,) <$> checkExpression environment names scope field fieldType
      -- an unknown expected type would depend on þe matched values; þe
      -- match inferreþ a result type wiþout þem instead.
      Match {} | flexible expected -> inferred expected
      Match scrutinees rows -> Patterns.checkMatch (patternChecker environment names) environment names scope scrutinees rows expected
      -- an expected implicit input is introduced before any oþer expression is
      -- checked, so a polymorphic value meeteþ a polymorphic type.
      _
        | N.VPi Implicit domain codomain <- expected -> introduceImplicit domain codomain
      _ -> inferred expected
    -- an omitted implicit binder shifteþ the context but introduceþ no name.
    introduceImplicit domain codomain = do
      domainTerm <- quote environment scope domain
      let current = extend scope Nothing domain
      resultType <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal (depth scope)))
      Core.Lambda Implicit domainTerm <$> checkExpression environment names current expression resultType
    flexible = \case
      N.VNeutral neutral | (N.NMeta _ _, _) <- N.neutralSpine neutral -> True
      _ -> False
    inferred expected = do
      (term, actual) <- case expression of
        Application function arguments
          | not (recursiveApplication scope function) -> inferApplication environment names scope (Just expected) function arguments
        _ -> inferExpression environment names scope expression
      specialise environment names scope term actual expected

-- ordinary and recursive bodies share ascription checking. omitted implicit
-- binders enter þe scope before an annotation is read; written holes learn
-- from þe expected type. recursion must not discard a written annotation.
checkAscription :: K.Environment -> Names -> Scope -> Expression -> Expression -> N.Value -> (Scope -> Expression -> N.Value -> Elaboration Term) -> Elaboration Term
checkAscription environment names scope body annotation expected checkBody =
  E.force (globals environment) expected >>= \case
    N.VPi Implicit domain codomain | not (writtenImplicit annotation) -> do
      domainTerm <- quote environment scope domain
      let current = extend scope Nothing domain
      resultType <- E.instantiate (globals environment) codomain (N.VNeutral (N.NLocal (depth scope)))
      Core.Lambda Implicit domainTerm <$> checkAscription environment names current body annotation resultType checkBody
    expected -> do
      (_, annotationValue) <- inferAnnotation environment names scope annotation
      E.force (globals environment) annotationValue >>= \case
        written@(N.VPi Implicit _ _) -> do
          term <- checkBody scope body written
          specialise environment names scope term written expected
        written -> do
          E.unify (globals environment) (scopeContext scope) written expected
          checkBody scope body expected
  where
    writtenImplicit = \case
      Product (Parameter {parameterPlicity = Implicit} : _) _ -> True
      Located _ inner -> writtenImplicit inner
      _ -> False

specialise :: K.Environment -> Names -> Scope -> Term -> N.Value -> N.Value -> Elaboration Term
specialise environment names scope = go
  where
    go term actual expected =
      E.force (globals environment) actual >>= \case
        N.VPi Implicit domain codomain
          | shouldSpecialise expected -> do
              (argumentTerm, argumentValue) <- implicitArgument environment names (scopeContext scope) domain
              resultType <- E.instantiate (globals environment) codomain argumentValue
              go (Apply Implicit term argumentTerm) resultType expected
        actual -> E.unify (globals environment) (scopeContext scope) actual expected >> pure term
    -- an unknown expected type receiveþ an instance, as in hindley-milner.
    shouldSpecialise (N.VPi Implicit _ _) = False
    shouldSpecialise _ = True

localDefinitions :: K.Environment -> Names -> Scope -> [Declaration] -> (Scope -> Elaboration (Term, N.Value)) -> Elaboration (Term, N.Value)
localDefinitions _ _ scope [] body = body scope
localDefinitions _ _ _ (InductiveDeclaration {} : _) _ = E.failure "ilk declarations must be top-level"
localDefinitions _ _ _ (HostDeclaration {} : _) _ = E.failure "fremmed bindings must be top-level"
localDefinitions _ _ _ (ImportDeclaration {} : _) _ = E.failure "use and show must be top-level"
localDefinitions _ _ _ (ShownDeclaration {} : _) _ = E.failure "use and show must be top-level"
localDefinitions _ _ _ (ReExportDeclaration {} : _) _ = E.failure "use and show must be top-level"
localDefinitions _ _ _ (FlockDeclaration {} : _) _ = E.failure "flock and bizen must be top-level"
localDefinitions _ _ _ (BizenDeclaration {} : _) _ = E.failure "flock and bizen must be top-level"
localDefinitions environment names scope (Declaration {..} : remaining) body = do
  (value, ty) <- inferDefinition environment names scope declarationName declarationAnnotation declarationBody
  annotation <- quote environment scope ty
  actual <- eval environment scope value
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
  _ -> Patterns.elaborateRecursive (patternChecker environment names) environment names scope name expected body

-- recursion and sibling lookup use free names, respecting source binders.
referencedNames :: K.Environment -> Names -> Expression -> Set.Set String
referencedNames environment names = freeNames (isJust . Patterns.constructorNamed environment names) Set.empty

-- flocks and bizens -------------------------------------------------------

-- `flock name:[parameters, @:parent, *] { members }` becomeþ a
-- one-constructor family, one accessor per member, and one instance per parent.
insertClass :: ModuleId -> SourceProgram -> Declaration -> Either SourceFailure SourceProgram
insertClass owner program FlockDeclaration {..} = Error.inContext ("in flock '" ++ flockName ++ "': ") do
  let parameters = [parameter | parameter@Parameter {parameterName = Just _} <- flockParameters]
      parents = [parameterType | Parameter {parameterName = Nothing, parameterType} <- flockParameters]
  unless (all ((== Explicit) . parameterPlicity) parameters) (Error.failure "flock parameters are written name:type, wiþout '@'")
  unless (and [plicity == Implicit | Parameter plicity Nothing _ <- flockParameters]) (Error.failure "a parent requirement is written @:parent")
  repeated (localNames program) (flockName : [name | FlockMember name _ <- flockMembers] ++ [name | FlockLaw name _ _ _ <- flockMembers])
  let members = [(name, ty) | FlockMember name ty <- flockMembers]
      laws = [(name, binders, left, right) | FlockLaw name binders left right <- flockMembers]
      constructor = flockName ++ "_make"
      family = Application (Name flockName) [Argument parameterPlicity (Name name) | Parameter {parameterPlicity, parameterName = Just name} <- parameters]
      parentName index = "#parent_" ++ show index
      fieldName name = "#field_" ++ name
      dictionaryName = "#dictionary"
      -- generated local binders cannot capture source parameter names.
      parentFields = [Parameter Implicit (Just (parentName index)) parent | (index, parent) <- zip [1 :: Int ..] parents]
      memberFields = [Parameter Explicit (Just name) ty | (name, ty) <- members]
      -- a law `[binders, left = right]` stateþ þe primitive identity type
      -- over þe members. each bizen proveþ it for its own members.
      lawTypes = [(name, lawType binders left right) | (name, binders, left, right) <- laws]
      lawType binders left right =
        let equation = Application (Name (symbolName H.identitySymbol)) [Argument Explicit left, Argument Explicit right]
         in if null binders then equation else Product binders equation
      fieldNames = map fst members
      declaration =
        InductiveDeclaration
          flockName
          (Product parameters Universe)
          [ConstructorDeclaration constructor (Product (parentFields ++ memberFields) family)]
      implicitParameters = [parameter {parameterPlicity = Implicit} | parameter <- parameters]
      dictionary = Parameter Implicit (Just dictionaryName) family
      -- each accessor selecteþ one field through the eliminator.
      select resultType field =
        Application
          (Induce flockName)
          ( [Argument Implicit (Name name) | Parameter {parameterName = Just name} <- parameters]
              ++ [ Argument Explicit (Lambda [Binder Explicit Nothing (Just family)] resultType),
                   Argument Explicit (Lambda ([Binder Implicit (Just (parentName index)) Nothing | index <- [1 .. length parents]] ++ [Binder Explicit (Just (fieldName name)) Nothing | name <- fieldNames]) (Name field)),
                   Argument Explicit (Name dictionaryName)
                 ]
          )
      -- named implicit slots bind as lambdas, as a written header would.
      binders = Lambda ([Binder Implicit (Just name) Nothing | Parameter {parameterName = Just name} <- parameters] ++ [Binder Implicit (Just dictionaryName) Nothing])
      accessor (name, ty) = Declaration name (Just (Product (implicitParameters ++ [dictionary]) ty)) (binders (select ty (fieldName name)))
      parentInstance (index, parent) = Declaration (flockName ++ "_parent_" ++ show index) (Just (Product (implicitParameters ++ [dictionary]) parent)) (binders (select parent (parentName index)))
  defined <- insertInductive owner program declaration
  familySymbol <- symbolOf flockName defined
  constructorSymbol <- symbolOf constructor defined
  parentFamilies <- traverse (`classOf` program) parents
  let statementName law = "law " ++ flockName ++ " " ++ law
      registered = defined {globalNames = registerClass familySymbol (ClassInfo constructorSymbol (map fst members) [(law, SymbolId owner (statementName law)) | (law, _) <- lawTypes] parentFamilies [] []) (globalNames defined)}
  withAccessors <- foldM (insertDeclaration owner) registered (map accessor members)
  withParents <-
    foldM
      ( \current (index, parent) -> do
          inserted <- insertDeclaration owner current (parentInstance (index, parent))
          instanceSymbol <- symbolOf (flockName ++ "_parent_" ++ show index) inserted
          parentFamily <- classOf parent inserted
          pure (registerInstance True parentFamily instanceSymbol inserted)
      )
      withAccessors
      (zip [1 :: Int ..] parents)
  -- a law's statement is a type over a dictionary of þe flock. its members
  -- refer to þat dictionary, which instance search findeþ as a local.
  let statement (law, ty) = Declaration (statementName law) (Just (Product (implicitParameters ++ [dictionary]) Universe)) (binders ty)
  foldM (insertDeclaration owner) withParents (map statement lawTypes)
  where
    classOf parent current = case parent of
      Application (Name name) _ | Just (FreshName symbol _) <- lookupName name (globalNames current), Map.member symbol (nameClasses (globalNames current)) -> pure symbol
      Name name | Just (FreshName symbol _) <- lookupName name (globalNames current), Map.member symbol (nameClasses (globalNames current)) -> pure symbol
      _ -> Error.failure "a parent requirement must apply a flock"
insertClass _ _ _ = Error.failure "expected flock declaration"

-- þe law a statement's hidden name standeþ for.
lawOf :: String -> Maybe String
lawOf name = case words name of
  ["law", _, law] -> Just law
  _ -> Nothing

-- `bizen:[@parameters, @:requirements, arguments flock] { members }`. the
-- dictionary is the flock constructor applied to the members; parent fields
-- are solved by instance search inside the bizen's own scope.
insertInstance :: ModuleId -> SourceProgram -> Declaration -> Either SourceFailure SourceProgram
insertInstance owner program@SourceProgram {..} BizenDeclaration {..} = Error.inContext ("in bizen of '" ++ writtenClass bizenType ++ "': ") do
  let identity = fresh (0 :: Int)
      written = case bizenType of
        Product items _ -> [parameterName item | item <- items]
        _ -> []
  definitions <- traverse member bizenMembers
  (result, laws, memberHoles) <- elaborateHoles False program do
    (annotation, kind) <- inferExpression sourceEnvironment globalNames emptyScope bizenType
    requireUniverse sourceEnvironment emptyScope kind
    expected <- eval sourceEnvironment emptyScope annotation
    (term, laws) <- bizenBody emptyScope expected written definitions
    pure (term, expected, laws)
  family <- resultClass (K.inferredType result)
  environment <- Error.fromString (K.defineInferred sourceEnvironment identity result)
  -- two bizens wiþ one pattern would make selection incoherent.
  let existing = maybe [] classInstances (Map.lookup family classes)
  when (any (sameInstance environment identity) existing) (Error.failure "a bizen wiþ þe same type already exists")
  let registered = registerInstance False family identity program {sourceEnvironment = environment, checkedDefinitions = (identity, result) : checkedDefinitions}
  -- an assumed law is elaborated too, so its `sorry` showeþ þe statement.
  lawHoles <- concat <$> mapM (\goal@(_, name, _) -> maybe (pure []) (proveLaw registered identity goal) (lookup name definitions)) laws
  let rendered = renderTermWith (displayName globalNames) [] (K.inferredType result)
      assumed = ["law '" ++ name ++ "' of bizen " ++ rendered | (_, name, _) <- laws, Just body <- [lookup name definitions], isSorry body]
  pure registered {assumedLaws = reverse assumed ++ assumedLaws, sourceHoles = reverse (memberHoles ++ lawHoles) ++ sourceHoles}
  where
    -- a law proof is checked against þe law's statement for þis bizen's own
    -- dictionary, supplied explicitly under þe bizen's binders.
    -- bare `sorry` needeþ no check; an ascription still constrainþ its type.
    -- a goal records its exact statement and parent projection path. a law
    -- name alone cannot identify it across classes or imported modules.
    proveLaw current@SourceProgram {sourceEnvironment = proving, globalNames = visible} identity (path, name, statementSymbol) body = Error.inContext ("in law '" ++ name ++ "': ") do
      (proof, (), holes) <- elaborateHoles False current do
        (dictionary, ty) <- global emptyScope identity
        (term, annotation) <- bind emptyScope written dictionary ty
        expected <- eval proving emptyScope annotation
        pure (term, expected, ())
      Error.fromString (K.validate proving proof)
      pure holes
      where
        written = case bizenType of
          Product items _ -> map parameterName items
          _ -> []
        global scope symbol = do
          count <- maybe (E.failure "missing generated declaration") (pure . definitionUniverses) (Map.lookup symbol (globals proving))
          levels <- mapM (const E.freshLevel) [1 .. count]
          let term = Global symbol levels
          (term,) <$> inferCore proving scope term
        apply scope (term, ty) argument =
          E.force (globals proving) ty >>= \case
            N.VPi Implicit domain codomain -> do
              actual <- inferCore proving scope argument
              E.unify (globals proving) (scopeContext scope) actual domain
              value <- eval proving scope argument
              (Apply Implicit term argument,) <$> E.instantiate (globals proving) codomain value
            _ -> E.failure "invalid generated dictionary accessor"
        family ty =
          E.force (globals proving) ty >>= \case
            N.VNeutral neutral | (N.NGlobal symbol _, arguments) <- N.neutralSpine neutral -> pure (symbol, map snd arguments)
            _ -> E.failure "a law needs a flock dictionary"
        applied scope symbol dictionary ty = do
          (_, parameters) <- family ty
          start <- global scope symbol
          arguments <- traverse (quote proving scope) parameters
          foldM (apply scope) start (arguments ++ [dictionary])
        parent scope (dictionary, ty) index = do
          (SymbolId owner name, _) <- family ty
          applied scope (SymbolId owner (name ++ "_parent_" ++ show (index + 1))) dictionary ty
        bind scope names dictionary ty =
          E.force (globals proving) ty >>= \case
            N.VPi Implicit domain codomain -> do
              annotation <- quote proving scope domain
              let (name, rest) = case names of
                    first : others -> (first, others)
                    [] -> (Nothing, [])
                  current = extend scope name domain
              next <- E.instantiate (globals proving) codomain (N.VNeutral (N.NLocal (depth scope)))
              (term, resultType) <- bind current rest (Apply Implicit (shiftTerm 1 dictionary) (Local 0)) next
              pure (Core.Lambda Implicit annotation term, Pi Implicit annotation resultType)
            target -> do
              (dictionary, target) <- foldM (parent scope) (dictionary, target) path
              (statement, kind) <- applied scope statementSymbol dictionary target
              requireUniverse proving scope kind
              expected <- eval proving scope statement
              term <- checkExpression proving visible scope body expected
              pure (term, statement)
    isSorry = \case
      Sorry -> True
      Located _ inner -> isSorry inner
      _ -> False
    -- private spellings cannot collide wiþ present or later source names;
    -- every generated identity must also be absent from the whole environment.
    fresh index =
      let symbol = SymbolId owner ("#instance_" ++ show index)
       in if Map.member symbol (globals sourceEnvironment) then fresh (index + 1) else symbol
    member = \case
      Declaration {..} -> pure (declarationName, maybe declarationBody (Ascription declarationBody) declarationAnnotation)
      _ -> Error.failure "a bizen containeþ only let definitions"
    classes = nameClasses globalNames
    resultClass = \case
      Pi _ _ codomain -> resultClass codomain
      term
        | (Global family _, _) <- termSpine term,
          Map.member family classes ->
            pure family
      _ -> Error.failure "a bizen type must end in a flock application"
    bizenBody scope expected written definitions =
      E.force (globals sourceEnvironment) expected >>= \case
        N.VPi Implicit domain codomain -> do
          domainTerm <- quote sourceEnvironment scope domain
          let (name, rest) = case written of
                first : others -> (first, others)
                [] -> (Nothing, [])
          next <- E.instantiate (globals sourceEnvironment) codomain (N.VNeutral (N.NLocal (depth scope)))
          (term, laws) <- bizenBody (extend scope name domain) next rest definitions
          pure (Core.Lambda Implicit domainTerm term, laws)
        N.VPi Explicit _ _ -> E.failure "a bizen type takeþ only implicit parameters"
        target -> dictionary scope target definitions
    -- a bizen may also define þe members and laws of a parent flock þat
    -- haþ no bizen of its own. þat parent's dictionary is built inline, and
    -- inherited instance search projecteþ it from þis one.
    dictionary scope target definitions = do
      (term, used, laws) <- build scope target
      case [name | (name, _) <- definitions, name `notElem` used] of
        name : _ -> E.failure ("'" ++ name ++ "' is not a member of this flock or a parent it witnesseþ")
        [] -> pure (term, laws)
      where
        given = map fst definitions
        build scope target = do
          (classInfo, familyArguments) <-
            classApplication target >>= \case
              Just found -> pure found
              Nothing -> E.failure "a bizen type must end in a flock application"
          let wanted = classMembers classInfo
              laws = map fst (classLaws classInfo)
          case [name | name <- wanted, name `notElem` given] of
            name : _ -> E.failure ("bizen is missing member '" ++ name ++ "'")
            [] -> pure ()
          case [name | name <- laws, name `notElem` given] of
            name : _ -> E.failure ("bizen is missing law '" ++ name ++ "'")
            [] -> pure ()
          let constructor = classConstructor classInfo
          universes <- maybe (E.failure "missing flock constructor") (pure . definitionUniverses) (Map.lookup constructor (globals sourceEnvironment))
          levels <- mapM (const E.freshLevel) [1 .. universes]
          constructorType <- inferCore sourceEnvironment scope (Global constructor levels)
          -- the head's arguments fix the flock parameters before fields are checked.
          (headTerm, headType) <- foldM (fixParameter scope) (Global constructor levels, constructorType) familyArguments
          (term, ty, used, parentLaws) <- fields scope (0 :: Int) headTerm headType wanted [] []
          E.unify (globals sourceEnvironment) (scopeContext scope) ty target
          pure (term, wanted ++ laws ++ used, [([], name, statement) | (name, statement) <- classLaws classInfo] ++ parentLaws)
        -- parent fields precede member fields.
        fields scope index term ty pending used siblings =
          E.force (globals sourceEnvironment) ty >>= \case
            N.VPi Implicit domain codomain -> do
              defines <-
                classApplication domain <&> \case
                  Just (parent, _) -> any (`elem` given) (classMembers parent ++ map fst (classLaws parent))
                  Nothing -> False
              -- a parent wiþ a bizen of its own keepeþ it.
              owned <-
                if defines
                  then maybe False (const True) <$> E.attempt (resolveInstance sourceEnvironment globalNames (scopeContext scope) domain)
                  else pure False
              (argument, value, parentUsed, parentLaws) <-
                if defines && not owned
                  then do
                    (argument, parentUsed, parentLaws) <- build scope domain
                    value <- eval sourceEnvironment scope argument
                    pure (argument, value, parentUsed, [(index : path, name, statement) | (path, name, statement) <- parentLaws])
                  else do
                    (argument, value) <- implicitArgument sourceEnvironment globalNames (scopeContext scope) domain
                    pure (argument, value, [], [])
              next <- E.instantiate (globals sourceEnvironment) codomain value
              (term, ty, used, laws) <- fields scope (index + 1) (Apply Implicit term argument) next pending (used ++ parentUsed) siblings
              pure (term, ty, used, parentLaws ++ laws)
            N.VPi Explicit domain codomain
              | name : rest <- pending,
                Just body <- lookup name definitions -> do
                  argument <- member scope siblings name body domain
                  value <- eval sourceEnvironment scope argument
                  next <- E.instantiate (globals sourceEnvironment) codomain value
                  fields scope index (Apply Explicit term argument) next rest used (siblings ++ [(name, value, domain)])
            N.VPi Explicit _ _ -> E.failure "invalid flock constructor"
            other -> pure (term, other, used, [])
        -- a member þat nameþ itself may use þe flock at anoþer type. when
        -- þat faileþ, its own name is a structural recursive call.
        -- a member þat nameþ an earlier member of þis bizen at þe bizen's
        -- own type cannot find þe bizen yet; it seeþ þat member's definition.
        member scope siblings name body domain
          | any ((`Set.member` usedNames) . fst3) siblings && name `Set.notMember` usedNames =
              trial >>= \case
                Just (term, commit) -> commit >> pure term
                Nothing -> do
                  let bound = foldl (\current (sibling, value, ty) -> define current (Just sibling) value ty) scope siblings
                  inner <- checkExpression sourceEnvironment globalNames bound body domain
                  wrap scope siblings inner
          | name `Set.member` usedNames =
              trial >>= \case
                Just (term, commit) -> commit >> pure term
                Nothing -> checkRecursiveExpression sourceEnvironment globalNames scope name body domain
          | otherwise = checkExpression sourceEnvironment globalNames scope body domain
          where
            usedNames = referencedNames sourceEnvironment globalNames body
            trial = E.speculate (checkExpression sourceEnvironment globalNames scope body domain <* solveInstances sourceEnvironment globalNames <* solved)
        fst3 (first, _, _) = first
        -- each sibling becomeþ a let around þe member.
        wrap _ [] inner = pure inner
        wrap current ((sibling, value, ty) : rest) inner = do
          annotation <- quote sourceEnvironment current ty
          valueTerm <- quote sourceEnvironment current value
          Let annotation valueTerm <$> wrap (define current (Just sibling) value ty) rest inner
        solved = E.takeInstanceGoals >>= \goals -> unless (null goals) (E.failure "unsolved requirement")
        classApplication value =
          E.force (globals sourceEnvironment) value <&> \case
            N.VNeutral neutral | (N.NGlobal family _, arguments) <- N.neutralSpine neutral, Just classInfo <- Map.lookup family classes -> Just (classInfo, arguments)
            _ -> Nothing
    fixParameter scope (term, ty) (_, value) =
      E.force (globals sourceEnvironment) ty >>= \case
        N.VPi Implicit _ codomain -> do
          argument <- quote sourceEnvironment scope value
          (Apply Implicit term argument,) <$> E.instantiate (globals sourceEnvironment) codomain value
        _ -> E.failure "invalid flock constructor"
    writtenClass = \case
      Product _ result -> writtenClass result
      Application (Name name) _ -> name
      Name name -> name
      _ -> "?"
insertInstance _ _ _ = Error.failure "expected bizen declaration"
