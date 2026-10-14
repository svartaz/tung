-- | top-level declarations: lets, host bindings, ilks, flocks, and bizens.
module Tung.Dependent.Source.Declaration
  ( insertDeclarations,
    recoverDeclarations,
  )
where

import Control.Monad (foldM, unless, when)
import Control.Monad.Trans.Except (ExceptT (..), except, mapExceptT, runExceptT)
import Control.Monad.Trans.Writer.Strict (Writer, runWriter, writer)
import Data.Functor.Identity (Identity (..))
import Data.List (intercalate)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Data.Traversable (for)
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Host qualified as H
import Tung.Dependent.Inductive qualified as I
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Elaborate qualified as Elaborate
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Source.Expression
import Tung.Dependent.Source.Instance (implicitArgument, resolveInstance, sameInstance, settleAnnotation, solveInstances)
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core
import Tung.Identity (ModuleId (..), SymbolId (..), inductionSymbol, modelSymbol)
import Tung.Token (SourceFailure (..), SourceSpan)

-- universe holes are fresh across the complete declaration, including its
-- annotation and every occurrence of a universe-polymorphic global.
type Elaboration = E.Elaboration

-- a dependency component is inserted atomically. shown flags belong to each
-- declaration, even though every family in a mutual component is checked together.
insertDeclarations :: ModuleId -> SourceProgram -> [(Maybe SourceSpan, Declaration)] -> Either SourceFailure SourceProgram
insertDeclarations owner program declarations = fst (recoverDeclarations owner program declarations)

-- goals are diagnostics, not partial definitions. a failed declaration group
-- leaveth its caller's environment untouched while retaining its checked goals.
-- a checked group keepeth the names its declarations resolved.
recoverDeclarations :: ModuleId -> SourceProgram -> [(Maybe SourceSpan, Declaration)] -> (Either SourceFailure SourceProgram, Report)
recoverDeclarations owner program declarations =
  let (result, report) = runWriter (runExceptT (checkDeclarations owner program declarations))
   in ((\checked -> checked {programNames = reportNames report ++ programNames checked}) <$> result, report)

type Checking = ExceptT SourceFailure (Writer Report)

fromSource :: Either SourceFailure a -> Checking a
fromSource = except

fromString :: Either String a -> Checking a
fromString = fromSource . Error.fromString

failure :: String -> Checking a
failure = fromSource . Error.failure

inContext :: String -> Checking a -> Checking a
inContext prefix = mapExceptT (fmap (Error.inContext prefix))

atSpan :: SourceSpan -> Checking a -> Checking a
atSpan span = mapExceptT (fmap (Error.atSpan span))

elaborateHoles :: SourceProgram -> Elaboration (Term, N.Value, a) -> Checking (K.Inferred, a, [Hole], Set.Set SymbolId)
elaborateHoles program = ExceptT . writer . Elaborate.elaborateHolesReport program

elaborateDependencies :: SourceProgram -> Elaboration (Term, N.Value) -> Checking (K.Inferred, Set.Set SymbolId)
elaborateDependencies program action = (\(result, (), _, references) -> (result, references)) <$> elaborateHoles program ((\(term, ty) -> (term, ty, ())) <$> action)

runWithHoles :: SourceProgram -> Globals -> Elaboration a -> Checking (a, [Constraint])
runWithHoles program base = ExceptT . writer . Elaborate.runWithHoles program base

checkDeclarations :: ModuleId -> SourceProgram -> [(Maybe SourceSpan, Declaration)] -> Checking SourceProgram
checkDeclarations _ program [] = pure program
checkDeclarations owner program [(span, declaration)] = maybe id atSpan span (checkDeclaration owner program declaration)
checkDeclarations owner program declarations@((span, _) : _) = maybe id atSpan span do
  let shownNames = Set.fromList [name | (_, ShownDeclaration declaration) <- declarations, InductiveDeclaration {..} <- [unshown declaration], name <- inductiveName : map constructorName inductiveConstructors]
      plain = [(span, unshown declaration) | (span, declaration) <- declarations]
  defined <- insertInductives owner program plain
  withFields <- foldM (insertFields owner) defined (map snd plain)
  pure (exportNames shownNames withFields)

-- a shown declaration exporteth every name it introduceth.
checkDeclaration :: ModuleId -> SourceProgram -> Declaration -> Checking SourceProgram
checkDeclaration owner program = \case
  ImportDeclaration {} -> pure program
  declaration@FlockDeclaration {} -> insertClass owner program declaration
  declaration@BizenDeclaration {} -> insertInstance owner program declaration
  ShownDeclaration declaration -> exportIntroduced program <$> checkDeclaration owner program declaration
  ReExportDeclaration names -> fromSource (reexportNames program names)
  declaration@InductiveDeclaration {} -> insertInductive owner program declaration >>= \defined -> insertFields owner defined declaration
  declaration@AssumptionDeclaration {} -> insertAssumption owner program declaration
  declaration@Declaration {declarationFixpoint = True} -> insertFixpoint owner program declaration
  Declaration {..} -> constant "let" owner program declarationName \identity -> do
    let SourceProgram {..} = program
    (result, (), holes, references) <- elaborateHoles program ((\(term, ty) -> (term, ty, ())) <$> inferDefinition programEnvironment globalNames emptyScope declarationName declarationAnnotation declarationBody)
    environment <- fromString (K.defineInferred programEnvironment identity result)
    pure (introduce declarationName identity environment references (recorded identity result holes program))
  HostDeclaration {..} -> constant "let" owner program hostName \identity -> do
    let SourceProgram {..} = program
    (signature, references) <- elaborateSignature program hostAnnotation
    -- the model is a hidden definition; a call of the binding's own name in
    -- it is structural recursion. it is checked against the binding's checked
    -- type, whose universe parameters stay rigid, so both share them even
    -- when the annotation nameth several universe-polymorphic families.
    let modelIdentity = modelSymbol identity
    modelled <- for hostModel \body -> do
      (result, modelReferences) <- elaborateDependencies program do
        expected <- E.evaluate K.emptyContext (K.inferredTerm signature)
        term <- checkDefinition programEnvironment globalNames emptyScope hostName body expected
        pure (term, expected)
      modelEnvironment <- fromString (lowerSurplus (K.inferredUniverses signature) result >>= K.defineInferred programEnvironment modelIdentity)
      pure (modelEnvironment, modelReferences)
    environment <- fromString (H.defineHost (maybe programEnvironment fst modelled) identity hostKey (modelIdentity <$ hostModel) signature)
    pure (introduce hostName identity environment references program {programReferences = maybe id (Map.insert modelIdentity . snd) modelled programReferences})

-- a top-level constant is checked in its own context. its name is written
-- and not yet declared.
constant :: String -> ModuleId -> SourceProgram -> String -> (SymbolId -> Checking a) -> Checking a
constant keyword owner SourceProgram {localNames} name check = inContext ("in " ++ keyword ++ " '" ++ name ++ "': ") do
  unless (name /= "_") (failure ("a top-level " ++ keyword ++ " requireth a name"))
  fromSource (repeated localNames [name])
  check (SymbolId owner name)

-- a checked constant joineth the environment and the name table, with the
-- references its source useth.
introduce :: String -> SymbolId -> K.Environment -> Set.Set SymbolId -> SourceProgram -> SourceProgram
introduce name identity environment references program@SourceProgram {programReferences} =
  bindLocal name (FreshName identity universes) program {programEnvironment = environment, programReferences = Map.insert identity references programReferences}
  where
    universes = maybe 0 definitionUniverses (Map.lookup identity (globals environment))

-- a checked source body keepeth its judgement and goals for later audits.
recorded :: SymbolId -> K.Inferred -> [Hole] -> SourceProgram -> SourceProgram
recorded identity result holes program@SourceProgram {checkedDefinitions, programHoles} =
  program {checkedDefinitions = (identity, result) : checkedDefinitions, programHoles = reverse holes ++ programHoles}

-- instance search in a model may leave universe parameters that its type
-- doth not mention; they are set to zero so the model shareth the binding's
-- parameters. the kernel rechecketh the result.
lowerSurplus :: Int -> K.Inferred -> Either String K.Inferred
lowerSurplus kept inferred@K.Inferred {..}
  | inferredUniverses <= kept = Right inferred
  | otherwise = do
      let levels = map LParam [0 .. kept - 1] ++ replicate (inferredUniverses - kept) LZero
          constraint = \case
            LevelEqual left right -> LevelEqual <$> instantiateLevel levels left <*> instantiateLevel levels right
            LevelBelow left right -> LevelBelow <$> instantiateLevel levels left <*> instantiateLevel levels right
      K.Inferred kept <$> traverse constraint inferredConstraints <*> instantiateLevels levels inferredTerm <*> instantiateLevels levels inferredType

-- a top-level annotation is an ilk, checked with the references it useth.
elaborateSignature :: SourceProgram -> Expression -> Checking (K.Inferred, Set.Set SymbolId)
elaborateSignature program@SourceProgram {programEnvironment, globalNames} annotation = elaborateDependencies program do
  result@(_, kind) <- inferExpression programEnvironment globalNames emptyScope annotation
  requireUniverse emptyScope kind
  pure result

-- a fast body nameth its declaration as a global with the signature's rigid
-- universe parameters, as a host model nameth its binding, so it may call
-- itself anywhere. the kernel storeth it as an opaque fixpoint.
insertFixpoint :: ModuleId -> SourceProgram -> Declaration -> Checking SourceProgram
insertFixpoint owner program@SourceProgram {..} Declaration {..} = constant "fast" owner program declarationName \identity -> do
  annotation <- maybe (failure "a fast declaration requireth an ilk annotation") pure declarationAnnotation
  (K.Inferred {inferredUniverses, inferredConstraints, inferredTerm}, signatureReferences) <- elaborateSignature program annotation
  let own = Definition inferredUniverses inferredConstraints inferredTerm Assumption
      environment = K.Environment (Map.insert identity own (globals programEnvironment))
      names = insertName declarationName (FixedName identity (map LParam [0 .. inferredUniverses - 1])) globalNames
  (result, (), holes, references) <- elaborateHoles program {programEnvironment = environment, globalNames = names} do
    expected <- E.evaluate K.emptyContext inferredTerm
    term <- checkExpression environment names emptyScope declarationBody expected
    pure (term, expected, ())
  unless (Set.member identity references) (failure "a fast declaration nameth itself; one that doth not is a let")
  -- instance search may add universe parameters after the signature's; each
  -- self-call passeth them on unchanged, so the recursion stayeth uniform.
  let surplus = map LParam [inferredUniverses .. K.inferredUniverses result - 1]
      extend _ (Global symbol levels) _ | symbol == identity = pure (Global symbol (levels ++ surplus))
      extend _ _ descend = descend
      checked = result {K.inferredTerm = runIdentity (traverseScoped extend (K.inferredTerm result))}
  defined <- fromString (H.defineFixpoint programEnvironment identity checked)
  pure (introduce declarationName identity defined (Set.delete identity (references <> signatureReferences)) (recorded identity checked holes program))
insertFixpoint _ _ _ = failure "expected fast declaration"

-- an assumption checketh only its type; the kernel stores it without a body.
insertAssumption :: ModuleId -> SourceProgram -> Declaration -> Checking SourceProgram
insertAssumption owner program@SourceProgram {programEnvironment} AssumptionDeclaration {..} = constant "orsetting" owner program assumptionName \identity -> do
  (signature, references) <- elaborateSignature program assumptionAnnotation
  environment <- fromString (K.assume programEnvironment identity signature)
  pure (introduce assumptionName identity environment references program)
insertAssumption _ _ _ = failure "expected orsetting declaration"

insertInductive :: ModuleId -> SourceProgram -> Declaration -> Checking SourceProgram
insertInductive owner program declaration = insertInductives owner program [(Nothing, declaration)]

insertInductives :: ModuleId -> SourceProgram -> [(Maybe SourceSpan, Declaration)] -> Checking SourceProgram
insertInductives owner program@SourceProgram {..} declarations = inContext context do
  group <- for declarations \(span, declaration) -> case declaration of
    InductiveDeclaration {..} -> pure (span, inductiveName, inductiveSignature, inductiveConstructors)
    _ -> failure "a mutual group requireth only ilk declarations"
  let members = concat [name : map constructorName constructors | (_, name, _, constructors) <- group]
      families = [SymbolId owner name | (_, name, _, _) <- group]
  unless (all (/= "_") members) (failure "ilk and constructor declarations require names")
  fromSource (repeated localNames members)
  signaturesWithReferences <- for group \(span, name, annotation, constructors) -> maybe id atSpan span do
    let family = SymbolId owner name
        uniform = uniformParameters name constructors annotation
    (signature, references) <- elaborateSignature program annotation
    fromString (K.validate programEnvironment signature)
    normal <- fromString (N.normalise (globals programEnvironment) 0 (K.inferredTerm signature))
    let info = InductiveInfo families (length uniform) (length uniform) (drop (length uniform) (productPlicities normal)) [] []
        definition = Definition (K.inferredUniverses signature) (K.inferredConstraints signature) (K.inferredTerm signature) (TypeConstructor info)
    pure ((span, name, constructors, family, uniform, signature, definition), references)
  let headerReferences = Set.unions (map snd signaturesWithReferences)
      signatures = map fst signaturesWithReferences
  let provisional = K.Environment (Map.union (Map.fromList [(family, definition) | (_, _, _, family, _, _, definition) <- signatures]) (globals programEnvironment))
  ((raw, references), constraints) <- runWithHoles program (globals provisional) do
    staged <- for signatures \(span, name, constructors, family, uniform, signature, _) -> do
      levels <- E.freshLevels (K.inferredUniverses signature)
      rawSignature <- E.fromEither (instantiateLevels levels (K.inferredTerm signature))
      pure (span, name, constructors, family, uniform, levels, rawSignature)
    let names = foldl (\names (_, name, _, family, _, levels, _) -> insertName name (FixedName family levels) names) globalNames staged
    -- all headers are checked before staging. each peer reference shareth its
    -- private universe vector; final insertion jointly generaliseth the group.
    raw <- for staged \(span, _, constructors, family, uniform, levels, rawSignature) -> maybe id E.located span do
      inferCore emptyScope (Global family levels)
      (scope, domains) <- bindUniform emptyScope uniform rawSignature
      checked <- mapM (elaborateConstructor provisional names scope domains) constructors
      pure (family, length uniform, rawSignature, checked)
    -- a constructor annotation may use a flock, as a law useth a parent's
    -- members; its dictionaries are found among the constructor's own fields.
    solveInstances provisional names
    remaining <- E.takeInstanceGoals
    unless (null remaining) (E.failure "a bizen requirement hath an ilk that is still unknown; add an annotation")
    checked <- for raw \(family, parameters, signature, constructors) ->
      (family,parameters,,) <$> E.zonk signature <*> mapM (\(name, ty) -> (name,) <$> E.zonk ty) constructors
    references <- E.takeReferences
    pure (checked, Set.union headerReferences references)
  environment <- fromString (I.inferInductives programEnvironment [I.InductiveDeclaration family (inductionSymbol family) parameters 0 constraints signature constructors | (family, parameters, signature, constructors) <- raw])
  let definitions = globals environment
      register current name = case Map.lookup (SymbolId owner name) definitions of
        Just definition -> pure (bindLocal name (FreshName (SymbolId owner name) (definitionUniverses definition)) current)
        Nothing -> failure "inductive checker omitted a declared member"
      provenance = Map.union (Map.map (const references) (Map.difference definitions (globals programEnvironment))) programReferences
  foldM register program {programEnvironment = environment, programReferences = provenance} members
  where
    context = case [inductiveName | (_, InductiveDeclaration {inductiveName}) <- declarations] of
      [name] -> "in ilk '" ++ name ++ "': "
      names -> "in mutual ilks '" ++ intercalate "', '" names ++ "': "
    elaborateConstructor environment names scope domains ConstructorDeclaration {..} = do
      (annotation, kind) <- inferExpression environment names scope constructorAnnotation
      requireUniverse scope kind
      pure (SymbolId owner constructorName, foldr (Pi Implicit) annotation domains)

-- named explicit fields of an unindexed one-constructor ilk use the same
-- checked projections as flock members. all constructor fields, including
-- implicit ones, retain their positions in dependent field types.
insertFields :: ModuleId -> SourceProgram -> Declaration -> Checking SourceProgram
insertFields owner program InductiveDeclaration {inductiveName, inductiveConstructors = [ConstructorDeclaration {constructorAnnotation}]}
  | let family = SymbolId owner inductiveName,
    Just Definition {definitionType, definitionBody = TypeConstructor InductiveInfo {inductiveIndexPlicities = [], inductiveConstructorInfo = [(constructor, _)]}} <- Map.lookup family (globals (programEnvironment program)) = do
      checked <- maybe (failure "missing ilk constructor") pure (Map.lookup constructor (globals (programEnvironment program)))
      let accessors = projections Explicit (map fst (fst (termTelescope definitionType))) family checked
          -- nested brackets extend the same telescope; a later field name
          -- shadoweth an earlier one, just as in its constructor's type.
          named = Map.fromList [(field, accessor) | (Parameter Explicit (Just field) _, accessor) <- zip (fields constructorAnnotation) accessors, field /= "_"]
      foldM defineAccessor program [(SymbolId owner (inductiveName ++ "." ++ field), accessor) | (field, accessor) <- Map.toList named]
  where
    fields (Product parameters result) = parameters ++ fields result
    fields _ = []
insertFields _ program _ = pure program

-- generated accessors still cross the kernel boundary. their checked types
-- name their family, retaining its proof dependencies through the usual graph.
defineAccessor :: SourceProgram -> (SymbolId, K.Inferred) -> Checking SourceProgram
defineAccessor program (identity, inferred) = do
  environment <- fromString (K.defineInferred (programEnvironment program) identity inferred)
  pure program {programEnvironment = environment, checkedDefinitions = (identity, inferred) : checkedDefinitions program}

-- named header inputs are parameters while every constructor's written
-- result passeth them unchanged; the rest are indices, as in a GADT.
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
    -- each slot is compared with the written argument of its plicity.
    passes plicity position name = \case
      Application (Name head) arguments
        | head == family,
          written <- [argument | Argument actual argument <- arguments, actual == plicity],
          length written > position ->
            case written !! position of
              Name given -> given == name
              _ -> False
      -- an unrecognised result keepeth the header's reading.
      _ -> True
uniformParameters _ _ _ = []

productPlicities :: Term -> [Plicity]
productPlicities (Pi plicity _ body) = plicity : productPlicities body
productPlicities _ = []

bindUniform :: Scope -> [Parameter] -> Term -> Elaboration (Scope, [Term])
bindUniform = go
  where
    go scope [] _ = pure (scope, [])
    go scope (Parameter {parameterName} : remaining) signature = do
      value <- eval scope signature >>= E.force
      case value of
        N.VPi _ domain codomain -> do
          domainTerm <- quote scope domain
          let current = extend scope parameterName domain
              argument = N.VNeutral (N.NLocal (depth scope))
          result <- E.instantiate codomain argument >>= quote current
          (scope, domains) <- go current remaining result
          pure (scope, domainTerm : domains)
        _ -> E.failure "uniform inductive parameters requireth a product signature"

-- `flock name:[parameters, @:parent, *] { members }` becometh a
-- one-constructor family, one accessor per member, and one instance per parent.
insertClass :: ModuleId -> SourceProgram -> Declaration -> Checking SourceProgram
insertClass owner program FlockDeclaration {..} = inContext ("in flock '" ++ flockName ++ "': ") do
  -- `β: * out` marketh a parameter that instance search findeth.
  let (parameters, outputs) = unzip [(parameter {parameterType = inner}, output) | parameter@Parameter {parameterName = Just _, parameterType} <- flockParameters, let (inner, output) = outputType parameterType]
      outputType = \case
        Application (Name "out") [Argument Explicit inner] -> (inner, True)
        ty -> (ty, False)
      parents = [parameterType | Parameter {parameterName = Nothing, parameterType} <- flockParameters]
  unless (all ((== Explicit) . parameterPlicity) parameters) (failure "flock parameters are written name:ilk, without '@'")
  unless (and [plicity == Implicit | Parameter plicity Nothing _ <- flockParameters]) (failure "a parent requirement is written @:parent")
  fromSource (repeated (localNames program) (flockName : [name | FlockMember name _ <- flockMembers]))
  -- member types may name earlier fields, including laws.
  let members = [(name, ty) | FlockMember name ty <- flockMembers]
      constructor = flockName ++ "_make"
      family = Application (Name flockName) [Argument parameterPlicity (Name name) | Parameter {parameterPlicity, parameterName = Just name} <- parameters]
      parentName index = "#parent_" ++ show index
      -- generated local binders cannot capture source parameter names.
      parentFields = [Parameter Implicit (Just (parentName index)) parent | (index, parent) <- zip [1 :: Int ..] parents]
      memberFields = [Parameter Explicit (Just name) ty | (name, ty) <- members]
      declaration =
        InductiveDeclaration
          flockName
          (Product parameters Universe)
          [ConstructorDeclaration constructor (Product (parentFields ++ memberFields) family)]
  defined <- insertInductive owner program declaration
  familySymbol <- fromSource (symbolOf flockName defined)
  constructorSymbol <- fromSource (symbolOf constructor defined)
  parentFamilies <- traverse (`classOf` program) parents
  let registered = defined {globalNames = registerClass familySymbol (ClassInfo (map fst members) parentFamilies [] [] Map.empty outputs []) (globalNames defined)}
  -- parent projections come first, so a law's type can use a parent's
  -- members through the dictionary.
  -- each accessor is built from the checked constructor, not elaborated
  -- again: its type is the field's type, with earlier fields projected.
  checked <- maybe (failure "missing flock constructor") pure (Map.lookup constructorSymbol (globals (programEnvironment registered)))
  let accessors = projections Implicit (map parameterPlicity parameters) familySymbol checked
      define current (name, inferred) =
        let identity = SymbolId owner name
         in bindLocal name (FreshName identity (K.inferredUniverses inferred)) <$> defineAccessor current (identity, inferred)
  withParents <-
    foldM
      ( \current (index, (parent, inferred)) -> do
          let name = flockName ++ "_parent_" ++ show index
          inserted <- define current (name, inferred)
          parentFamily <- classOf parent inserted
          pure (registerInstance True (defaultPriority, False) parentFamily (SymbolId owner name) inserted)
      )
      registered
      (zip [1 :: Int ..] (zip parents accessors))
  foldM define withParents (zip (map fst members) (drop (length parents) accessors))
  where
    classOf parent current = case parent of
      Application (Name name) _ | Just (FreshName symbol _) <- lookupName name (globalNames current), Map.member symbol (nameClasses (globalNames current)) -> pure symbol
      Name name | Just (FreshName symbol _) <- lookupName name (globalNames current), Map.member symbol (nameClasses (globalNames current)) -> pure symbol
      _ -> failure "a parent requirement must apply a flock"
insertClass _ _ _ = failure "expected flock declaration"

-- one accessor per field: replace earlier fields by projections from the
-- same value. data values are explicit inputs; flock dictionaries are implicit.
-- constructor parameters are implicit, while the family keepeth its own
-- parameter plicities. de bruijn indices avoid generated source binders.
projections :: Plicity -> [Plicity] -> SymbolId -> Definition -> [K.Inferred]
projections valuePlicity parameterPlicities family Definition {definitionUniverses, definitionConstraints, definitionType} =
  [ K.Inferred definitionUniverses definitionConstraints (wrap Core.Lambda (Field index (Local 0))) (wrap Pi (project index field))
  | (index, (_, field)) <- zip [0 ..] fields
  ]
  where
    parameterCount = length parameterPlicities
    (parameters, fields) = splitAt parameterCount (fst (termTelescope definitionType))
    levels = [LParam level | level <- [0 .. definitionUniverses - 1]]
    valueType = foldl (\function (plicity, index) -> Apply plicity function (Local index)) (Global family levels) (zip parameterPlicities (reverse [0 .. parameterCount - 1]))
    wrap binder body = foldr (binder Implicit . snd) (binder valuePlicity valueType body) parameters
    -- field `index` seeth the parameters and earlier fields; under the
    -- accessor it seeth the parameters and the projected value.
    project index =
      runIdentity . traverseScoped \bound term descend -> case term of
        Local local
          | local < bound -> pure term
          | outer <- local - bound,
            outer < index ->
              pure (Field (index - 1 - outer) (Local bound))
          | otherwise -> pure (Local (local - index + 1))
        _ -> descend

-- named members lower to ordinary lets and the flock's checked constructor.
-- registration addeth the complete, kernel-checked dictionary to instance search.
insertInstance :: ModuleId -> SourceProgram -> Declaration -> Checking SourceProgram
insertInstance owner program@SourceProgram {..} BizenDeclaration {..} = inContext ("in bizen of '" ++ writtenClass bizenType ++ "': ") do
  let identity = fresh (0 :: Int)
  definitions <- foldM member Map.empty bizenMembers
  (result, (), memberHoles, references) <- elaborateHoles program do
    (annotation, kind) <- inferExpression programEnvironment globalNames emptyScope bizenType
    requireUniverse emptyScope kind
    settleAnnotation programEnvironment globalNames
    expected <- eval emptyScope annotation
    term <- lowerDictionary program emptyScope expected (writtenNames bizenType) definitions
    pure (term, expected, ())
  family <- resultClass (K.inferredType result)
  environment <- fromString (K.defineInferred programEnvironment identity result)
  -- two bizens with one pattern would make selection incoherent.
  let existing = maybe [] classInstances (Map.lookup family classes)
  when (any (sameInstance environment identity) existing) (failure "a bizen with the same ilk already exists")
  let registered = registerInstance False (fromMaybe defaultPriority bizenPriority, bizenFallback) family identity program {programEnvironment = environment, checkedDefinitions = (identity, result) : checkedDefinitions}
  pure registered {programHoles = reverse memberHoles ++ programHoles, programReferences = Map.insert identity references programReferences}
  where
    member definitions Declaration {..} = do
      when declarationFixpoint (failure "a bizen member is a let, not fast")
      when (Map.member declarationName definitions) (failure ("bizen member repeateth '" ++ declarationName ++ "'"))
      pure (Map.insert declarationName (maybe declarationBody (Ascription declarationBody) declarationAnnotation) definitions)
    member _ _ = failure "a bizen inholdeth only let definitions"
    writtenNames (Product parameters result) = map parameterName parameters ++ writtenNames result
    writtenNames _ = []
    -- private spellings cannot collide with present or later source names;
    -- every generated identity must also be absent from the whole environment.
    fresh index =
      let symbol = SymbolId owner ("#instance_" ++ show index)
       in if Map.member symbol (globals programEnvironment) then fresh (index + 1) else symbol
    classes = nameClasses globalNames
    resultClass = \case
      Pi Implicit _ codomain -> resultClass codomain
      Pi Explicit _ _ -> failure "a bizen ilk taketh only implicit parameters"
      term
        | (Global family _, _) <- termSpine term,
          Map.member family classes ->
            pure family
      _ -> failure "a bizen ilk must end in a flock application"
    writtenClass = \case
      Product _ result -> writtenClass result
      Application (Name name) _ -> name
      Name name -> name
      _ -> "?"
insertInstance _ _ _ = failure "expected bizen declaration"

-- constructor domains supply the sugar's omitted member annotations. each
-- supplied field becometh one ordinary let, in constructor order, so later
-- fields see earlier values and types. its own right-hand side still seeth the
-- global accessor. no retry changeth how a source name is resolved.
lowerDictionary :: SourceProgram -> Scope -> N.Value -> [Maybe String] -> Map.Map String Expression -> Elaboration Term
lowerDictionary SourceProgram {..} = bindHeader
  where
    classes = nameClasses globalNames
    bindHeader scope expected written definitions =
      E.force expected >>= \case
        N.VPi Implicit domain codomain -> do
          annotation <- quoteFolded scope domain
          let (name, rest) = case written of
                name : rest -> (name, rest)
                [] -> (Nothing, [])
          (current, next) <- bindDomain scope name domain codomain
          Core.Lambda Implicit annotation <$> bindHeader current next rest definitions
        N.VPi Explicit _ _ -> E.failure "a bizen ilk taketh only implicit parameters"
        target -> do
          (_, term, used, bindings) <- build scope target definitions
          case Set.toList (Map.keysSet definitions `Set.difference` used) of
            name : _ -> E.failure ("'" ++ name ++ "' is not a member of this flock or a parent it witnesseth")
            [] -> pure (foldr (uncurry Let) term bindings)
    build scope target definitions = do
      (family, arguments, info) <- classApplication target >>= maybe (E.failure "a bizen ilk must end in a flock application") pure
      constructor <- case Map.lookup family (globals programEnvironment) of
        Just Definition {definitionBody = TypeConstructor InductiveInfo {inductiveConstructorInfo = [(constructor, _)]}} -> pure constructor
        _ -> E.failure "a flock requireth one checked constructor"
      levels <- E.freshUniverses constructor
      ty <- inferCore scope (Global constructor levels)
      (head, signature) <- foldM (fixParameter scope) (Global constructor levels, ty) arguments
      (current, term, used, bindings) <- fields scope head signature (classMembers info) definitions
      result <- inferCore current term
      E.unify (scopeContext current) result target
      pure (current, term, used, bindings)
    fixParameter scope (term, ty) (_, value) =
      E.force ty >>= \case
        N.VPi Implicit _ codomain -> do
          argument <- quoteFolded scope value
          (Apply Implicit term argument,) <$> E.instantiate codomain value
        _ -> E.failure "invalid flock constructor"
    fields scope term ty pending definitions =
      E.force ty >>= \case
        N.VPi Implicit domain codomain -> do
          parent <- classApplication domain
          let inline = maybe False (\(family, _, _) -> not (Set.disjoint (Map.keysSet definitions) (inheritedMembers Set.empty family))) parent
          -- ordinary parent evidence retaineth precedence over inline fields.
          -- search compareth class identities, including imported namesakes.
          existing <- if inline then E.attempt (resolveInstance programEnvironment globalNames (scopeContext scope) domain) else pure Nothing
          (current, argument, used, bindings) <-
            case existing of
              Just argument -> pure (scope, argument, Set.empty, [])
              Nothing | inline -> build scope domain definitions
              Nothing -> do
                (argument, _) <- implicitArgument globalNames (scopeContext scope) domain
                pure (scope, argument, Set.empty, [])
          annotation <- quoteFolded current domain
          value <- evalArgument current argument
          next <- E.instantiate codomain value
          let bound = define current Nothing value domain
              applied = Apply Implicit (shiftTerm (depth current - depth scope + 1) term) (Local 0)
          (final, body, later, following) <- fields bound applied next pending definitions
          pure (final, body, Set.union used later, bindings ++ [(annotation, argument)] ++ following)
        N.VPi Explicit domain codomain
          | name : rest <- pending -> do
              source <- maybe (E.failure ("bizen is missing member '" ++ name ++ "'")) pure (Map.lookup name definitions)
              annotation <- quoteFolded scope domain
              argument <- checkExpression programEnvironment globalNames scope source domain
              value <- evalArgument scope argument
              next <- E.instantiate codomain value
              let bound = define scope (Just name) value domain
                  applied = Apply Explicit (shiftTerm 1 term) (Local 0)
              (current, body, used, bindings) <- fields bound applied next rest definitions
              pure (current, body, Set.insert name used, (annotation, argument) : bindings)
        N.VPi Explicit _ _ -> E.failure "invalid flock constructor"
        _ | null pending -> pure (scope, term, Set.empty, [])
        _ -> E.failure "invalid flock constructor"
    classApplication value =
      E.force value >>= \case
        N.VNeutral neutral
          | (N.NGlobal family _, arguments) <- N.neutralSpine neutral,
            Just info <- Map.lookup family classes ->
              pure (Just (family, arguments, info))
        _ -> pure Nothing
    inheritedMembers seen family
      | family `Set.member` seen = Set.empty
      | Just ClassInfo {classMembers, classParents} <- Map.lookup family classes =
          Set.unions (Set.fromList classMembers : map (inheritedMembers (Set.insert family seen)) classParents)
      | otherwise = Set.empty
