-- | top-level declarations: lets, host bindings, ilks, flocks, and bizens.
module Tung.Dependent.Source.Declaration
  ( insertDeclaration,
  )
where

import Control.Monad (foldM, unless, when)
import Data.Functor ((<&>))
import Data.Functor.Identity (Identity (..))
import Data.List (uncons)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Host qualified as H
import Tung.Dependent.Inductive qualified as I
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Elaborate
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Source.Expression
import Tung.Dependent.Source.Instance (implicitArgument, resolveInstance, sameInstance, solveInstances)
import Tung.Dependent.Source.Scope
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Syntax qualified as Core
import Tung.Identity (ModuleId (..), SymbolId (..), inductionSymbol)
import Tung.Token (SourceFailure (..))

-- universe holes are fresh across the complete declaration, including its
-- annotation and every occurrence of a universe-polymorphic global.
type Elaboration = E.Elaboration

-- a shown declaration exporteþ every name it introduceþ.
insertDeclaration :: ModuleId -> SourceProgram -> Declaration -> Either SourceFailure SourceProgram
insertDeclaration owner program = \case
  ImportDeclaration {} -> pure program
  declaration@FlockDeclaration {} -> insertClass owner program declaration
  declaration@BizenDeclaration {} -> insertInstance owner program declaration
  ShownDeclaration declaration -> exportIntroduced program <$> insertDeclaration owner program declaration
  ReExportDeclaration names -> reexportNames program names
  declaration@InductiveDeclaration {} -> insertInductive owner program declaration
  declaration@AssumptionDeclaration {} -> insertAssumption owner program declaration
  Declaration {..} -> Error.inContext ("in let '" ++ declarationName ++ "': ") do
    let SourceProgram {..} = program
        identity = SymbolId owner declarationName
    unless (declarationName /= "_") (Error.failure "top-level definitions require a name")
    repeated localNames [declarationName]
    (result, (), holes) <- elaborateHoles program ((\(term, ty) -> (term, ty, ())) <$> inferDefinition programEnvironment globalNames emptyScope declarationName declarationAnnotation declarationBody)
    environment <- Error.fromString (K.defineInferred programEnvironment identity result)
    pure (bindLocal declarationName (FreshName identity (K.inferredUniverses result)) program {programEnvironment = environment, checkedDefinitions = (identity, result) : checkedDefinitions, programHoles = reverse holes ++ programHoles})
  HostDeclaration {..} -> Error.inContext ("in let '" ++ hostName ++ "': ") do
    let SourceProgram {..} = program
        identity = SymbolId owner hostName
    unless (hostName /= "_") (Error.failure "top-level definitions require a name")
    repeated localNames [hostName]
    signature <- elaborate program do
      result@(_, kind) <- inferExpression programEnvironment globalNames emptyScope hostAnnotation
      requireUniverse emptyScope kind
      pure result
    model <-
      traverse
        ( \written -> case lookupName written globalNames >>= bindingSymbol of
            Just symbol -> pure symbol
            Nothing -> Error.failure ("unknown model '" ++ written ++ "'")
        )
        hostModel
    environment <- Error.fromString (H.defineHost programEnvironment identity hostKey model signature)
    let universes = maybe 0 definitionUniverses (Map.lookup identity (globals environment))
    pure (bindLocal hostName (FreshName identity universes) program {programEnvironment = environment})

-- an assumption checkeþ only its type; þe kernel stores it wiþout a body.
insertAssumption :: ModuleId -> SourceProgram -> Declaration -> Either SourceFailure SourceProgram
insertAssumption owner program@SourceProgram {..} AssumptionDeclaration {..} = Error.inContext ("in orsend '" ++ assumptionName ++ "': ") do
  let identity = SymbolId owner assumptionName
  unless (assumptionName /= "_") (Error.failure "an orsend requireþ a name")
  repeated localNames [assumptionName]
  signature <- elaborate program do
    result@(_, kind) <- inferExpression programEnvironment globalNames emptyScope assumptionAnnotation
    requireUniverse emptyScope kind
    pure result
  environment <- Error.fromString (K.assume programEnvironment identity signature)
  pure (bindLocal assumptionName (FreshName identity (K.inferredUniverses signature)) program {programEnvironment = environment})
insertAssumption _ _ _ = Error.failure "expected orsend declaration"

insertInductive :: ModuleId -> SourceProgram -> Declaration -> Either SourceFailure SourceProgram
insertInductive owner program@SourceProgram {..} InductiveDeclaration {..} = Error.inContext ("in ilk '" ++ inductiveName ++ "': ") do
  let family = SymbolId owner inductiveName
      eliminator = inductionSymbol family
      members = inductiveName : map constructorName inductiveConstructors
      uniform = uniformParameters inductiveName inductiveConstructors inductiveSignature
  unless (all (/= "_") members) (Error.failure "ilk and constructor declarations require names")
  repeated localNames members
  signature <- elaborate program do
    result@(_, kind) <- inferExpression programEnvironment globalNames emptyScope inductiveSignature
    requireUniverse emptyScope kind
    pure result
  Error.fromString (K.validate programEnvironment signature)
  normalSignature <- Error.fromString (N.normalise (globals programEnvironment) 0 (K.inferredTerm signature))
  let info = InductiveInfo (length uniform) (drop (length uniform) (productPlicities normalSignature)) []
      provisionalDefinition = Definition (K.inferredUniverses signature) (K.inferredConstraints signature) (K.inferredTerm signature) (TypeConstructor info)
      provisional = K.Environment (Map.insert family provisionalDefinition (globals programEnvironment))
  ((rawSignature, constructors), constraints) <- E.runElaboration (displayName globalNames) (globals provisional) do
    levels <- E.freshLevels (K.inferredUniverses signature)
    rawSignature <- E.fromEither (instantiateLevels levels (K.inferredTerm signature))
    let names = insertName inductiveName (FixedName family levels) globalNames
    -- the staged family template is checked before entering this private
    -- scope. every self-reference shareþ one universe vector; final insertion
    -- generaliseþ and independently checkeþ the complete constructor group.
    inferCore emptyScope (Global family levels)
    (scope, domains) <- bindUniform emptyScope uniform rawSignature
    constructors <- mapM (elaborateConstructor provisional names scope domains) inductiveConstructors
    -- a constructor annotation may use a flock, as a law useþ a parent's
    -- members; its dictionaries are found among þe constructor's own fields.
    solveInstances provisional names
    remaining <- E.takeInstanceGoals
    unless (null remaining) (E.failure "a bizen requirement haþ a type þat is still unknown; add an annotation")
    rawSignature <- E.zonk rawSignature
    constructors <- mapM (\(name, ty) -> (name,) <$> E.zonk ty) constructors
    pure (rawSignature, constructors)
  environment <- Error.fromString (I.inferInductive programEnvironment family eliminator (length uniform) rawSignature constructors constraints)
  let definitions = globals environment
      register current name = case Map.lookup (SymbolId owner name) definitions of
        Just definition -> pure (bindLocal name (FreshName (SymbolId owner name) (definitionUniverses definition)) current)
        Nothing -> Error.failure "inductive checker omitted a declared member"
  foldM register program {programEnvironment = environment} members
  where
    elaborateConstructor environment names scope domains ConstructorDeclaration {..} = do
      (annotation, kind) <- inferExpression environment names scope constructorAnnotation
      requireUniverse scope kind
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
        _ -> E.failure "uniform inductive parameters requireþ a product signature"

-- `flock name:[parameters, @:parent, *] { members }` becomeþ a
-- one-constructor family, one accessor per member, and one instance per parent.
insertClass :: ModuleId -> SourceProgram -> Declaration -> Either SourceFailure SourceProgram
insertClass owner program FlockDeclaration {..} = Error.inContext ("in flock '" ++ flockName ++ "': ") do
  -- `β: * out` markeþ a parameter þat instance search findeþ.
  let (parameters, outputs) = unzip [(parameter {parameterType = inner}, output) | parameter@Parameter {parameterName = Just _, parameterType} <- flockParameters, let (inner, output) = outputType parameterType]
      outputType = \case
        Application (Name "out") [Argument Explicit inner] -> (inner, True)
        ty -> (ty, False)
      parents = [parameterType | Parameter {parameterName = Nothing, parameterType} <- flockParameters]
  unless (all ((== Explicit) . parameterPlicity) parameters) (Error.failure "flock parameters are written name:type, wiþout '@'")
  unless (and [plicity == Implicit | Parameter plicity Nothing _ <- flockParameters]) (Error.failure "a parent requirement is written @:parent")
  repeated (localNames program) (flockName : [name | FlockMember name _ <- flockMembers] ++ [name | FlockLaw name _ _ _ <- flockMembers])
  -- a law is an ordinary member whose type is its equation. members keep
  -- source order, so a law's type nameþ þe earlier members it relateþ.
  let members = [memberType member | member <- flockMembers]
      memberType = \case
        FlockMember name ty -> (name, ty)
        FlockLaw name binders left right -> (name, lawType binders left right)
      constructor = flockName ++ "_make"
      family = Application (Name flockName) [Argument parameterPlicity (Name name) | Parameter {parameterPlicity, parameterName = Just name} <- parameters]
      parentName index = "#parent_" ++ show index
      -- generated local binders cannot capture source parameter names.
      parentFields = [Parameter Implicit (Just (parentName index)) parent | (index, parent) <- zip [1 :: Int ..] parents]
      memberFields = [Parameter Explicit (Just name) ty | (name, ty) <- members]
      -- a law `[binders, left = right]` stateþ þe primitive identity type
      -- over þe members.
      lawType binders left right =
        let equation = Application (Name (symbolName H.identitySymbol)) [Argument Explicit left, Argument Explicit right]
         in if null binders then equation else Product binders equation
      declaration =
        InductiveDeclaration
          flockName
          (Product parameters Universe)
          [ConstructorDeclaration constructor (Product (parentFields ++ memberFields) family)]
  defined <- insertInductive owner program declaration
  familySymbol <- symbolOf flockName defined
  constructorSymbol <- symbolOf constructor defined
  parentFamilies <- traverse (`classOf` program) parents
  let registered = defined {globalNames = registerClass familySymbol (ClassInfo constructorSymbol (map fst members) parentFamilies [] [] Map.empty outputs []) (globalNames defined)}
  -- parent projections come first, so a law's type can use a parent's
  -- members þrough þe dictionary.
  -- each accessor is built from þe checked constructor, not elaborated
  -- again: its type is þe field's type, wiþ earlier fields projected.
  Definition {definitionUniverses, definitionConstraints, definitionType} <-
    maybe (Error.failure "missing flock constructor") pure (Map.lookup constructorSymbol (globals (programEnvironment registered)))
  let accessors = projections (length parameters) familySymbol definitionUniverses definitionConstraints definitionType
      define current (name, inferred) = do
        let identity = SymbolId owner name
        environment <- Error.fromString (K.defineInferred (programEnvironment current) identity inferred)
        pure (bindLocal name (FreshName identity definitionUniverses) current {programEnvironment = environment, checkedDefinitions = (identity, inferred) : checkedDefinitions current})
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
      _ -> Error.failure "a parent requirement must apply a flock"
insertClass _ _ _ = Error.failure "expected flock declaration"

-- þe accessors of a one-constructor family, one per field: under þe
-- family's parameters and a dictionary, a field's type wiþ each earlier
-- field replaced by its projection, and þe projection itself.
projections :: Int -> SymbolId -> Int -> [Constraint] -> Term -> [K.Inferred]
projections parameterCount family universes constraints constructorType =
  [ K.Inferred universes constraints (wrap Core.Lambda (Field index (Local 0))) (wrap Pi (project index field))
  | (index, field) <- zip [0 ..] fields
  ]
  where
    (parameters, afterParameters) = splitTelescope parameterCount constructorType
    fields = telescope afterParameters
    levels = [LParam level | level <- [0 .. universes - 1]]
    dictionary = foldl (\function index -> Apply Explicit function (Local index)) (Global family levels) (reverse [0 .. parameterCount - 1])
    wrap binder body = foldr (binder Implicit) (binder Implicit dictionary body) parameters
    splitTelescope 0 term = ([], term)
    splitTelescope count (Pi _ domain codomain) = let (rest, final) = splitTelescope (count - 1) codomain in (domain : rest, final)
    splitTelescope _ term = ([], term)
    telescope = \case
      Pi _ domain codomain -> domain : telescope codomain
      _ -> []
    -- field `index` seeþ þe parameters and þe earlier fields; under þe
    -- accessor it seeþ þe parameters and þe dictionary.
    project index =
      runIdentity . traverseScoped \bound term descend -> case term of
        Local local
          | local < bound -> pure term
          | outer <- local - bound,
            outer < index ->
              pure (Field (index - 1 - outer) (Local bound))
          | otherwise -> pure (Local (local - index + 1))
        _ -> descend

-- `bizen:[@parameters, @:requirements, arguments flock] { members }`. the
-- dictionary is the flock constructor applied to the members; parent fields
-- are solved by instance search inside the bizen's own scope.
insertInstance :: ModuleId -> SourceProgram -> Declaration -> Either SourceFailure SourceProgram
insertInstance owner program@SourceProgram {..} BizenDeclaration {..} = Error.inContext ("in bizen of '" ++ writtenClass bizenType ++ "': ") do
  let identity = fresh (0 :: Int)
  definitions <- traverse member bizenMembers
  (result, (), memberHoles) <- elaborateHoles program do
    (annotation, kind) <- inferExpression programEnvironment globalNames emptyScope bizenType
    requireUniverse emptyScope kind
    expected <- eval emptyScope annotation
    term <- bizenBody program emptyScope expected written definitions
    pure (term, expected, ())
  family <- resultClass (K.inferredType result)
  environment <- Error.fromString (K.defineInferred programEnvironment identity result)
  -- two bizens wiþ one pattern would make selection incoherent.
  let existing = maybe [] classInstances (Map.lookup family classes)
  when (any (sameInstance environment identity) existing) (Error.failure "a bizen wiþ þe same type already exists")
  let registered = registerInstance False (fromMaybe defaultPriority bizenPriority, bizenFallback) family identity program {programEnvironment = environment, checkedDefinitions = (identity, result) : checkedDefinitions}
  pure registered {programHoles = reverse memberHoles ++ programHoles}
  where
    written = case bizenType of
      Product items _ -> map parameterName items
      _ -> []
    -- private spellings cannot collide wiþ present or later source names;
    -- every generated identity must also be absent from the whole environment.
    fresh index =
      let symbol = SymbolId owner ("#instance_" ++ show index)
       in if Map.member symbol (globals programEnvironment) then fresh (index + 1) else symbol
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
    writtenClass = \case
      Product _ result -> writtenClass result
      Application (Name name) _ -> name
      Name name -> name
      _ -> "?"
insertInstance _ _ _ = Error.failure "expected bizen declaration"

-- a bizen's dictionary under its implicit binders.
bizenBody :: SourceProgram -> Scope -> N.Value -> [Maybe String] -> [(String, Expression)] -> Elaboration Term
bizenBody program@SourceProgram {..} scope expected written definitions =
  E.force expected >>= \case
    N.VPi Implicit domain codomain -> do
      domainTerm <- quote scope domain
      let (name, rest) = nextName written
      next <- E.instantiate codomain (N.VNeutral (N.NLocal (depth scope)))
      Core.Lambda Implicit domainTerm <$> bizenBody program (extend scope name domain) next rest definitions
    N.VPi Explicit _ _ -> E.failure "a bizen type takeþ only implicit parameters"
    target -> dictionary scope target definitions
  where
    -- a bizen may also define þe members of a parent flock þat
    -- haþ no bizen of its own. þat parent's dictionary is built inline, and
    -- inherited instance search projecteþ it from þis one.

    classes = nameClasses globalNames
    dictionary scope target definitions = do
      (term, used, _) <- build scope target []
      case [name | (name, _) <- definitions, name `notElem` used] of
        name : _ -> E.failure ("'" ++ name ++ "' is not a member of this flock or a parent it witnesseþ")
        [] -> pure term
      where
        given = map fst definitions
        -- þe members defined so far, including an inline parent's, are
        -- siblings þat later members, such as laws, may name.
        build scope target siblings = do
          (classInfo, familyArguments) <-
            classApplication target >>= \case
              Just found -> pure found
              Nothing -> E.failure "a bizen type must end in a flock application"
          let wanted = classMembers classInfo
          case [name | name <- wanted, name `notElem` given] of
            name : _ -> E.failure ("bizen is missing member '" ++ name ++ "'")
            [] -> pure ()
          let constructor = classConstructor classInfo
          levels <- E.freshUniverses constructor
          constructorType <- inferCore scope (Global constructor levels)
          -- the head's arguments fix the flock parameters before fields are checked.
          (headTerm, headType) <- foldM (fixParameter scope) (Global constructor levels, constructorType) familyArguments
          (term, ty, used, defined) <- fields scope headTerm headType wanted [] siblings
          E.unify (scopeContext scope) ty target
          pure (term, wanted ++ used, defined)
        -- parent fields precede member fields.
        fields scope term ty pending used siblings =
          E.force ty >>= \case
            N.VPi Implicit domain codomain -> do
              defines <-
                classApplication domain <&> \case
                  Just (parent, _) -> any (`elem` given) (classMembers parent)
                  Nothing -> False
              -- a parent wiþ a bizen of its own keepeþ it.
              owned <-
                if defines
                  then maybe False (const True) <$> E.attempt (resolveInstance programEnvironment globalNames (scopeContext scope) domain)
                  else pure False
              (argument, value, parentUsed, withParent) <-
                if defines && not owned
                  then do
                    (argument, parentUsed, withParent) <- build scope domain siblings
                    value <- eval scope argument
                    pure (argument, value, parentUsed, withParent)
                  else do
                    (argument, value) <- implicitArgument globalNames (scopeContext scope) domain
                    pure (argument, value, [], siblings)
              next <- E.instantiate codomain value
              fields scope (Apply Implicit term argument) next pending (used ++ parentUsed) withParent
            N.VPi Explicit domain codomain
              | name : rest <- pending,
                Just body <- lookup name definitions -> do
                  argument <- member scope siblings name body domain
                  value <- eval scope argument
                  next <- E.instantiate codomain value
                  fields scope (Apply Explicit term argument) next rest used (siblings ++ [(name, value, domain)])
            N.VPi Explicit _ _ -> E.failure "invalid flock constructor"
            other -> pure (term, other, used, siblings)
        -- a member þat nameþ itself refereþ to þe flock's accessor, as any
        -- visible name doþ; a recursive member is an ordinary recursive let.
        -- a member þat nameþ an earlier member of þis bizen at þe bizen's
        -- own type cannot find þe bizen yet; it seeþ þat member's definition.
        member scope siblings name body domain
          | any ((`Set.member` usedNames) . fst3) siblings && name `Set.notMember` usedNames =
              trial >>= \case
                Just (term, commit) -> commit >> pure term
                Nothing -> do
                  let bound = foldl (\current (sibling, value, ty) -> define current (Just sibling) value ty) scope siblings
                  inner <- checkExpression programEnvironment globalNames bound body domain
                  wrap scope siblings inner
          | otherwise = checkExpression programEnvironment globalNames scope body domain
          where
            usedNames = referencedNames programEnvironment globalNames body
            trial = E.speculate (checkExpression programEnvironment globalNames scope body domain <* solveInstances programEnvironment globalNames <* solved)
        fst3 (first, _, _) = first
        -- each sibling becomeþ a let around þe member.
        wrap _ [] inner = pure inner
        wrap current ((sibling, value, ty) : rest) inner = do
          annotation <- quote current ty
          valueTerm <- quote current value
          Let annotation valueTerm <$> wrap (define current (Just sibling) value ty) rest inner
        solved = E.takeInstanceGoals >>= \goals -> unless (null goals) (E.failure "unsolved requirement")
        classApplication value =
          E.force value <&> \case
            N.VNeutral neutral | (N.NGlobal family _, arguments) <- N.neutralSpine neutral, Just classInfo <- Map.lookup family classes -> Just (classInfo, arguments)
            _ -> Nothing
    fixParameter scope (term, ty) (_, value) =
      E.force ty >>= \case
        N.VPi Implicit _ codomain -> do
          argument <- quote scope value
          (Apply Implicit term argument,) <$> E.instantiate codomain value
        _ -> E.failure "invalid flock constructor"

-- þe next written binder name, if any.
nextName :: [Maybe String] -> (Maybe String, [Maybe String])
nextName = fromMaybe (Nothing, []) . uncons
