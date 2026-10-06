-- | checked inductive families and their generated induction principles.
-- only direct recursive fields are supported; all other occurrences are
-- rejected before any recursive computation rule entereþ the environment.
module Tung.Dependent.Inductive
  ( InductiveDeclaration (..),
    defineInductive,
    inferInductive,
  )
where

import Control.Monad (foldM, unless, when)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State.Strict (runStateT)
import Data.Foldable (traverse_)
import Data.Functor.Identity (Identity (..))
import Data.List (nub)
import Data.Map.Strict qualified as Map
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Syntax
import Tung.Dependent.Universe qualified as U
import Tung.Identity (SymbolId)

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
    constructorType :: Term,
    constructorFields :: [(Plicity, Term, Bool)],
    constructorIndices :: [(Plicity, Term)]
  }

-- rigid declarations must prove every obligation from their exported universe
-- constraints. insertion is atomic: no partly checked family is returned.
defineInductive :: K.Environment -> InductiveDeclaration -> Either String K.Environment
defineInductive environment declaration@InductiveDeclaration {..} = do
  validateSyntax (Just inductiveUniverses) False declaration
  (result, obligations) <- runStateT (build environment declaration) inductiveConstraints
  unless (all (U.entails inductiveConstraints) (K.openObligations inductiveConstraints obligations)) (Left "unproved universe constraint in inductive declaration")
  pure result

-- source staging useþ one fixed vector of distinct universe placeholders for
-- self references. explicit universe arguments belong to 'defineInductive'.
-- joint generalisation can introduce constructor-only parameters, so each
-- placeholder vector is then widened to the group's complete canonical vector.
inferInductive :: K.Environment -> SymbolId -> SymbolId -> Int -> Term -> [(SymbolId, Term)] -> [Constraint] -> Either String K.Environment
inferInductive environment name eliminator parameters annotation constructors constraints = do
  let raw = InductiveDeclaration name eliminator parameters 0 constraints annotation constructors
  validateSyntax Nothing True raw
  let selfArguments = nub (concatMap (selfUniverses name) (annotation : map snd constructors))
  unless (length selfArguments <= 1) (Left "recursive family universe arguments must remain uniform")
  traverse_ checkPlaceholders selfArguments
  (universes, assumptions, signatures) <- K.generaliseTerms (annotation : map snd constructors) constraints
  case signatures of
    family : constructorTypes -> do
      let canonical = map LParam [0 .. universes - 1]
          declaration =
            InductiveDeclaration
              name
              eliminator
              parameters
              universes
              assumptions
              (replaceSelfUniverses name canonical family)
              (zip (map fst constructors) (map (replaceSelfUniverses name canonical) constructorTypes))
      (K.Environment built, obligations) <- runStateT (build environment declaration) assumptions
      let constraints = nub obligations
          updated = declaration {inductiveConstraints = constraints}
          names = name : eliminator : map fst constructors
          final = foldr (Map.adjust (\definition -> definition {definitionConstraints = constraints})) built names
      validateSyntax (Just universes) False updated
      -- adding inferred assumptions cannot alter positivity or the generated
      -- eliminator. recheck final signatures rigidly, wiþout rebuilding them.
      (_, rigid) <- runStateT (traverse_ (K.checkType final K.emptyContext . definitionType . (final Map.!)) names) constraints
      unless (all (U.entails constraints) (K.openObligations constraints rigid)) (Left "unproved universe constraint in inductive declaration")
      pure (K.Environment final)
    [] -> Left "missing inductive family signature"
  where
    checkPlaceholders levels = do
      let identities = [identity | LMeta identity <- levels]
      unless (length identities == length levels && length identities == length (nub identities)) (Left "inductive self references requireþ distinct inference placeholders")

validateSyntax :: Maybe Int -> Bool -> InductiveDeclaration -> Either String ()
validateSyntax bound holes InductiveDeclaration {..} = do
  when (inductiveParameters < 0) (Left "negative inductive parameter count")
  when (inductiveUniverses < 0) (Left "negative inductive universe count")
  let signatures = inductiveType : map snd inductiveConstructors
  traverse_ K.rejectMetas signatures
  traverse_ (K.validLevel bound holes) (concatMap termLevels signatures ++ concatMap constraintLevels inductiveConstraints)
  unless (U.satisfiable inductiveConstraints) (Left "inconsistent universe constraints")

build :: K.Environment -> InductiveDeclaration -> K.Typing K.Environment
build (K.Environment globals) declaration@InductiveDeclaration {..} = do
  let names = inductiveName : inductiveEliminator : map fst inductiveConstructors
  unless (length names == length (nub names) && all (`Map.notMember` globals) names) (K.failure "duplicate inductive declaration name")
  K.checkType globals K.emptyContext inductiveType
  familyType <- lift (N.normalise globals 0 inductiveType)
  let (familyBinders, familyResult) = termTelescope familyType
      (parameters, indices) = splitAt inductiveParameters familyBinders
  unless (length parameters == inductiveParameters) (K.failure "inductive parameter count exceedeth family signature")
  targetLevel <- case familyResult of
    Sort level -> pure level
    _ -> K.failure "inductive family signature must end in a universe"
  let initialInfo = InductiveInfo inductiveParameters (map fst indices) []
      entry annotation body = Definition inductiveUniverses inductiveConstraints annotation body
      staged = Map.insert inductiveName (entry familyType (TypeConstructor initialInfo)) globals
  checked <- traverse (checkConstructor staged declaration parameters indices targetLevel) inductiveConstructors
  let info = initialInfo {inductiveConstructorInfo = [(constructorName constructor, constructorFields constructor) | constructor <- checked]}
      familyGlobals = Map.insert inductiveName (entry familyType (TypeConstructor info)) globals
      constructorGlobals =
        foldl
          (\environment (index, constructor) -> Map.insert (constructorName constructor) (entry (constructorType constructor) (DataConstructor inductiveName index)) environment)
          familyGlobals
          (zip [0 ..] checked)
  recursorType <- lift (generateRecursor declaration parameters indices checked)
  K.checkType constructorGlobals K.emptyContext recursorType
  let recursor = Definition (inductiveUniverses + 1) inductiveConstraints recursorType (Eliminator inductiveName)
  pure (K.Environment (Map.insert inductiveEliminator recursor constructorGlobals))

checkConstructor :: Globals -> InductiveDeclaration -> Telescope -> Telescope -> Level -> (SymbolId, Term) -> K.Typing Constructor
checkConstructor globals declaration@InductiveDeclaration {..} parameters indices targetLevel (name, annotation) = do
  K.checkType globals K.emptyContext annotation
  normal <- lift (N.normalise globals 0 annotation)
  let (binders, result) = termTelescope normal
      (inherited, fields) = splitAt inductiveParameters binders
  unless (length inherited == inductiveParameters) (K.failure "constructor is missing uniform parameters")
  parameterContext <- inherit K.emptyContext parameters inherited
  (fieldContext, classified) <- checkFields parameterContext fields
  resultIndices <- familyApplication globals declaration parameters indices fieldContext result
  pure (Constructor name normal classified resultIndices)
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
      -- a recursive field is þe family or a function ending in it, whose
      -- inputs do not mention þe family: strictly positive.
      recursive <-
        if containsFamily inductiveName domain
          then do
            let (inputs, result) = termTelescope domain
            when (any (containsFamily inductiveName . snd) inputs) (K.failure "inductive occurrence must be strictly positive")
            inputContext <- foldM (\current (_, input) -> K.bind current <$> K.evaluate globals current input) context inputs
            familyApplication globals declaration parameters indices inputContext result
            pure True
          else pure False
      value <- K.evaluate globals context domain
      (ending, remaining) <- checkFields (K.bind context value) rest
      pure (ending, (plicity, domain, recursive) : remaining)

-- a family occurrence is a saturated application of þe family, never inside
-- its own parameters or indices.
familyApplication :: Globals -> InductiveDeclaration -> Telescope -> Telescope -> K.Context -> Term -> K.Typing [(Plicity, Term)]
familyApplication globals InductiveDeclaration {..} parameters indices context term = do
  let (headTerm, arguments) = termSpine term
      expectedPlicities = map fst (parameters ++ indices)
      contextDepth = length (K.contextTypes context)
  levels <- case headTerm of
    Global name universeArguments | name == inductiveName -> pure universeArguments
    _ -> K.failure "inductive occurrence must be a direct saturated family application"
  unless (length levels == inductiveUniverses) (K.failure "wrong number of inductive universe arguments")
  traverse_ (K.oblige . uncurry LevelEqual) (zip levels (map LParam [0 .. inductiveUniverses - 1]))
  unless (length arguments == length expectedPlicities && map fst arguments == expectedPlicities) (K.failure "inductive result requireþ every parameter and index")
  unless (all (not . containsFamily inductiveName . snd) arguments) (K.failure "inductive family cannot occur inside its arguments")
  let (actualParameters, resultIndices) = splitAt inductiveParameters arguments
  traverse_
    ( \(position, (_, argument)) -> do
        actual <- K.evaluate globals context argument
        expected <- K.evaluate globals context (Local (contextDepth - position - 1))
        K.convert globals context actual expected
    )
    (zip [0 ..] actualParameters)
  pure resultIndices

-- generated signatures use stable binder levels while construction proceeds.
-- original constructor levels map to field levels; induction hypotheses add
-- extra binders without appearing in that map. quotation back to indices is
-- explicit below, so later dependent fields retain their original references.
generateRecursor :: InductiveDeclaration -> Telescope -> Telescope -> [Constructor] -> Either String Term
generateRecursor InductiveDeclaration {..} parameters indices constructors = parameterBinders parameters
  where
    parameterCount = length parameters
    levels = map LParam [0 .. inductiveUniverses - 1]
    resultLevel = LParam inductiveUniverses
    motiveLevel = parameterCount
    parameterLevels = [0 .. parameterCount - 1]
    parameterBinders [] = do
      motive <- motiveType parameterCount parameterLevels indices
      remainder <- methodBinders (parameterCount + 1) constructors
      pure (Pi Explicit motive remainder)
    parameterBinders ((_, domain) : rest) = Pi Implicit domain <$> parameterBinders rest
    motiveType depth mapping [] = do
      self <- familyTerm depth mapping
      pure (Pi Explicit self (Sort resultLevel))
    motiveType depth mapping ((plicity, domain) : rest) = do
      moved <- renameTerm mapping depth domain
      Pi plicity moved <$> motiveType (depth + 1) (mapping ++ [depth]) rest
    methodBinders depth [] = indexBinders depth parameterLevels indices
    methodBinders depth (constructor : rest) = do
      method <- methodType depth constructor
      Pi Explicit method <$> methodBinders (depth + 1) rest
    methodType depth Constructor {..} = fields depth parameterLevels constructorFields
      where
        fields current mapping [] = do
          resultIndices <- traverse (moveArgument mapping current) constructorIndices
          let values = zipWith (\(plicity, _, _) level -> (plicity, localAt current level)) constructorFields (drop parameterCount mapping)
              inherited = [(Implicit, localAt current level) | level <- parameterLevels]
              self = applyArguments (Global constructorName levels) (inherited ++ values)
          pure (applyArguments (localAt current motiveLevel) (resultIndices ++ [(Explicit, self)]))
        fields current mapping ((plicity, domain, recursive) : remaining) = do
          moved <- renameTerm mapping current domain
          let extended = mapping ++ [current]
          remainder <-
            if recursive
              then do
                -- þe hypothesis for a function field `k` is `[inputs, motive (inputs k)]`.
                movedField <- renameTerm mapping (current + 1) domain
                let (inputs, result) = termTelescope movedField
                    inputCount = length inputs
                    (_, familyArguments) = termSpine result
                    applied = applyArguments (Local inputCount) [(plicity, Local (inputCount - position - 1)) | (position, (plicity, _)) <- zip [0 ..] inputs]
                    conclusion = applyArguments (localAt (current + 1 + inputCount) motiveLevel) (drop parameterCount familyArguments ++ [(Explicit, applied)])
                    hypothesis = foldr (\(plicity, input) body -> Pi plicity input body) conclusion inputs
                Pi Explicit hypothesis <$> fields (current + 2) extended remaining
              else fields (current + 1) extended remaining
          pure (Pi plicity moved remainder)
    indexBinders depth mapping [] = do
      self <- familyTerm depth mapping
      let indexValues = zipWith (\(plicity, _) level -> (plicity, localAt (depth + 1) level)) indices (drop parameterCount mapping)
          result = applyArguments (localAt (depth + 1) motiveLevel) (indexValues ++ [(Explicit, Local 0)])
      pure (Pi Explicit self result)
    indexBinders depth mapping ((plicity, domain) : rest) = do
      moved <- renameTerm mapping depth domain
      Pi plicity moved <$> indexBinders (depth + 1) (mapping ++ [depth]) rest
    familyTerm depth mapping =
      pure (applyArguments (Global inductiveName levels) (zipWith (\(plicity, _) level -> (plicity, localAt depth level)) (parameters ++ indices) mapping))
    moveArgument mapping depth (plicity, argument) = (plicity,) <$> renameTerm mapping depth argument

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

containsFamily :: SymbolId -> Term -> Bool
containsFamily name = not . null . selfUniverses name

selfUniverses :: SymbolId -> Term -> [[Level]]
selfUniverses name = \case
  Global identity levels | identity == name -> [levels]
  term -> concatMap (selfUniverses name . snd) (children term)

replaceSelfUniverses :: SymbolId -> [Level] -> Term -> Term
replaceSelfUniverses name levels = runIdentity . traverseScoped replace
  where
    replace _ (Global identity _) _ | identity == name = pure (Global name levels)
    replace _ _ descend = descend
