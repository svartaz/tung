-- | normalisation by evaluation for the checked dependent core. evaluation
-- assumeth well-typed terms and acyclic globals; it is not a termination checker.
module Tung.Dependent.Normalise
  ( Value (..),
    Closure (..),
    Neutral (..),
    neutralSpine,
    evaluate,
    instantiate,
    quote,
    normalise,
    MetaResolver,
    Normaliser (..),
    evaluateWith,
    instantiateWith,
    applyValueWith,
    quoteWith,
    quoteFoldedWith,
    quoteDisplayWith,
    forceWith,
  )
where

import Control.Monad (foldM)
import Data.Map.Strict qualified as Map
import Tung.Dependent.Literal (constructedLiteral, coreConstructor, literalConstructor, literalType, literalValue, valueLiteral)
import Tung.Dependent.Syntax
import Tung.Dependent.Universe (normaliseLevel)
import Tung.Identity (ModuleId (..), SymbolId (..))
import Tung.Primitive (HostBinding (..), HostSignature (..), HostType (..), HostValue (..), consConstructorId, emptyConstructorId, findForeignBinding, integerNegativeId, integerPositiveId, listName, naturalSuccessorId, nayConstructorId, noneConstructorId, productConstructorId, pureOperation, someConstructorId, yeaConstructorId)

data Value
  = VSort Level
  | VPi Plicity Value Closure
  | VLambda Plicity Value Closure
  | VNeutral Neutral
  | VLiteral SymbolId HostLiteral
  | VRecordType [(String, Value)]
  | VRecord [(String, Value)]
  | -- a transparent global applied to its spine, with its unfolding computed
    -- only when forced. evaluation keepeth definitions folded in nested
    -- positions; every public evaluation result is forced at its head.
    VGlued SymbolId [Level] [(Plicity, Value)] (Either String Value)
  deriving stock (Show)

data Closure = Closure [Value] Term
  deriving stock (Show)

-- neutral locals use levels, so extending a context requireth no shifting.
-- neutral applications inherit their plicity check from the core checker.
data Neutral
  = NLocal Int
  | NGlobal SymbolId [Level]
  | NApply Plicity Neutral Value
  | NMeta Int [Value]
  | NProject Neutral String
  | NField Int Neutral
  deriving stock (Show)

-- closures contain syntax and values, never a snapshot of the solution store.
-- elaboration supplieth the current resolver at every evaluation or quotation.
type MetaResolver = Int -> Either String (Maybe Term)

rejectMeta :: MetaResolver
rejectMeta _ = Left "unresolved term inference hole in core"

-- the hole solutions and definitions that evaluation and quotation read.
data Normaliser = Normaliser {resolveMeta :: MetaResolver, normalGlobals :: Globals}

-- checked core hath no holes.
closed :: Globals -> Normaliser
closed = Normaliser rejectMeta

evaluate :: Globals -> [Value] -> Term -> Either String Value
evaluate = evaluateWith . closed

-- the result is forced at its head, so callers see the same values as before
-- definitions were glued; nested positions may stay folded.
evaluateWith :: Normaliser -> [Value] -> Term -> Either String Value
evaluateWith normaliser environment term =
  evaluateGlued normaliser environment term >>= forceWith normaliser

evaluateGlued :: Normaliser -> [Value] -> Term -> Either String Value
evaluateGlued normaliser environment = \case
  Local index
    | index < 0 -> Left "negative local index"
    | otherwise -> case drop index environment of
        value : _ -> Right value
        [] -> Left "unbound local index"
  Global name levels -> case Map.lookup name (normalGlobals normaliser) of
    Nothing -> Left ("unknown global " ++ show name)
    Just definition
      | length levels /= definitionUniverses definition ->
          Left "wrong number of universe arguments"
      | otherwise -> case definitionBody definition of
          Transparent term ->
            -- global bodies are closed; the caller's local environment is irrelevant.
            Right (VGlued name (map normaliseLevel levels) [] (instantiateLevels (map normaliseLevel levels) term >>= evaluateWith normaliser []))
          _
            | Just literal <- constructedLiteral name [] -> Right (VLiteral (literalType literal) literal)
            | otherwise -> Right (VNeutral (NGlobal name (map normaliseLevel levels)))
  Sort level -> Right (VSort (normaliseLevel level))
  Pi plicity domain codomain -> do
    domainValue <- evaluateWith normaliser environment domain
    pure (VPi plicity domainValue (Closure environment codomain))
  Lambda plicity domain body -> do
    domainValue <- evaluateWith normaliser environment domain
    pure (VLambda plicity domainValue (Closure environment body))
  Apply plicity function argument -> do
    functionValue <- evaluateGlued normaliser environment function
    argumentValue <- evaluateGlued normaliser environment argument
    applyGlued normaliser plicity functionValue argumentValue
  Let _ value body -> do
    valueValue <- evaluateGlued normaliser environment value
    evaluateGlued normaliser (valueValue : environment) body
  Meta identity arguments -> do
    values <- traverse (evaluateGlued normaliser environment) arguments
    forceWith normaliser (VNeutral (NMeta identity values))
  Literal name value -> Right (VLiteral name value)
  RecordType fields -> VRecordType <$> traverse (\(name, field) -> (name,) <$> evaluateGlued normaliser environment field) fields
  Record fields -> VRecord <$> traverse (\(name, field) -> (name,) <$> evaluateGlued normaliser environment field) fields
  Project record name -> evaluateGlued normaliser environment record >>= project normaliser name
  Field index value -> evaluateGlued normaliser environment value >>= field normaliser index

-- applying a folded definition extendeth its spine; its unfolding followeth
-- lazily.
applyGlued :: Normaliser -> Plicity -> Value -> Value -> Either String Value
applyGlued normaliser plicity function argument = case function of
  VGlued name levels spine unfolded ->
    Right (VGlued name levels (spine ++ [(plicity, argument)]) (unfolded >>= \value -> applyValueWith normaliser plicity value argument))
  _ -> applyValueWith normaliser plicity function argument

instantiate :: Globals -> Closure -> Value -> Either String Value
instantiate = instantiateWith . closed

instantiateWith :: Normaliser -> Closure -> Value -> Either String Value
instantiateWith normaliser (Closure environment body) argument =
  evaluateWith normaliser (argument : environment) body

applyValueWith :: Normaliser -> Plicity -> Value -> Value -> Either String Value
applyValueWith normaliser plicity function argument =
  forceWith normaliser function >>= \case
    VLambda expected _ closure
      | plicity == expected -> instantiateWith normaliser closure argument
      | otherwise -> Left "application plicity differeth from function plicity"
    VNeutral neutral -> reduceNeutral normaliser (NApply plicity neutral argument)
    _ -> Left "application of a non-function"

-- a neutral saved in an older closure may have since acquired a solution.
-- forcing its head also resumeth applications blocked on that metavariable.
forceWith :: Normaliser -> Value -> Either String Value
forceWith normaliser value =
  forceStep normaliser value >>= \case
    -- a reduction may yield a folded value, such as a host model.
    glued@VGlued {} -> forceWith normaliser glued
    forced -> Right forced

forceStep :: Normaliser -> Value -> Either String Value
forceStep normaliser = \case
  VGlued _ _ _ unfolded -> unfolded >>= forceWith normaliser
  VNeutral (NMeta identity arguments) ->
    resolveMeta normaliser identity >>= \case
      Nothing -> Right (VNeutral (NMeta identity arguments))
      Just solution -> do
        function <- evaluateWith normaliser [] solution
        foldM (applyValueWith normaliser Explicit) function arguments
  VNeutral (NApply plicity function argument) -> do
    headValue <- forceWith normaliser (VNeutral function)
    case headValue of
      VNeutral neutral -> reduceNeutral normaliser (NApply plicity neutral argument)
      _ -> applyValueWith normaliser plicity headValue argument
  VNeutral (NProject record name) -> project normaliser name (VNeutral record)
  VNeutral (NField index value) -> field normaliser index (VNeutral value)
  value -> Right value

-- a projection reduceth on a record value and stayeth neutral on a variable.
project :: Normaliser -> String -> Value -> Either String Value
project normaliser name record =
  forceWith normaliser record >>= \case
    VRecord fields -> maybe (Left ("record hath no field '" ++ name ++ "'")) Right (lookup name fields)
    VNeutral neutral -> Right (VNeutral (NProject neutral name))
    _ -> Left "projection from a non-record"

-- a field of a constructor application is its argument after the family's
-- parameters; on a neutral value the field stayeth neutral.
field :: Normaliser -> Int -> Value -> Either String Value
field normaliser index value =
  forceWith normaliser value >>= \case
    VNeutral neutral
      | (NGlobal constructor _, arguments) <- neutralSpine neutral,
        Just Definition {definitionBody = DataConstructor owner _} <- Map.lookup constructor (normalGlobals normaliser),
        Just Definition {definitionBody = TypeConstructor InductiveInfo {inductiveParameterCount}} <- Map.lookup owner (normalGlobals normaliser) ->
          case drop (inductiveParameterCount + index) arguments of
            (_, argument) : _ -> Right argument
            [] -> Left "field of an unsaturated constructor"
      | otherwise -> Right (VNeutral (NField index neutral))
    _ -> Left "field of a non-constructor value"

-- induction reduceth only on constructors. recursive calls use direct children,
-- never an arbitrary source function or a user-supplied recursion annotation.
reduceNeutral :: Normaliser -> Neutral -> Either String Value
reduceNeutral normaliser neutral = case neutralSpine neutral of
  -- a number constructor applied to a literal is a literal.
  (NGlobal name _, [(Explicit, argument)])
    | name `elem` [naturalSuccessorId, integerPositiveId, integerNegativeId] ->
        forceWith normaliser argument >>= \case
          VLiteral _ field | Just literal <- constructedLiteral name [field] -> Right (VLiteral (literalType literal) literal)
          _ -> stuck
  -- the head is looked up once; identity comparison is a hot path.
  (NGlobal name levels, arguments) -> case Map.lookup name (normalGlobals normaliser) of
    -- a literal case chooseth once both compared values are literals.
    Just Definition {definitionBody = Host "literal_case" _}
      | [_, _, (Explicit, value), (Explicit, written), (Explicit, yes), (Explicit, no)] <- arguments ->
          (,) <$> forceWith normaliser value <*> forceWith normaliser written >>= \case
            (VLiteral _ actual, VLiteral _ expected) -> Right (if actual == expected then yes else no)
            _ -> stuck
    Just Definition {definitionType, definitionBody = Host key model}
      | Just operation <- pureOperation key,
        Just HostBinding {hostSignature = HostSignature {hostVariables, hostArguments}} <- findForeignBinding key,
        length arguments == length hostVariables + length hostArguments -> do
          inputs <- sequence <$> traverse (uncurry decode) (zip hostArguments (map snd (drop (length hostVariables) arguments)))
          case inputs >>= operation of
            Just result -> do
              annotation <- instantiateLevels levels definitionType >>= evaluateWith normaliser []
              ty <- foldM instantiateProduct annotation arguments
              encode ty result
            -- an input that is not a literal unfoldeth the model, kept glued so
            -- goals still show its name.
            Nothing -> case model of
              Just symbol -> do
                function <- evaluateGlued normaliser [] (Global symbol levels)
                foldM (\value (plicity, argument) -> applyGlued normaliser plicity value argument) function arguments
              Nothing -> stuck
    Just Definition {definitionBody = Eliminator family}
      | Just Definition {definitionUniverses, definitionBody = TypeConstructor info} <- Map.lookup family (normalGlobals normaliser) ->
          eliminate name levels family definitionUniverses info arguments
    _ -> stuck
  _ -> stuck
  where
    stuck = Right (VNeutral neutral)
    -- induction readeth a number literal as its outer constructor.
    literalView = \case
      VLiteral _ literal
        | Just (constructor, fields) <- literalConstructor literal ->
            VNeutral (foldl (\function field -> NApply Explicit function (VLiteral (literalType field) field)) (NGlobal constructor []) fields)
      value -> value
    -- an input computeth only when it is a literal or a list of them.
    decode ty value =
      forceWith normaliser value >>= \case
        VLiteral _ literal -> Right (Just (literalValue literal))
        VNeutral constructed
          | HostApp list [element] <- ty,
            list == listName,
            (NGlobal constructor _, fields) <- neutralSpine constructed ->
              case [field | (Explicit, field) <- fields] of
                []
                  | constructor == coreConstructor emptyConstructorId -> Right (Just (HostList []))
                [first, rest]
                  | constructor == coreConstructor consConstructorId -> do
                      head' <- decode element first
                      tail' <- decode ty rest
                      Right case (head', tail') of
                        (Just value', Just (HostList values)) -> Just (HostList (value' : values))
                        _ -> Nothing
                _ -> Right Nothing
        _ -> Right Nothing
    instantiateProduct ty (plicity, argument) =
      forceWith normaliser ty >>= \case
        VPi expected _ codomain | expected == plicity -> instantiateWith normaliser codomain argument
        _ -> Left "invalid checked host product"
    -- result families retain their checked universes and parameters. field
    -- types come from the instantiated constructor, including nested results.
    encode ty value
      | Just literal <- valueLiteral value =
          forceWith normaliser ty >>= \case
            VNeutral (NGlobal name []) | name == literalType literal -> Right (VLiteral name literal)
            _ -> Left "invalid checked host literal result type"
      | Just (constructor, writtenFields) <- hostConstructor value =
          forceWith normaliser ty >>= \case
            VNeutral neutral
              | (NGlobal family levels, arguments) <- neutralSpine neutral,
                let symbol = coreConstructor constructor,
                Just Definition {definitionType, definitionBody = DataConstructor owner _} <- Map.lookup symbol (normalGlobals normaliser),
                owner == family -> do
                  annotation <- instantiateLevels levels definitionType >>= evaluateWith normaliser []
                  let parameters = [(Implicit, parameter) | (_, parameter) <- arguments]
                  fieldType <- foldM instantiateProduct annotation parameters
                  fields <- encodeFields fieldType writtenFields
                  pure (VNeutral (foldl (\function (plicity, argument) -> NApply plicity function argument) (NGlobal symbol levels) (parameters ++ fields)))
            _ -> Left "invalid checked host result family"
      | otherwise = Left "invalid checked host result value"
    encodeFields ty [] =
      forceWith normaliser ty >>= \case
        VPi {} -> Left "missing checked host result fields"
        _ -> Right []
    encodeFields ty (value : rest) =
      forceWith normaliser ty >>= \case
        VPi plicity domain codomain -> do
          field <- encode domain value
          remaining <- instantiateWith normaliser codomain field
          ((plicity, field) :) <$> encodeFields remaining rest
        _ -> Left "extra checked host result fields"
    hostConstructor = \case
      HostTruth truth -> Just (if truth then yeaConstructorId else nayConstructorId, [])
      HostOption Nothing -> Just (noneConstructorId, [])
      HostOption (Just value) -> Just (someConstructorId, [value])
      HostPair first second -> Just (productConstructorId, [first, second])
      HostList [] -> Just (emptyConstructorId, [])
      HostList (first : rest) -> Just (consConstructorId, [first, HostList rest])
      _ -> Nothing
    eliminate name levels family universes InductiveInfo {..} arguments
      | length arguments /= total = stuck
      | otherwise = do
          scrutinee <- literalView <$> forceWith normaliser (snd (last arguments))
          case scrutinee of
            VNeutral value -> case neutralSpine value of
              (NGlobal constructor constructorLevels, constructorArguments)
                | Just Definition {definitionBody = DataConstructor owner index} <- Map.lookup constructor (normalGlobals normaliser),
                  owner == family,
                  index >= 0,
                  (_, fields) : _ <- drop index inductiveConstructorInfo,
                  length constructorArguments == inductiveParameterCount + length fields -> do
                    let parameters = map snd (take inductiveParameterCount constructorArguments)
                        values = map snd (drop inductiveParameterCount constructorArguments)
                        methods = drop (inductiveParameterCount + 1) arguments
                        method = snd (methods !! index)
                        prefix = take (inductiveParameterCount + 1 + length inductiveConstructorInfo) arguments
                    applyFields name levels universes constructorLevels prefix inductiveParameterCount parameters method (zip fields values)
              _ -> stuck
            _ -> stuck
      where
        total = inductiveParameterCount + 1 + length inductiveConstructorInfo + length inductiveIndexPlicities + 1
    applyFields _ _ _ _ _ _ _ method [] = pure method
    applyFields name levels universes constructorLevels prefix parameterCount preceding method (((plicity, annotation, recursive), value) : rest) = do
      applied <- applyValueWith normaliser plicity method value
      withHypothesis <-
        if recursive
          then do
            fieldType <- instantiateLevels (take universes constructorLevels) annotation
            case termTelescope fieldType of
              ([], _) -> directHypothesis applied fieldType
              (_, _) -> functionHypothesis applied fieldType
          else pure applied
      applyFields name levels universes constructorLevels prefix parameterCount (preceding ++ [value]) withHypothesis rest
      where
        apply function (visibility, argument) = applyValueWith normaliser visibility function argument
        directHypothesis applied fieldType = do
          ty <- evaluateWith normaliser (reverse preceding) fieldType
          indices <- case ty of
            VNeutral field -> case neutralSpine field of
              (NGlobal _ _, arguments) -> pure (drop parameterCount arguments)
              _ -> Left "invalid recursive field metadata"
            _ -> Left "invalid recursive field type"
          induction <- foldM apply (VNeutral (NGlobal name levels)) (prefix ++ indices ++ [(Explicit, value)])
          applyValueWith normaliser Explicit applied induction
        -- for a function field `k`, the hypothesis is `{inputs ^ induction (inputs k)}`,
        -- evaluated with the field, the eliminator prefix, and the earlier fields.
        functionHypothesis applied fieldType = do
          let prefixCount = length prefix
              (inputs, result) = termTelescope (shiftTerm (1 + prefixCount) fieldType)
              inputCount = length inputs
              familyArguments = snd (termSpine result)
              field = applyArguments (Local inputCount) [(visibility, Local (inputCount - position - 1)) | (position, (visibility, _)) <- zip [0 ..] inputs]
              body = applyArguments (Global name levels) ([(visibility, Local (inputCount + 1 + position)) | (position, (visibility, _)) <- zip [0 ..] prefix] ++ drop parameterCount familyArguments ++ [(Explicit, field)])
              hypothesis = foldr (uncurry Lambda) body inputs
          induction <- evaluateWith normaliser (value : map snd prefix ++ reverse preceding) hypothesis
          applyValueWith normaliser Explicit applied induction

neutralSpine :: Neutral -> (Neutral, [(Plicity, Value)])
neutralSpine = go []
  where
    go arguments (NApply plicity function argument) = go ((plicity, argument) : arguments) function
    go arguments headValue = (headValue, arguments)

-- quotation introduceth a fresh neutral for each binder. the depth turneth its
-- stable level back into a de bruijn index; no eta expansion is performed.
quote :: Globals -> Int -> Value -> Either String Term
quote = quoteWith . closed

quoteWith :: Normaliser -> Int -> Value -> Either String Term
quoteWith normaliser = quoteShaped normaliser False (\_ _ _ -> True) (const (pure Nothing)) []

-- quotation that keepeth each folded definition as its name and spine. it
-- denoteth the same value as 'quoteWith' and is smaller; elaboration useth it to
-- build motives, so a branch goal still nameth its definitions.
quoteFoldedWith :: Normaliser -> Int -> Value -> Either String Term
quoteFoldedWith normaliser = quoteShaped normaliser True (\_ _ _ -> False) (const (pure Nothing)) []

-- quotation for goals and messages, as agda simplifieth: a folded definition
-- unfoldeth only when that reacheth a constructor, literal, or record, and a
-- stuck elimination that computeth the same normal form as an enclosing
-- definition applied to the eliminated child is shown as that application, so
-- a goal showeth `rest · l` rather than the eliminator that computeth it.
-- conversion never useth this form.
quoteDisplayWith :: Normaliser -> Int -> Value -> Either String Term
quoteDisplayWith normaliser depth value =
  -- display never faileth where quotation succeedeth.
  either (const (quoteWith normaliser depth value)) Right (quoteShaped normaliser True progress refold [] depth value)
  where
    -- a constructor, literal, record, or variable is progress. a stuck
    -- computation is not, and neither is a type or function, so an alias
    -- such as `α → β` stayeth folded.
    progress _ _ forced = case forced of
      VLiteral {} -> True
      VRecord {} -> True
      VNeutral neutral -> case neutralSpine neutral of
        (NLocal _, _) -> True
        (NGlobal head _, _)
          | Just Definition {definitionBody = DataConstructor {}} <- Map.lookup head (normalGlobals normaliser) -> True
        _ -> False
      _ -> False
    refold (context, currentDepth, neutral) = case neutralSpine neutral of
      (NGlobal eliminator _, arguments)
        | Just Definition {definitionBody = Eliminator family} <- Map.lookup eliminator (normalGlobals normaliser),
          Just Definition {definitionBody = TypeConstructor InductiveInfo {..}} <- Map.lookup family (normalGlobals normaliser),
          let arity = inductiveParameterCount + 1 + length inductiveConstructorInfo + length inductiveIndexPlicities + 1,
          length arguments >= arity -> do
            let (eliminated, extra) = splitAt arity arguments
                (_, child) = last eliminated
            stuck <- eraseGlobalLevels <$> quoteWith normaliser currentDepth (VNeutral neutral)
            -- the child and the extra arguments take the places, and plicities,
            -- of the definition's own inputs.
            let candidates =
                  [ (name, levels, take position spine ++ [(fst (spine !! position), child)] ++ extra)
                  | (name, levels, spine) <- context,
                    position <- [0 .. length spine - 1],
                    length spine == position + 1 + length extra,
                    map fst (drop (position + 1) spine) == map fst extra
                  ]
            firstCandidate stuck currentDepth candidates
      _ -> Right Nothing
    firstCandidate _ _ [] = Right Nothing
    firstCandidate stuck currentDepth ((name, levels, spine) : rest) =
      case candidateNormal currentDepth name levels spine of
        Right normal | normal == stuck -> Right (Just (name, levels, spine))
        _ -> firstCandidate stuck currentDepth rest
    candidateNormal currentDepth name levels spine = do
      folded <- evaluateGlued normaliser [] (Global name levels)
      applied <- foldM (\function (plicity, argument) -> applyGlued normaliser plicity function argument) folded spine
      eraseGlobalLevels <$> quoteWith normaliser currentDepth applied

-- one structural walk for normal, folded, and display quotation. normal
-- quotation also unfoldeth implicit inputs; display never useth it for conversion.
-- `unfold` decideth whether a folded definition is shown by its forced value;
-- `refold` may show
-- a stuck neutral as an enclosing definition's application.
quoteShaped ::
  Normaliser ->
  Bool ->
  ([(SymbolId, [Level], [(Plicity, Value)])] -> Int -> Value -> Bool) ->
  (([(SymbolId, [Level], [(Plicity, Value)])], Int, Neutral) -> Either String (Maybe (SymbolId, [Level], [(Plicity, Value)]))) ->
  [(SymbolId, [Level], [(Plicity, Value)])] ->
  Int ->
  Value ->
  Either String Term
quoteShaped normaliser foldImplicit unfold refold = go
  where
    go context depth value
      | depth < 0 = Left "negative quotation depth"
      | VGlued name levels spine unfolded <- value = do
          forced <- unfolded >>= forceWith normaliser
          let inner = if foldImplicit then (name, levels, spine) : context else []
          if unfold context depth forced
            then go inner depth forced
            else case forced of
              -- a definition that reduced to a stuck call of itself is shown
              -- as that call, so `nil app l` showeth `l`.
              VNeutral neutral ->
                refold (inner, depth, neutral) >>= \case
                  Just (name', levels', spine') -> applied context depth name' levels' spine'
                  Nothing -> applied context depth name levels spine
              _ -> applied context depth name levels spine
      | otherwise =
          forceWith normaliser value >>= \case
            VSort level -> Right (Sort (normaliseLevel level))
            VPi plicity domain codomain -> binder context depth (Pi plicity) domain codomain
            VLambda plicity domain body -> binder context depth (Lambda plicity) domain body
            VNeutral neutral ->
              refold (context, depth, neutral) >>= \case
                Just (name, levels, spine) -> applied context depth name levels spine
                Nothing -> neutralTerm context depth neutral
            VLiteral name literal -> Right (Literal name literal)
            VRecordType fields -> RecordType <$> traverse (\(name, field) -> (name,) <$> go context depth field) fields
            VRecord fields -> Record <$> traverse (\(name, field) -> (name,) <$> go context depth field) fields
            VGlued {} -> Left "a forced value is still folded"
    applied context depth name levels spine =
      foldM (\function (plicity, argument) -> Apply plicity function <$> argumentTerm context depth plicity argument) (Global name (map normaliseLevel levels)) spine
    -- implicit arguments, such as dictionaries, are not shown, so they stay
    -- folded instead of being walked.
    argumentTerm context depth plicity argument = case plicity of
      Implicit | foldImplicit -> quoteFoldedWith normaliser depth argument
      _ -> go context depth argument
    binder context depth constructor domain closure = do
      domainTerm <- go context depth domain
      bodyValue <- instantiateGlued closure (VNeutral (NLocal depth))
      constructor domainTerm <$> go context (depth + 1) bodyValue
    instantiateGlued (Closure environment body) argument = evaluateGlued normaliser (argument : environment) body
    neutralTerm context depth = \case
      NLocal level
        | level < 0 || level >= depth -> Left "neutral local outside quotation scope"
        | otherwise -> Right (Local (depth - level - 1))
      NGlobal name levels -> Right (Global name (map normaliseLevel levels))
      NApply plicity function argument -> Apply plicity <$> neutralTerm context depth function <*> argumentTerm context depth plicity argument
      NMeta identity arguments -> Meta identity <$> traverse (go context depth) arguments
      NProject record name -> (`Project` name) <$> neutralTerm context depth record
      NField index value -> Field index <$> neutralTerm context depth value

normalise :: Globals -> Int -> Term -> Either String Term
normalise globals depth term
  | depth < 0 = Left "negative normalisation depth"
  | otherwise = do
      -- the innermost index denoteth the newest level in the open context.
      let environment = map (VNeutral . NLocal) (reverse [0 .. depth - 1])
      value <- evaluate globals environment term
      quote globals depth value
