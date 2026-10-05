-- | normalisation by evaluation for the checked dependent core. evaluation
-- assumeþ well-typed terms and acyclic globals; it is not a termination checker.
module Tung.Dependent.Normalise
  ( Value (..),
    Closure (..),
    Neutral (..),
    neutralSpine,
    evaluate,
    instantiate,
    applyValue,
    quote,
    normalise,
    MetaResolver,
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
import Tung.Dependent.Literal (coreConstructor, literalType, literalValue, valueLiteral)
import Tung.Dependent.Syntax
import Tung.Dependent.Universe (normaliseLevel)
import Tung.Identity (ModuleId (..), SymbolId (..))
import Tung.Primitive (HostBinding (..), HostSignature (..), HostType (..), HostValue (..), consConstructorId, emptyConstructorId, findForeignBinding, listName, naturalSuccessorId, naturalZeroId, nayConstructorId, noneConstructorId, productConstructorId, pureOperation, someConstructorId, yeaConstructorId)

data Value
  = VSort Level
  | VPi Plicity Value Closure
  | VLambda Plicity Value Closure
  | VNeutral Neutral
  | VLiteral SymbolId HostLiteral
  | VRecordType [(String, Value)]
  | VRecord [(String, Value)]
  | -- a transparent global applied to its spine, wiþ its unfolding computed
    -- only when forced. evaluation keepeþ definitions folded in nested
    -- positions; every public evaluation result is forced at its head.
    VGlued SymbolId [Level] [(Plicity, Value)] (Either String Value)
  deriving stock (Show)

data Closure = Closure [Value] Term
  deriving stock (Show)

-- neutral locals use levels, so extending a context requireþ no shifting.
-- neutral applications inherit their plicity check from the core checker.
data Neutral
  = NLocal Int
  | NGlobal SymbolId [Level]
  | NApply Plicity Neutral Value
  | NMeta Int [Value]
  | NProject Neutral String
  deriving stock (Show)

-- closures contain syntax and values, never a snapshot of the solution store.
-- elaboration supplieþ the current resolver at every evaluation or quotation.
type MetaResolver = Int -> Either String (Maybe Term)

rejectMeta :: MetaResolver
rejectMeta _ = Left "unresolved term inference hole in core"

evaluate :: Globals -> [Value] -> Term -> Either String Value
evaluate = evaluateWith rejectMeta

-- þe result is forced at its head, so callers see þe same values as before
-- definitions were glued; nested positions may stay folded.
evaluateWith :: MetaResolver -> Globals -> [Value] -> Term -> Either String Value
evaluateWith resolver globals environment term =
  evaluateGlued resolver globals environment term >>= forceWith resolver globals

evaluateGlued :: MetaResolver -> Globals -> [Value] -> Term -> Either String Value
evaluateGlued resolver globals environment = \case
  Local index
    | index < 0 -> Left "negative local index"
    | otherwise -> case drop index environment of
        value : _ -> Right value
        [] -> Left "unbound local index"
  Global name levels -> case Map.lookup name globals of
    Nothing -> Left ("unknown global " ++ show name)
    Just definition
      | length levels /= definitionUniverses definition ->
          Left "wrong number of universe arguments"
      | otherwise -> case definitionBody definition of
          Transparent term ->
            -- global bodies are closed; the caller's local environment is irrelevant.
            Right (VGlued name (map normaliseLevel levels) [] (instantiateLevels (map normaliseLevel levels) term >>= evaluateWith resolver globals []))
          _
            | name == naturalZeroId -> Right (VLiteral naturalType (NaturalValue 0))
            | otherwise -> Right (VNeutral (NGlobal name (map normaliseLevel levels)))
  Sort level -> Right (VSort (normaliseLevel level))
  Pi plicity domain codomain -> do
    domainValue <- evaluateWith resolver globals environment domain
    pure (VPi plicity domainValue (Closure environment codomain))
  Lambda plicity domain body -> do
    domainValue <- evaluateWith resolver globals environment domain
    pure (VLambda plicity domainValue (Closure environment body))
  Apply plicity function argument -> do
    functionValue <- evaluateGlued resolver globals environment function
    argumentValue <- evaluateGlued resolver globals environment argument
    applyGlued resolver globals plicity functionValue argumentValue
  Let _ value body -> do
    valueValue <- evaluateGlued resolver globals environment value
    evaluateGlued resolver globals (valueValue : environment) body
  Meta identity arguments -> do
    values <- traverse (evaluateGlued resolver globals environment) arguments
    forceWith resolver globals (VNeutral (NMeta identity values))
  Literal name value -> Right (VLiteral name value)
  RecordType fields -> VRecordType <$> traverse (\(name, field) -> (name,) <$> evaluateGlued resolver globals environment field) fields
  Record fields -> VRecord <$> traverse (\(name, field) -> (name,) <$> evaluateGlued resolver globals environment field) fields
  Project record name -> evaluateGlued resolver globals environment record >>= project resolver globals name

-- applying a folded definition extendeþ its spine; its unfolding followeþ
-- lazily.
applyGlued :: MetaResolver -> Globals -> Plicity -> Value -> Value -> Either String Value
applyGlued resolver globals plicity function argument = case function of
  VGlued name levels spine unfolded ->
    Right (VGlued name levels (spine ++ [(plicity, argument)]) (unfolded >>= \value -> applyValueWith resolver globals plicity value argument))
  _ -> applyValueWith resolver globals plicity function argument

instantiate :: Globals -> Closure -> Value -> Either String Value
instantiate = instantiateWith rejectMeta

instantiateWith :: MetaResolver -> Globals -> Closure -> Value -> Either String Value
instantiateWith resolver globals (Closure environment body) argument =
  evaluateWith resolver globals (argument : environment) body

applyValue :: Globals -> Plicity -> Value -> Value -> Either String Value
applyValue = applyValueWith rejectMeta

applyValueWith :: MetaResolver -> Globals -> Plicity -> Value -> Value -> Either String Value
applyValueWith resolver globals plicity function argument =
  forceWith resolver globals function >>= \case
    VLambda expected _ closure
      | plicity == expected -> instantiateWith resolver globals closure argument
      | otherwise -> Left "application plicity differeþ from function plicity"
    VNeutral neutral -> reduceNeutral resolver globals (NApply plicity neutral argument)
    _ -> Left "application of a non-function"

-- a neutral saved in an older closure may have since acquired a solution.
-- forcing its head also resumeþ applications blocked on that metavariable.
forceWith :: MetaResolver -> Globals -> Value -> Either String Value
forceWith resolver globals = \case
  VGlued _ _ _ unfolded -> unfolded >>= forceWith resolver globals
  VNeutral (NMeta identity arguments) ->
    resolver identity >>= \case
      Nothing -> Right (VNeutral (NMeta identity arguments))
      Just solution -> do
        function <- evaluateWith resolver globals [] solution
        foldM (applyValueWith resolver globals Explicit) function arguments
  VNeutral (NApply plicity function argument) -> do
    headValue <- forceWith resolver globals (VNeutral function)
    case headValue of
      VNeutral neutral -> reduceNeutral resolver globals (NApply plicity neutral argument)
      _ -> applyValueWith resolver globals plicity headValue argument
  VNeutral (NProject record name) -> project resolver globals name (VNeutral record)
  value -> Right value

-- a projection reduceþ on a record value and stayeþ neutral on a variable.
project :: MetaResolver -> Globals -> String -> Value -> Either String Value
project resolver globals name record =
  forceWith resolver globals record >>= \case
    VRecord fields -> maybe (Left ("record hath no field '" ++ name ++ "'")) Right (lookup name fields)
    VNeutral neutral -> Right (VNeutral (NProject neutral name))
    _ -> Left "projection from a non-record"

naturalType :: SymbolId
naturalType = SymbolId PrimitiveModule "ℕ"

-- induction reduceþ only on constructors. recursive calls use direct children,
-- never an arbitrary source function or a user-supplied recursion annotation.
reduceNeutral :: MetaResolver -> Globals -> Neutral -> Either String Value
reduceNeutral resolver globals neutral = case neutralSpine neutral of
  -- þe successor of a literal is a literal.
  (NGlobal name _, [(Explicit, argument)])
    | name == naturalSuccessorId ->
        forceWith resolver globals argument >>= \case
          VLiteral _ (NaturalValue value) -> Right (VLiteral naturalType (NaturalValue (value + 1)))
          _ -> stuck
  -- þe head is looked up once; identity comparison is a hot path.
  (NGlobal name levels, arguments) -> case Map.lookup name globals of
    -- a literal case chooseþ once boþ compared values are literals.
    Just Definition {definitionBody = Host "literal_case"}
      | [_, _, (Explicit, value), (Explicit, written), (Explicit, yes), (Explicit, no)] <- arguments ->
          (,) <$> forceWith resolver globals value <*> forceWith resolver globals written >>= \case
            (VLiteral _ actual, VLiteral _ expected) -> Right (if actual == expected then yes else no)
            _ -> stuck
    Just Definition {definitionType, definitionBody = Host key}
      | Just operation <- pureOperation key,
        Just HostBinding {hostSignature = HostSignature {hostVariables, hostArguments}} <- findForeignBinding key,
        length arguments == length hostVariables + length hostArguments -> do
          inputs <- sequence <$> traverse (uncurry decode) (zip hostArguments (map snd (drop (length hostVariables) arguments)))
          case inputs >>= operation of
            Just result -> do
              annotation <- instantiateLevels levels definitionType >>= evaluateWith resolver globals []
              ty <- foldM instantiateProduct annotation arguments
              encode ty result
            Nothing -> stuck
    Just Definition {definitionBody = Eliminator family}
      | Just Definition {definitionUniverses, definitionBody = TypeConstructor info} <- Map.lookup family globals ->
          eliminate name levels family definitionUniverses info arguments
    _ -> stuck
  _ -> stuck
  where
    stuck = Right (VNeutral neutral)
    -- induction readeþ a literal natural as `0` or þe successor of its
    -- predecessor.
    naturalView = \case
      VLiteral _ (NaturalValue 0) -> VNeutral (NGlobal naturalZeroId [])
      VLiteral _ (NaturalValue value) -> VNeutral (NApply Explicit (NGlobal naturalSuccessorId []) (VLiteral naturalType (NaturalValue (value - 1))))
      value -> value
    -- an input computeþ only when it is a literal or a list of þem.
    decode ty value =
      forceWith resolver globals value >>= \case
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
      forceWith resolver globals ty >>= \case
        VPi expected _ codomain | expected == plicity -> instantiateWith resolver globals codomain argument
        _ -> Left "invalid checked host product"
    -- result families retain their checked universes and parameters. field
    -- types come from þe instantiated constructor, including nested results.
    encode ty value
      | Just literal <- valueLiteral value =
          forceWith resolver globals ty >>= \case
            VNeutral (NGlobal name []) | name == literalType literal -> Right (VLiteral name literal)
            _ -> Left "invalid checked host literal result type"
      | Just (constructor, writtenFields) <- hostConstructor value =
          forceWith resolver globals ty >>= \case
            VNeutral neutral
              | (NGlobal family levels, arguments) <- neutralSpine neutral,
                let symbol = coreConstructor constructor,
                Just Definition {definitionType, definitionBody = DataConstructor owner _} <- Map.lookup symbol globals,
                owner == family -> do
                  annotation <- instantiateLevels levels definitionType >>= evaluateWith resolver globals []
                  let parameters = [(Implicit, parameter) | (_, parameter) <- arguments]
                  fieldType <- foldM instantiateProduct annotation parameters
                  fields <- encodeFields fieldType writtenFields
                  pure (VNeutral (foldl (\function (plicity, argument) -> NApply plicity function argument) (NGlobal symbol levels) (parameters ++ fields)))
            _ -> Left "invalid checked host result family"
      | otherwise = Left "invalid checked host result value"
    encodeFields ty [] =
      forceWith resolver globals ty >>= \case
        VPi {} -> Left "missing checked host result fields"
        _ -> Right []
    encodeFields ty (value : rest) =
      forceWith resolver globals ty >>= \case
        VPi plicity domain codomain -> do
          field <- encode domain value
          remaining <- instantiateWith resolver globals codomain field
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
          scrutinee <- naturalView <$> forceWith resolver globals (snd (last arguments))
          case scrutinee of
            VNeutral value -> case neutralSpine value of
              (NGlobal constructor constructorLevels, constructorArguments)
                | Just Definition {definitionBody = DataConstructor owner index} <- Map.lookup constructor globals,
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
      applied <- applyValueWith resolver globals plicity method value
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
        apply function (visibility, argument) = applyValueWith resolver globals visibility function argument
        directHypothesis applied fieldType = do
          ty <- evaluateWith resolver globals (reverse preceding) fieldType
          indices <- case ty of
            VNeutral field -> case neutralSpine field of
              (NGlobal _ _, arguments) -> pure (drop parameterCount arguments)
              _ -> Left "invalid recursive field metadata"
            _ -> Left "invalid recursive field type"
          induction <- foldM apply (VNeutral (NGlobal name levels)) (prefix ++ indices ++ [(Explicit, value)])
          applyValueWith resolver globals Explicit applied induction
        -- for a function field `k`, þe hypothesis is `{inputs ^ induction (inputs k)}`,
        -- evaluated wiþ þe field, þe eliminator prefix, and þe earlier fields.
        functionHypothesis applied fieldType = do
          let prefixCount = length prefix
              (inputs, result) = termTelescope (shiftTerm (1 + prefixCount) fieldType)
              inputCount = length inputs
              familyArguments = snd (termSpine result)
              field = applyArguments (Local inputCount) [(visibility, Local (inputCount - position - 1)) | (position, (visibility, _)) <- zip [0 ..] inputs]
              body = applyArguments (Global name levels) ([(visibility, Local (inputCount + 1 + position)) | (position, (visibility, _)) <- zip [0 ..] prefix] ++ drop parameterCount familyArguments ++ [(Explicit, field)])
              hypothesis = foldr (uncurry Lambda) body inputs
          induction <- evaluateWith resolver globals (value : map snd prefix ++ reverse preceding) hypothesis
          applyValueWith resolver globals Explicit applied induction

neutralSpine :: Neutral -> (Neutral, [(Plicity, Value)])
neutralSpine = go []
  where
    go arguments (NApply plicity function argument) = go ((plicity, argument) : arguments) function
    go arguments headValue = (headValue, arguments)

-- quotation introduceþ a fresh neutral for each binder. the depth turneþ its
-- stable level back into a de bruijn index; no eta expansion is performed.
quote :: Globals -> Int -> Value -> Either String Term
quote = quoteWith rejectMeta

quoteWith :: MetaResolver -> Globals -> Int -> Value -> Either String Term
quoteWith resolver globals depth value
  | depth < 0 = Left "negative quotation depth"
  | otherwise =
      forceWith resolver globals value >>= \case
        VSort level -> Right (Sort (normaliseLevel level))
        VPi plicity domain codomain -> quoteBinder (Pi plicity) domain codomain
        VLambda plicity domain body -> quoteBinder (Lambda plicity) domain body
        VNeutral neutral -> quoteNeutral neutral
        VLiteral name value -> Right (Literal name value)
        VRecordType fields -> RecordType <$> traverse (\(name, field) -> (name,) <$> quoteWith resolver globals depth field) fields
        VRecord fields -> Record <$> traverse (\(name, field) -> (name,) <$> quoteWith resolver globals depth field) fields
        VGlued {} -> Left "a forced value is still folded"
  where
    quoteBinder constructor domain closure = do
      domainTerm <- quoteWith resolver globals depth domain
      bodyValue <- instantiateWith resolver globals closure (VNeutral (NLocal depth))
      bodyTerm <- quoteWith resolver globals (depth + 1) bodyValue
      pure (constructor domainTerm bodyTerm)
    quoteNeutral = \case
      NLocal level
        | level < 0 || level >= depth -> Left "neutral local outside quotation scope"
        | otherwise -> Right (Local (depth - level - 1))
      NGlobal name levels -> Right (Global name (map normaliseLevel levels))
      NApply plicity function argument ->
        Apply plicity <$> quoteNeutral function <*> quoteWith resolver globals depth argument
      NMeta identity arguments -> Meta identity <$> traverse (quoteWith resolver globals depth) arguments
      NProject record name -> (`Project` name) <$> quoteNeutral record

-- quotation þat keepeþ each folded definition as its name and spine. it
-- denoteþ þe same value as 'quoteWith' and is smaller; elaboration useþ it to
-- build motives, so a branch goal still nameþ its definitions.
quoteFoldedWith :: MetaResolver -> Globals -> Int -> Value -> Either String Term
quoteFoldedWith resolver globals = quoteShaped resolver globals (\_ _ _ -> False) (const (pure Nothing)) []

-- quotation for goals and messages, as agda simplifieþ: a folded definition
-- unfoldeþ only when þat reacheþ a constructor, literal, or record, and a
-- stuck elimination þat computeþ þe same normal form as an enclosing
-- definition applied to þe eliminated child is shown as þat application, so
-- a goal showeþ `rest · l` raþer þan þe eliminator þat computeþ it.
-- conversion never useþ þis form.
quoteDisplayWith :: MetaResolver -> Globals -> Int -> Value -> Either String Term
quoteDisplayWith resolver globals depth value =
  -- display never faileþ where quotation succeedeþ.
  either (const (quoteWith resolver globals depth value)) Right (quoteShaped resolver globals progress refold [] depth value)
  where
    -- a constructor, literal, record, or variable is progress. a stuck
    -- computation is not, and neiþer is a type or function, so an alias
    -- such as `α → β` stayeþ folded.
    progress _ _ forced = case forced of
      VLiteral {} -> True
      VRecord {} -> True
      VNeutral neutral -> case neutralSpine neutral of
        (NLocal _, _) -> True
        (NGlobal head _, _)
          | Just Definition {definitionBody = DataConstructor {}} <- Map.lookup head globals -> True
        _ -> False
      _ -> False
    refold (context, currentDepth, neutral) = case neutralSpine neutral of
      (NGlobal eliminator _, arguments)
        | Just Definition {definitionBody = Eliminator family} <- Map.lookup eliminator globals,
          Just Definition {definitionBody = TypeConstructor InductiveInfo {..}} <- Map.lookup family globals,
          let arity = inductiveParameterCount + 1 + length inductiveConstructorInfo + length inductiveIndexPlicities + 1,
          length arguments >= arity -> do
            let (eliminated, extra) = splitAt arity arguments
                (_, child) = last eliminated
            stuck <- eraseGlobalLevels <$> quoteWith resolver globals currentDepth (VNeutral neutral)
            -- þe child and þe extra arguments take þe places, and plicities,
            -- of þe definition's own inputs.
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
      folded <- evaluateGlued resolver globals [] (Global name levels)
      applied <- foldM (\function (plicity, argument) -> applyGlued resolver globals plicity function argument) folded spine
      eraseGlobalLevels <$> quoteWith resolver globals currentDepth applied

-- þe shared walk of þe folded and display quotations. `unfold` decideþ
-- wheþer a folded definition is shown by its forced value; `refold` may show
-- a stuck neutral as an enclosing definition's application.
quoteShaped ::
  MetaResolver ->
  Globals ->
  ([(SymbolId, [Level], [(Plicity, Value)])] -> Int -> Value -> Bool) ->
  (([(SymbolId, [Level], [(Plicity, Value)])], Int, Neutral) -> Either String (Maybe (SymbolId, [Level], [(Plicity, Value)]))) ->
  [(SymbolId, [Level], [(Plicity, Value)])] ->
  Int ->
  Value ->
  Either String Term
quoteShaped resolver globals unfold refold = go
  where
    go context depth value
      | depth < 0 = Left "negative quotation depth"
      | VGlued name levels spine unfolded <- value = do
          forced <- unfolded >>= forceWith resolver globals
          let inner = (name, levels, spine) : context
          if unfold context depth forced
            then go inner depth forced
            else case forced of
              -- a definition þat reduced to a stuck call of itself is shown
              -- as þat call, so `nil app l` showeþ `l`.
              VNeutral neutral ->
                refold (inner, depth, neutral) >>= \case
                  Just (name', levels', spine') -> applied context depth name' levels' spine'
                  Nothing -> applied context depth name levels spine
              _ -> applied context depth name levels spine
      | otherwise =
          forceWith resolver globals value >>= \case
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
    -- implicit arguments, such as dictionaries, are not shown, so þey stay
    -- folded instead of being walked.
    argumentTerm context depth plicity argument = case plicity of
      Implicit -> quoteShaped resolver globals (\_ _ _ -> False) (const (pure Nothing)) [] depth argument
      Explicit -> go context depth argument
    binder context depth constructor domain closure = do
      domainTerm <- go context depth domain
      bodyValue <- instantiateGlued closure (VNeutral (NLocal depth))
      constructor domainTerm <$> go context (depth + 1) bodyValue
    instantiateGlued (Closure environment body) argument = evaluateGlued resolver globals (argument : environment) body
    neutralTerm context depth = \case
      NLocal level
        | level < 0 || level >= depth -> Left "neutral local outside quotation scope"
        | otherwise -> Right (Local (depth - level - 1))
      NGlobal name levels -> Right (Global name (map normaliseLevel levels))
      NApply plicity function argument -> Apply plicity <$> neutralTerm context depth function <*> argumentTerm context depth plicity argument
      NMeta identity arguments -> Meta identity <$> traverse (go context depth) arguments
      NProject record name -> (`Project` name) <$> neutralTerm context depth record

normalise :: Globals -> Int -> Term -> Either String Term
normalise globals depth term
  | depth < 0 = Left "negative normalisation depth"
  | otherwise = do
      -- the innermost index denoteþ the newest level in the open context.
      let environment = map (VNeutral . NLocal) (reverse [0 .. depth - 1])
      value <- evaluate globals environment term
      quote globals depth value
