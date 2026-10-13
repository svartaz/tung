-- | host bindings in the core. a host declaration bindeth one key of the
-- shared catalogue, 'Tung.Primitive.hostBindings', to a kernel-checked type
-- that matcheth its catalogued signature.
--
-- consistency: the standard model readeth each primitive type as its runtime
-- set, each pure host function as its total definition, and each deed type as
-- a one-element set. host constants therefore cannot inhabit an empty type;
-- `sorry` is the one reported exception. no constant extracteth the result of a
-- deed, and the deed fixed point stayeth opaque. pure host functions compute
-- only on literal arguments.
module Tung.Dependent.Host
  ( defineHost,
    primitiveDefinitions,
    sorrySymbol,
    literalCaseSymbol,
    matchMain,
  )
where

import Control.Monad (foldM, forM_, unless, void, when)
import Data.List (elemIndex, find, sort)
import Data.Map.Strict qualified as Map
import Data.Maybe (isNothing)
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Inductive qualified as I
import Tung.Dependent.Literal (coreConstructor, hostTypeSymbol, literalTypeNames)
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Syntax
import Tung.Identity (ModuleId (..), SymbolId (..), inductionSymbol)
import Tung.Primitive (HostBinding (..), HostDataSchema (..), HostSignature (..), HostType (..), findForeignBinding, hostDataSchemas, integerNegativeId, integerPositiveId, naturalSuccessorId, naturalZeroId, oneName, opaqueTypeFamilyNames, pureOperation)

-- primitive types and `sorry` precede every module. host value types live in
-- the base universe, so literals carry no levels. `sorry` inhabiteth every type;
-- it is the one reported assumption, and running it faileth.
primitiveDefinitions :: Globals
primitiveDefinitions =
  Map.union numberDefinitions . Map.fromList $
    [(SymbolId PrimitiveModule name, Definition 0 [] (Sort LZero) (Host name Nothing)) | name <- literalTypeNames, name `notElem` ["ℕ", "ℤ"]]
      ++ [(SymbolId PrimitiveModule name, Definition 1 [] (Pi Explicit (Sort (LParam 0)) (Sort (LParam 0))) (Host name Nothing)) | name <- opaqueTypeFamilyNames]
      ++ [ (sorrySymbol, Definition 1 [] (Pi Implicit (Sort (LParam 0)) (Local 0)) (Host "sorry" Nothing)),
           -- `[@α: *, @β, x: α, k: α, yes: β, no: β, β]` chooseth `yes` when the
           -- literals `x` and `k` are equal. literal patterns compile to it.
           (literalCaseSymbol, Definition 1 [] literalCaseType (Host "literal_case" Nothing))
         ]
  where
    literalCaseType =
      Pi Implicit (Sort LZero) . Pi Implicit (Sort (LParam 0)) $
        Pi Explicit (Local 1) (Pi Explicit (Local 2) (Pi Explicit (Local 2) (Pi Explicit (Local 3) (Local 4))))

-- `ℕ` is an inductive family with `0` and `heir`, and `ℤ` one with
-- `overnaught` and `heir_undernaught` over `ℕ`. each is checked like any
-- other and eliminated by `unbuild`. literals represent their values; the
-- normaliser and the runner read a literal as its constructors.
numberDefinitions :: Globals
numberDefinitions = family integer [(integerPositiveId, fromNatural), (integerNegativeId, fromNatural)] (family natural [(naturalZeroId, Global natural []), (naturalSuccessorId, Pi Explicit (Global natural []) (Global natural []))] Map.empty)
  where
    natural = SymbolId PrimitiveModule "ℕ"
    integer = SymbolId PrimitiveModule "ℤ"
    fromNatural = Pi Explicit (Global natural []) (Global integer [])
    family name constructors globals =
      case I.inferInductive (K.Environment globals) name (inductionSymbol name) 0 (Sort LZero) constructors [] of
        Right (K.Environment extended) -> extended
        Left message -> error ("invalid primitive " ++ symbolName name ++ ": " ++ message)

sorrySymbol, literalCaseSymbol :: SymbolId
sorrySymbol = SymbolId PrimitiveModule "sorry"
literalCaseSymbol = SymbolId PrimitiveModule "literal_case"

-- a model is a checked tung definition of the same type that conversion
-- unfoldeth when an input is not a literal; the runner keepeth the native
-- operation. only a pure operation can have one.
defineHost :: K.Environment -> SymbolId -> String -> Maybe SymbolId -> K.Inferred -> Either String K.Environment
defineHost environment@(K.Environment globals) name key model signature@K.Inferred {..} = do
  when (Map.member name globals) (Left "duplicate definition")
  HostBinding {hostSignature} <- maybe (Left ("unknown host key '" ++ key ++ "'")) pure (findForeignBinding key)
  when (any (isHost key . definitionBody) (Map.elems globals)) (Left ("host key '" ++ key ++ "' is already bound"))
  K.validate environment signature
  sort <- N.normalise globals 0 inferredType
  case sort of
    Sort _ -> pure ()
    _ -> Left "host annotation is not an ilk"
  -- validation checked the annotation; raw normalisation is now safe.
  ty <- N.normalise globals 0 inferredTerm
  unless (matches hostSignature ty) (Left ("host key '" ++ key ++ "' requireth a different ilk"))
  validateHostData globals hostSignature
  forM_ model \symbol -> do
    when (isNothing (pureOperation key)) (Left ("host key '" ++ key ++ "' is not a pure operation, so it cannot have a model"))
    Definition {definitionUniverses, definitionType, definitionBody} <- maybe (Left "unknown model") pure (Map.lookup symbol globals)
    case definitionBody of
      Transparent _ -> pure ()
      _ -> Left "a model must be a let definition"
    unless (definitionUniverses == inferredUniverses) (Left "a model must have the binding's universe parameters")
    modelType <- N.normalise globals 0 definitionType
    unless (modelType == ty) (Left ("a model must have the binding's ilk"))
  pure (K.Environment (Map.insert name (Definition inferredUniverses inferredConstraints ty (Host key model)) globals))
  where
    isHost wanted (Host actual _) = wanted == actual
    isHost _ _ = False

-- a canonical name alone doth not establish its runtime representation. check
-- the nominal schema and its dependencies before a host can produce values.
-- the visited set stopth recursive schemas, such as list, from looping.
validateHostData :: Globals -> HostSignature -> Either String ()
validateHostData globals HostSignature {..} = void (types Set.empty (hostArguments ++ [hostResult]))
  where
    types = foldM validate
    validate seen = \case
      HostVar _ -> pure seen
      HostCon name -> family seen name
      HostApp name arguments -> family seen name >>= \checked -> types checked arguments
      HostArrow arguments result -> types seen (arguments ++ [result])
    family seen name = case find ((== name) . hostDataType) hostDataSchemas of
      Nothing -> pure seen
      Just _ | Set.member name seen -> pure seen
      Just HostDataSchema {..} -> do
        let invalid = Left ("host data '" ++ name ++ "' requireth its catalogued constructors")
            constructors = [(coreConstructor constructor, signature) | (constructor, signature) <- hostDataConstructors]
        symbol <- maybe invalid pure (hostTypeSymbol name)
        Definition {definitionType, definitionBody} <- maybe invalid pure (Map.lookup symbol globals)
        info <- case definitionBody of
          TypeConstructor info -> pure info
          _ -> invalid
        let actualConstructors = map fst (inductiveConstructorInfo info)
        normal <- N.normalise globals 0 definitionType
        unless
          ( inductiveParameterCount info == length hostDataParameters
              && null (inductiveIndexPlicities info)
              && sort actualConstructors == sort (map fst constructors)
              && parameterKinds (length hostDataParameters) normal
          )
          invalid
        forM_ constructors \(constructor, signature) -> do
          index <- maybe invalid pure (elemIndex constructor actualConstructors)
          Definition {definitionType, definitionBody} <- maybe invalid pure (Map.lookup constructor globals)
          case definitionBody of
            DataConstructor owner position | owner == symbol && position == index -> pure ()
            _ -> invalid
          normal <- N.normalise globals 0 definitionType
          unless (matches signature normal) invalid
        types (Set.insert name seen) (concatMap (\(_, HostSignature {..}) -> hostArguments ++ [hostResult]) constructors)
    parameterKinds 0 (Sort _) = True
    parameterKinds count (Pi Explicit (Sort _) result) | count > 0 = parameterKinds (count - 1) result
    parameterKinds _ _ = False

-- main must be a deed of the bookhoard unit type.
matchMain :: Globals -> Term -> Either String ()
matchMain globals ty = do
  normal <- N.normalise globals 0 ty
  unless (matches (HostSignature [] [] (HostApp "deed" [HostCon oneName])) normal) (Left "main requireth a unit deed ilk")

-- a normal type matcheth a signature when its implicit type inputs, explicit
-- inputs, and result agree. data types match by declaration; universe levels
-- are not constrained, as the model existeth at every universe.
matches :: HostSignature -> Term -> Bool
matches HostSignature {..} = quantified [] hostVariables
  where
    quantified bound (variable : rest) (Pi Implicit (Sort _) body) = quantified (variable : bound) rest body
    quantified bound [] ty = function bound 0 hostArguments hostResult ty
    quantified _ _ _ = False
    -- explicit inputs are unnamed: no later type dependeth on them.
    function bound depth (argument : rest) result (Pi Explicit domain codomain) =
      hostType bound depth argument domain && function bound (depth + 1) rest result codomain
    function bound depth [] result ty = hostType bound depth result ty
    function _ _ _ _ _ = False
    hostType bound depth expected actual = case expected of
      HostVar variable | Local index <- actual -> fmap (+ depth) (elemIndex variable bound) == Just index
      HostCon typeName | Global symbol _ <- actual -> hostTypeSymbol typeName == Just symbol
      HostApp typeName arguments
        | (Global symbol _, actuals) <- spine actual [],
          length arguments == length actuals ->
            hostTypeSymbol typeName == Just symbol && and (zipWith (hostType bound depth) arguments actuals)
      HostArrow arguments result -> function bound depth arguments result actual
      _ -> False
    spine (Apply Explicit function argument) arguments = spine function (argument : arguments)
    spine term arguments = (term, arguments)
