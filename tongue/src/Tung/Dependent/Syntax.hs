-- | explicit dependent terms. local variables use de bruijn indices; universe
-- parameters and inference holes are distinct from term variables.
module Tung.Dependent.Syntax
  ( Level (..),
    Constraint (..),
    Plicity (..),
    Term (..),
    HostLiteral (..),
    Definition (..),
    DefinitionBody (..),
    InductiveInfo (..),
    inductiveInfo,
    inductiveMethods,
    Globals,
    children,
    mapChildren,
    mapDefinitionSymbols,
    traverseScoped,
    mapLevels,
    instantiateLevel,
    instantiateLevels,
    termLevels,
    constraintLevels,
    eraseGlobalLevels,
    sameUpToLevels,
    abstractTerms,
    freeIndices,
    termTelescope,
    termSpine,
    applyArguments,
    shiftTerm,
  )
where

import Data.Functor.Const (Const (..))
import Data.Functor.Identity (Identity (..))
import Data.List (findIndex)
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Tung.Dependent.Literal (HostLiteral (..))
import Tung.Identity (SymbolId)

data Level
  = LZero
  | LParam Int
  | LMeta Int
  | LSucc Level
  | LMax Level Level
  deriving stock (Eq, Ord, Show)

data Constraint = LevelEqual Level Level | LevelBelow Level Level
  deriving stock (Eq, Ord, Show)

data Plicity = Explicit | Implicit
  deriving stock (Eq, Ord, Show)

-- both types and values use this syntax. binder names are absent from identity.
-- term metas are temporary elaboration syntax; the kernel rejecteth every one.
data Term
  = Local Int
  | Global SymbolId [Level]
  | Sort Level
  | Pi Plicity Term Term
  | Lambda Plicity Term Term
  | Apply Plicity Term Term
  | Let Term Term Term
  | Meta Int [Term]
  | -- a literal nameth the host value type it inhabiteth. host value types
    -- have no universe parameters.
    Literal SymbolId HostLiteral
  | -- closed records. field names are distinct and sorted, so field order
    -- in source never affecteth identity.
    RecordType [(String, Term)]
  | Record [(String, Term)]
  | Project Term String
  | -- the field at an index of a value of a one-constructor family without
    -- indices, counting implicit fields, as lean's primitive projections.
    Field Int Term
  deriving stock (Eq, Show)

data Definition = Definition
  { definitionUniverses :: Int,
    definitionConstraints :: [Constraint],
    definitionType :: Term,
    definitionBody :: DefinitionBody
  }
  deriving stock (Eq, Show)

-- primitive constants are introduced together by checked inductive declarations.
-- constructor field types are scoped over parameters and preceding fields.
data DefinitionBody
  = Transparent Term
  | TypeConstructor InductiveInfo
  | -- a private nested-induction target. its checked alias body retaineth
    -- the ordinary container type; metadata giveth its specialised recursor.
    EliminationTarget InductiveInfo Term
  | DataConstructor SymbolId Int
  | Eliminator SymbolId
  | -- a trusted host constant, bound to a catalogue key. a pure operation
    -- reduceth on literal inputs. on other inputs it unfoldeth its model, a
    -- checked tung definition of the same type, when it hath one; any other
    -- host constant is opaque.
    Host String (Maybe SymbolId)
  | -- an `orsetting` assumption: a constant with a checked type and no body.
    Assumption
  deriving stock (Eq, Show)

-- group order fixeth the shared recursor prefix; constructors remain per-family.
-- a recursive field endeth in any group member, directly or after function inputs.
data InductiveInfo = InductiveInfo
  { inductiveFamilies :: [SymbolId],
    inductiveParameterCount :: Int,
    inductiveConstructorParameterCount :: Int,
    inductiveIndexPlicities :: [Plicity],
    inductiveConstructorInfo :: [(SymbolId, [(Plicity, Term, Maybe SymbolId)])],
    -- each checked rule is scoped over the common recursor prefix followed
    -- by its constructor's fields. both evaluators execute these terms.
    inductiveRules :: [Term]
  }
  deriving stock (Eq, Show)

type Globals = Map.Map SymbolId Definition

-- every recursor in a mutual group taketh the same ordered method prefix.
inductiveInfo :: Globals -> SymbolId -> Either String InductiveInfo
inductiveInfo globals family = case definitionBody <$> Map.lookup family globals of
  Just (TypeConstructor info) -> pure info
  Just (EliminationTarget info _) -> pure info
  _ -> Left "missing inductive group member"

inductiveMethods :: Globals -> InductiveInfo -> Either String [(SymbolId, [(Plicity, Term, Maybe SymbolId)])]
inductiveMethods _ InductiveInfo {inductiveFamilies = [_], inductiveConstructorInfo} = pure inductiveConstructorInfo
inductiveMethods globals info = concat <$> traverse methods (inductiveFamilies info)
  where
    methods family = inductiveConstructorInfo <$> inductiveInfo globals family

mapSymbols :: (SymbolId -> SymbolId) -> Term -> Term
mapSymbols f = runIdentity . traverseScoped visit
  where
    visit _ (Global symbol levels) _ = pure (Global (f symbol) levels)
    visit _ (Literal symbol value) _ = pure (Literal (f symbol) value)
    visit _ _ descend = descend

-- metadata carrieth identities too, including recursive field annotations
-- and a host binding's structural model.
mapDefinitionSymbols :: (SymbolId -> SymbolId) -> Definition -> Definition
mapDefinitionSymbols f definition@Definition {definitionType, definitionBody} =
  definition {definitionType = mapSymbols f definitionType, definitionBody = body definitionBody}
  where
    body = \case
      Transparent term -> Transparent (mapSymbols f term)
      TypeConstructor info -> TypeConstructor (metadata info)
      EliminationTarget info term -> EliminationTarget (metadata info) (mapSymbols f term)
      DataConstructor family index -> DataConstructor (f family) index
      Eliminator family -> Eliminator (f family)
      Host key model -> Host key (f <$> model)
      Assumption -> Assumption
    metadata info@InductiveInfo {inductiveFamilies, inductiveConstructorInfo, inductiveRules} =
      info
        { inductiveFamilies = map f inductiveFamilies,
          inductiveConstructorInfo = [(f symbol, [(plicity, mapSymbols f ty, f <$> recursive) | (plicity, ty, recursive) <- fields]) | (symbol, fields) <- inductiveConstructorInfo],
          inductiveRules = map (mapSymbols f) inductiveRules
        }

-- product domains retain their original scope over preceding binders.
termTelescope :: Term -> ([(Plicity, Term)], Term)
termTelescope = \case
  Pi plicity domain codomain -> let (rest, result) = termTelescope codomain in ((plicity, domain) : rest, result)
  term -> ([], term)

-- application inputs stay in written order, with their original plicities.
termSpine :: Term -> (Term, [(Plicity, Term)])
termSpine = go []
  where
    go arguments (Apply plicity function argument) = go ((plicity, argument) : arguments) function
    go arguments headTerm = (headTerm, arguments)

applyArguments :: Term -> [(Plicity, Term)] -> Term
applyArguments = foldl (\function (plicity, argument) -> Apply plicity function argument)

-- free locals move past the given number of new outer binders.
shiftTerm :: Int -> Term -> Term
shiftTerm amount = runIdentity . traverseScoped move
  where
    move bound (Local index) _ | index >= bound = pure (Local (index + amount))
    move _ _ descend = descend

-- | each immediate subterm, in order, with the number of binders between it
-- and its parent. every term traversal is built from these two functions.
children :: Term -> [(Int, Term)]
children = getConst . mapChildren (\binders child -> Const [(binders, child)])

mapChildren :: (Applicative f) => (Int -> Term -> f Term) -> Term -> f Term
mapChildren f = \case
  Pi plicity domain codomain -> Pi plicity <$> f 0 domain <*> f 1 codomain
  Lambda plicity domain body -> Lambda plicity <$> f 0 domain <*> f 1 body
  Apply plicity function argument -> Apply plicity <$> f 0 function <*> f 0 argument
  Let annotation value body -> Let <$> f 0 annotation <*> f 0 value <*> f 1 body
  Meta identity arguments -> Meta identity <$> traverse (f 0) arguments
  RecordType fields -> RecordType <$> traverse (\(name, field) -> (name,) <$> f 0 field) fields
  Record fields -> Record <$> traverse (\(name, field) -> (name,) <$> f 0 field) fields
  Project record name -> (`Project` name) <$> f 0 record
  Field index value -> Field index <$> f 0 value
  term@Local {} -> pure term
  term@Global {} -> pure term
  term@Sort {} -> pure term
  term@Literal {} -> pure term

-- visit a node before its children, carrying the number of enclosing binders.
-- use the lazy default descent at most once; replacements are not revisited.
-- this walk tracketh depth but doth not validate local indices.
traverseScoped :: (Applicative f) => (Int -> Term -> f Term -> f Term) -> Term -> f Term
traverseScoped visit = go 0
  where
    go bound term = visit bound term (mapChildren (\binders -> go (bound + binders)) term)

traverseLevels :: (Applicative f) => (Level -> f Level) -> Term -> f Term
traverseLevels f = traverseScoped visit
  where
    visit _ (Global name levels) _ = Global name <$> traverse f levels
    visit _ (Sort level) _ = Sort <$> f level
    visit _ _ descend = descend

mapLevels :: (Level -> Level) -> Term -> Term
mapLevels f = runIdentity . traverseLevels (Identity . f)

-- template holes are forbidden; supplied levels remain untouched, including
-- inference holes introduced by a caller.
-- the arguments are indexed once, so a partial application shareth them.
instantiateLevel :: [Level] -> Level -> Either String Level
instantiateLevel arguments = go
  where
    indexed = Seq.fromList arguments
    go = \case
      LParam index -> maybe (Left "unbound universe parameter") Right (Seq.lookup index indexed)
      LMeta _ -> Left "unresolved universe inference hole"
      LSucc level -> LSucc <$> go level
      LMax left right -> LMax <$> go left <*> go right
      LZero -> Right LZero

instantiateLevels :: [Level] -> Term -> Either String Term
instantiateLevels arguments = traverseLevels (instantiateLevel arguments)

termLevels :: Term -> [Level]
termLevels = getConst . traverseLevels (\level -> Const [level])

constraintLevels :: Constraint -> [Level]
constraintLevels (LevelEqual left right) = [left, right]
constraintLevels (LevelBelow left right) = [left, right]

-- search keys ignore global instantiations, but retain written sort levels.
eraseGlobalLevels :: Term -> Term
eraseGlobalLevels = runIdentity . traverseScoped erase
  where
    erase _ (Global name _) _ = pure (Global name [])
    erase _ _ descend = descend

-- equality that ignoreth global universe instantiations, as
-- 'eraseGlobalLevels' doth, without rebuilding either term.
sameUpToLevels :: Term -> Term -> Bool
sameUpToLevels left right = case (left, right) of
  (Global name _, Global other _) -> name == other
  _ -> blank left == blank right && and (zipWith (\(_, first) (_, second) -> sameUpToLevels first second) (children left) (children right))
  where
    blank = runIdentity . mapChildren (\_ _ -> Identity (Sort LZero))

-- replaceth each occurrence of the given terms, up to global universe levels,
-- with new innermost inputs, the first term outermost. the result liveth that
-- many binders deeper; the flags tell which terms occurred.
abstractTerms :: [Term] -> Term -> (Term, [Bool])
abstractTerms targets body = (abstracted, [position `elem` found | position <- [0 .. count - 1]])
  where
    count = length targets
    shifted = [map (shiftTerm (bound + count)) targets | bound <- [0 :: Int ..]]
    (found, abstracted) = traverseScoped replace (shiftTerm count body)
    replace bound term descend = case findIndex (sameUpToLevels term) (shifted !! bound) of
      Just position -> ([position], Local (bound + count - 1 - position))
      Nothing -> descend

-- free de bruijn indices, measured outside the term's own binders.
freeIndices :: Term -> [Int]
freeIndices = getConst . traverseScoped collect
  where
    collect bound (Local index) _ | index >= bound = Const [index - bound]
    collect _ _ descend = descend
