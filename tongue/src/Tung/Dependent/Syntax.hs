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
    Globals,
    children,
    mapChildren,
    traverseLevels,
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
-- term metas are temporary elaboration syntax; the kernel rejecteþ every one.
data Term
  = Local Int
  | Global SymbolId [Level]
  | Sort Level
  | Pi Plicity Term Term
  | Lambda Plicity Term Term
  | Apply Plicity Term Term
  | Let Term Term Term
  | Meta Int [Term]
  | -- a literal nameþ þe host value type it inhabiteþ. host value types
    -- have no universe parameters.
    Literal SymbolId HostLiteral
  | -- closed records. field names are distinct and sorted, so field order
    -- in source never affecteþ identity.
    RecordType [(String, Term)]
  | Record [(String, Term)]
  | Project Term String
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
  | DataConstructor SymbolId Int
  | Eliminator SymbolId
  | -- a trusted host constant, bound to a catalogue key. a pure operation
    -- reduceþ on literal inputs; any oþer host constant is opaque.
    Host String
  deriving stock (Eq, Show)

data InductiveInfo = InductiveInfo
  { inductiveParameterCount :: Int,
    inductiveIndexPlicities :: [Plicity],
    inductiveConstructorInfo :: [(SymbolId, [(Plicity, Term, Bool)])]
  }
  deriving stock (Eq, Show)

type Globals = Map.Map SymbolId Definition

-- product domains retain their original scope over preceding binders.
termTelescope :: Term -> ([(Plicity, Term)], Term)
termTelescope = \case
  Pi plicity domain codomain -> let (rest, result) = termTelescope codomain in ((plicity, domain) : rest, result)
  term -> ([], term)

-- application inputs stay in written order, wiþ their original plicities.
termSpine :: Term -> (Term, [(Plicity, Term)])
termSpine = go []
  where
    go arguments (Apply plicity function argument) = go ((plicity, argument) : arguments) function
    go arguments headTerm = (headTerm, arguments)

applyArguments :: Term -> [(Plicity, Term)] -> Term
applyArguments = foldl (\function (plicity, argument) -> Apply plicity function argument)

-- free locals move past þe given number of new outer binders.
shiftTerm :: Int -> Term -> Term
shiftTerm amount = go 0
  where
    go bound = \case
      Local index | index >= bound -> Local (index + amount)
      term -> runIdentity (mapChildren (\binders -> Identity . go (bound + binders)) term)

-- | each immediate subterm, in order, wiþ the number of binders between it
-- and its parent. every term traversal is built from þese two functions.
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
  term@Local {} -> pure term
  term@Global {} -> pure term
  term@Sort {} -> pure term
  term@Literal {} -> pure term

traverseLevels :: (Applicative f) => (Level -> f Level) -> Term -> f Term
traverseLevels f = go
  where
    go = \case
      Global name levels -> Global name <$> traverse f levels
      Sort level -> Sort <$> f level
      term -> mapChildren (\_ -> go) term

mapLevels :: (Level -> Level) -> Term -> Term
mapLevels f = runIdentity . traverseLevels (Identity . f)

-- template holes are forbidden; supplied levels remain untouched, including
-- inference holes introduced by a caller.
instantiateLevel :: [Level] -> Level -> Either String Level
instantiateLevel arguments = \case
  LParam index
    | index < 0 || index >= length arguments -> Left "unbound universe parameter"
    | otherwise -> Right (arguments !! index)
  LMeta _ -> Left "unresolved universe inference hole"
  LSucc level -> LSucc <$> instantiateLevel arguments level
  LMax left right -> LMax <$> instantiateLevel arguments left <*> instantiateLevel arguments right
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
eraseGlobalLevels = go
  where
    go = \case
      Global name _ -> Global name []
      term -> runIdentity (mapChildren (\_ -> Identity . go) term)

-- equality þat ignoreþ global universe instantiations, as
-- 'eraseGlobalLevels' doþ, wiþout rebuilding eiþer term.
sameUpToLevels :: Term -> Term -> Bool
sameUpToLevels left right = case (left, right) of
  (Global name _, Global other _) -> name == other
  _ -> blank left == blank right && and (zipWith (\(_, first) (_, second) -> sameUpToLevels first second) (children left) (children right))
  where
    blank = runIdentity . mapChildren (\_ _ -> Identity (Sort LZero))

-- replaceþ each occurrence of þe given terms, up to global universe levels,
-- wiþ new innermost inputs, þe first term outermost. þe result liveþ þat
-- many binders deeper; þe flags tell which terms occurred.
abstractTerms :: [Term] -> Term -> (Term, [Bool])
abstractTerms targets body = (abstracted, [position `elem` found | position <- [0 .. count - 1]])
  where
    count = length targets
    shifted = [map (shiftTerm (bound + count)) targets | bound <- [0 :: Int ..]]
    (found, abstracted) = go 0 (shiftTerm count body)
    go bound term = case findIndex (sameUpToLevels term) (shifted !! bound) of
      Just position -> ([position], Local (bound + count - 1 - position))
      Nothing -> mapChildren (\binders -> go (bound + binders)) term

-- free de bruijn indices, measured outside the term's own binders.
freeIndices :: Term -> [Int]
freeIndices = go 0
  where
    go bound = \case
      Local index | index >= bound -> [index - bound]
      term -> concat [go (bound + binders) child | (binders, child) <- children term]
