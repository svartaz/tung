{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

-- | types and values share this source syntax. names remain readable until
-- elaboration resolveþ them to checked global identities or local indices.
module Tung.Dependent.Source.Syntax
  ( Expression (Located),
    pattern Name,
    pattern Universe,
    pattern Product,
    pattern Lambda,
    pattern Application,
    pattern Ascription,
    pattern Block,
    pattern LiteralExpression,
    pattern Wildcard,
    pattern Cases,
    pattern Match,
    pattern MatchFor,
    pattern RecordTypeExpression,
    pattern RecordExpression,
    pattern RecordUpdate,
    pattern Projection,
    pattern Sorry,
    pattern Induce,
    pattern Inferred,
    unlocated,
    Parameter (..),
    Binder (..),
    Argument (..),
    Declaration (..),
    ConstructorDeclaration (..),
    Row (..),
    RecordChange (..),
    FlockMember (..),
    freeNames,
    sketch,
  )
where

import Data.List (intercalate)
import Data.Set qualified as Set
import Tung.Dependent.Literal (renderLiteral)
import Tung.Dependent.Syntax (HostLiteral (..), Plicity (..))
import Tung.Token (SourceSpan)

-- an expression's constructors are written wiþout þeir `Raw` prefix: each
-- name below is a pattern þat lookeþ þrough `Located`, so a span never
-- changeþ what a match seeþ. only elaboration's entry points read spans.
data Expression
  = RawName String
  | RawUniverse
  | RawProduct [Parameter] Expression
  | RawLambda [Binder] Expression
  | RawApplication Expression [Argument]
  | RawAscription Expression Expression
  | RawBlock [Declaration] Expression
  | RawLiteralExpression HostLiteral
  | -- patterns reuse expression syntax; elaboration decideþ which names are
    -- constructors. `_` is valid only inside a pattern.
    RawWildcard
  | -- `{rows}` wiþ more þan one row or a non-variable pattern.
    RawCases [Row]
  | RawMatch [Expression] [Row]
  | -- `match e for known { rows }`: each row also bindeþ `known: e = pattern`.
    RawMatchFor Expression String [Row]
  | -- `r{name:type, ...}`, `r{name = value, ...}`, `r{= base, changes}`.
    RawRecordTypeExpression [(String, Expression)]
  | RawRecordExpression [(String, Expression)]
  | RawRecordUpdate Expression [RecordChange]
  | RawProjection Expression String
  | -- `sorry` standeþ for an omitted term of any type.
    RawSorry
  | -- `unbuild name` is þe eliminator of þe ilk or flock `name`.
    RawInduce String
  | -- `a:` leaveþ a slot type to inference, as doth an omitted result.
    RawInferred
  | -- þe source span of þe expression inside.
    Located SourceSpan Expression
  deriving stock (Eq, Show)

unlocated :: Expression -> Expression
unlocated = \case
  Located _ expression -> unlocated expression
  expression -> expression

{-# COMPLETE Name, Universe, Product, Lambda, Application, Ascription, Block, LiteralExpression, Wildcard, Cases, Match, MatchFor, RecordTypeExpression, RecordExpression, RecordUpdate, Projection, Sorry, Induce, Inferred #-}

pattern Name :: String -> Expression
pattern Name a0 <- (unlocated -> RawName a0)
  where
    Name a0 = RawName a0

pattern Universe :: Expression
pattern Universe <- (unlocated -> RawUniverse)
  where
    Universe = RawUniverse

pattern Product :: [Parameter] -> Expression -> Expression
pattern Product a0 a1 <- (unlocated -> RawProduct a0 a1)
  where
    Product a0 a1 = RawProduct a0 a1

pattern Lambda :: [Binder] -> Expression -> Expression
pattern Lambda a0 a1 <- (unlocated -> RawLambda a0 a1)
  where
    Lambda a0 a1 = RawLambda a0 a1

pattern Application :: Expression -> [Argument] -> Expression
pattern Application a0 a1 <- (unlocated -> RawApplication a0 a1)
  where
    Application a0 a1 = RawApplication a0 a1

pattern Ascription :: Expression -> Expression -> Expression
pattern Ascription a0 a1 <- (unlocated -> RawAscription a0 a1)
  where
    Ascription a0 a1 = RawAscription a0 a1

pattern Block :: [Declaration] -> Expression -> Expression
pattern Block a0 a1 <- (unlocated -> RawBlock a0 a1)
  where
    Block a0 a1 = RawBlock a0 a1

pattern LiteralExpression :: HostLiteral -> Expression
pattern LiteralExpression a0 <- (unlocated -> RawLiteralExpression a0)
  where
    LiteralExpression a0 = RawLiteralExpression a0

pattern Wildcard :: Expression
pattern Wildcard <- (unlocated -> RawWildcard)
  where
    Wildcard = RawWildcard

pattern Cases :: [Row] -> Expression
pattern Cases a0 <- (unlocated -> RawCases a0)
  where
    Cases a0 = RawCases a0

pattern Match :: [Expression] -> [Row] -> Expression
pattern Match a0 a1 <- (unlocated -> RawMatch a0 a1)
  where
    Match a0 a1 = RawMatch a0 a1

pattern MatchFor :: Expression -> String -> [Row] -> Expression
pattern MatchFor a0 a1 a2 <- (unlocated -> RawMatchFor a0 a1 a2)
  where
    MatchFor a0 a1 a2 = RawMatchFor a0 a1 a2

pattern RecordTypeExpression :: [(String, Expression)] -> Expression
pattern RecordTypeExpression a0 <- (unlocated -> RawRecordTypeExpression a0)
  where
    RecordTypeExpression a0 = RawRecordTypeExpression a0

pattern RecordExpression :: [(String, Expression)] -> Expression
pattern RecordExpression a0 <- (unlocated -> RawRecordExpression a0)
  where
    RecordExpression a0 = RawRecordExpression a0

pattern RecordUpdate :: Expression -> [RecordChange] -> Expression
pattern RecordUpdate a0 a1 <- (unlocated -> RawRecordUpdate a0 a1)
  where
    RecordUpdate a0 a1 = RawRecordUpdate a0 a1

pattern Projection :: Expression -> String -> Expression
pattern Projection a0 a1 <- (unlocated -> RawProjection a0 a1)
  where
    Projection a0 a1 = RawProjection a0 a1

pattern Sorry :: Expression
pattern Sorry <- (unlocated -> RawSorry)
  where
    Sorry = RawSorry

pattern Induce :: String -> Expression
pattern Induce a0 <- (unlocated -> RawInduce a0)
  where
    Induce a0 = RawInduce a0

pattern Inferred :: Expression
pattern Inferred <- (unlocated -> RawInferred)
  where
    Inferred = RawInferred

-- a flock requireþ members and stateþ named laws. a law is a member whose type
-- endeþ in an equation; it is checked documentation, not a proof obligation,
-- during migration.
data FlockMember
  = FlockMember String Expression
  | FlockLaw String [Parameter] Expression Expression
  deriving stock (Eq, Show)

-- an update setþ a field, adding it when absent, or removeþ one.
data RecordChange = SetField String Expression | RemoveField String
  deriving stock (Eq, Show)

-- one explicit pattern per column. `;` alternatives become separate rows.
data Row = Row
  { rowPatterns :: [Expression],
    rowBody :: Expression
  }
  deriving stock (Eq, Show)

-- an unnamed implicit parameter, written `@:flock`, is a requirement.
data Parameter = Parameter
  { parameterPlicity :: Plicity,
    parameterName :: Maybe String,
    parameterType :: Expression
  }
  deriving stock (Eq, Show)

data Binder = Binder
  { binderPlicity :: Plicity,
    binderName :: Maybe String,
    binderAnnotation :: Maybe Expression
  }
  deriving stock (Eq, Show)

data Argument = Argument
  { argumentPlicity :: Plicity,
    argumentExpression :: Expression
  }
  deriving stock (Eq, Show)

data Declaration
  = Declaration
      { declarationName :: String,
        declarationAnnotation :: Maybe Expression,
        declarationBody :: Expression
      }
  | InductiveDeclaration
      { inductiveName :: String,
        inductiveSignature :: Expression,
        inductiveConstructors :: [ConstructorDeclaration]
      }
  | -- `flock name:[parameters, @:parent, *] { let member:type; law:[...] }`.
    FlockDeclaration
      { flockName :: String,
        flockParameters :: [Parameter],
        flockMembers :: [FlockMember]
      }
  | -- `bizen:type { let member = body }` defineþ a registered dictionary. the
    -- type's implicit slots are parameters and requirements; it endeþ in a flock.
    BizenDeclaration
      { -- `bizen 10: …` writeþ a priority; higher is tried first.
        bizenPriority :: Maybe Integer,
        -- `bizen fallback: …` is tried only for a goal stuck on an unknown input.
        bizenFallback :: Bool,
        bizenType :: Expression,
        bizenMembers :: [Declaration]
      }
  | -- `use path [alias]` importeþ a module's shown names.
    ImportDeclaration
      { importPath :: String,
        importAlias :: Maybe String
      }
  | -- `show declaration` publisheþ its names to importing modules.
    ShownDeclaration Declaration
  | -- `show a, b` publisheþ visible names, including imported ones.
    ReExportDeclaration [String]
  | -- `orsend name:type` assumeþ a constant of a type wiþout a proof.
    AssumptionDeclaration
      { assumptionName :: String,
        assumptionAnnotation :: Expression
      }
  | -- a top-level host binding: `let name:type ≔ 'key' fremmed`, optionally
    -- followed by þe name of its model.
    HostDeclaration
      { hostName :: String,
        hostAnnotation :: Expression,
        hostKey :: String,
        hostModel :: Maybe String
      }
  deriving stock (Eq, Show)

-- every constructor stateþ its type, as in a GADT.
data ConstructorDeclaration = ConstructorDeclaration
  { constructorName :: String,
    constructorAnnotation :: Expression
  }
  deriving stock (Eq, Show)

-- | immediate subexpressions, including declaration annotations and bodies
-- inside blocks. patterns are not included.
subexpressions :: Expression -> [Expression]
subexpressions = \case
  Name _ -> []
  Universe -> []
  Product parameters result -> map parameterType parameters ++ [result]
  Lambda binders body -> [annotation | Binder {binderAnnotation = Just annotation} <- binders] ++ [body]
  Application function arguments -> function : map argumentExpression arguments
  Ascription expression annotation -> [expression, annotation]
  Block declarations result -> concatMap declarationExpressions declarations ++ [result]
  LiteralExpression _ -> []
  Wildcard -> []
  Cases rows -> map rowBody rows
  Match scrutinees rows -> scrutinees ++ map rowBody rows
  MatchFor scrutinee _ rows -> scrutinee : map rowBody rows
  RecordTypeExpression fields -> map snd fields
  RecordExpression fields -> map snd fields
  RecordUpdate base changes -> base : [value | SetField _ value <- changes]
  Projection record _ -> [record]
  Sorry -> []
  Induce _ -> []
  Inferred -> []
  where
    declarationExpressions = \case
      Declaration {..} -> maybe [] pure declarationAnnotation ++ [declarationBody]
      _ -> []

-- names an expression useþ but doth not bind. in a pattern, a name is a use
-- only when þe supplied predicate recogniseþ a constructor; any oþer name bindeþ.
freeNames :: (String -> Bool) -> Set.Set String -> Expression -> Set.Set String
freeNames isConstructor = go
  where
    go bound = \case
      Name name -> if name `Set.member` bound then Set.empty else Set.singleton name
      Induce name -> if name `Set.member` bound then Set.empty else Set.singleton name
      Product parameters result -> binders bound [(parameterName, [parameterType]) | Parameter {parameterName, parameterType} <- parameters] result
      Lambda lambdaBinders body ->
        binders bound [(binderName, maybe [] pure binderAnnotation) | Binder {binderName, binderAnnotation} <- lambdaBinders] body
      Block declarations result -> locals bound declarations result
      Cases rows -> Set.unions (map (row bound) rows)
      Match scrutinees rows -> Set.unions (map (go bound) scrutinees ++ map (row bound) rows)
      MatchFor scrutinee known rows -> Set.unions (go bound scrutinee : map (row (Set.insert known bound)) rows)
      expression -> Set.unions (map (go bound) (subexpressions expression))
    binders bound [] result = go bound result
    -- every annotation and local right-hand side seeþ only earlier binders.
    binders bound ((name, annotations) : rest) result =
      Set.unions (map (go bound) annotations ++ [binders (maybe bound (`Set.insert` bound) name) rest result])
    locals bound [] result = go bound result
    locals bound (Declaration {..} : rest) result =
      Set.unions (go bound declarationBody : map (go bound) (maybe [] pure declarationAnnotation) ++ [locals (Set.insert declarationName bound) rest result])
    -- unsupported local declaration forms are rejected by source checking.
    locals bound (_ : rest) result = locals bound rest result
    row bound Row {rowPatterns, rowBody} =
      let (uses, bindings) = foldMap patternNames rowPatterns
       in Set.union uses (go (Set.union bound bindings) rowBody)
    patternNames = \case
      Name name
        | isConstructor name -> (Set.singleton name, Set.empty)
        | otherwise -> (Set.empty, Set.singleton name)
      Application function arguments -> foldMap patternNames (function : map argumentExpression arguments)
      _ -> (Set.empty, Set.empty)

-- a fully parenþesised, location-free rendering for tests: an application
-- printeþ its function first, as `(f a @t b)`.
sketch :: Expression -> String
sketch = \case
  Name name -> name
  Universe -> "*"
  Product parameters result -> "[" ++ intercalate ", " (map parameter parameters ++ [sketch result]) ++ "]"
  Lambda binders body -> "{" ++ intercalate ", " (map binder binders) ++ " ^ " ++ sketch body ++ "}"
  Application function arguments -> "(" ++ unwords (sketch function : map argument arguments) ++ ")"
  Ascription expression annotation -> "(" ++ sketch expression ++ ": " ++ sketch annotation ++ ")"
  Block declarations result -> "(" ++ concatMap declaration declarations ++ "yield " ++ sketch result ++ ")"
  LiteralExpression literal -> renderLiteral literal
  Wildcard -> "_"
  Cases rows -> "{" ++ intercalate ", " (map row rows) ++ "}"
  Match scrutinees rows -> "match " ++ intercalate ", " (map sketch scrutinees) ++ " {" ++ intercalate ", " (map row rows) ++ "}"
  MatchFor scrutinee known rows -> "match " ++ sketch scrutinee ++ " for " ++ known ++ " {" ++ intercalate ", " (map row rows) ++ "}"
  RecordTypeExpression fields -> "r{" ++ intercalate ", " [name ++ ": " ++ sketch field | (name, field) <- fields] ++ "}"
  RecordExpression fields -> "r{" ++ intercalate ", " [name ++ " ≔ " ++ sketch field | (name, field) <- fields] ++ "}"
  RecordUpdate base changes -> "r{≔ " ++ intercalate ", " (sketch base : map change changes) ++ "}"
  Projection record field -> sketch record ++ "." ++ field
  Sorry -> "sorry"
  Induce name -> "unbuild " ++ name
  Inferred -> "?"
  where
    parameter Parameter {..} = (if parameterPlicity == Implicit then "@" else "") ++ maybe "" (++ ": ") parameterName ++ sketch parameterType
    binder Binder {..} = (if binderPlicity == Implicit then "@" else "") ++ maybe "_" id binderName ++ maybe "" ((": " ++) . sketch) binderAnnotation
    argument Argument {..} = (if argumentPlicity == Implicit then "@" else "") ++ sketch argumentExpression
    row Row {..} = intercalate ", " (map sketch rowPatterns) ++ " ^ " ++ sketch rowBody
    change = \case
      SetField name value -> name ++ " ≔ " ++ sketch value
      RemoveField name -> "- " ++ name
    declaration = \case
      Declaration {..} -> "let " ++ declarationName ++ maybe "" ((": " ++) . sketch) declarationAnnotation ++ " ≔ " ++ sketch declarationBody ++ " "
      _ -> "declaration "
