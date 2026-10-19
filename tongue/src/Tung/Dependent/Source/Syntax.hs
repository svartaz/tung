{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ViewPatterns #-}

-- | types and values share this source syntax. names remain readable until
-- elaboration resolveth them to checked global identities or local indices.
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
    pattern Projection,
    pattern Sorry,
    pattern Induce,
    pattern Inferred,
    unlocated,
    expressionSpan,
    trailingSpan,
    Parameter (..),
    Binder (..),
    Argument (..),
    Declaration (..),
    ConstructorDeclaration (..),
    Row (..),
    FlockMember (..),
    unshown,
    repeatedNames,
    freeNames,
    sketch,
  )
where

import Data.List (intercalate)
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Tung.Dependent.Literal (renderLiteral)
import Tung.Dependent.Syntax (HostLiteral (..), Plicity (..))
import Tung.Token (SourceSpan (..), utf16Length)

-- an expression's constructors are written without their `Raw` prefix: each
-- name below is a pattern that looketh through `Located`, so a span never
-- changeth what a match seeth. only elaboration's entry points read spans.
data Expression
  = RawName String
  | RawUniverse
  | RawProduct [Parameter] Expression
  | RawLambda [Binder] Expression
  | RawApplication Expression [Argument]
  | RawAscription Expression Expression
  | RawBlock [Declaration] Expression
  | RawLiteralExpression HostLiteral
  | -- patterns reuse expression syntax; elaboration decideth which names are
    -- constructors. `_` is valid only inside a pattern.
    RawWildcard
  | -- `{rows}` with more than one row or a non-variable pattern.
    RawCases [Row]
  | RawMatch [Expression] [Row]
  | -- `value.field` readeth a named field of a one-constructor ilk.
    RawProjection Expression String
  | -- `sorry` standeth for an omitted term of any type.
    RawSorry
  | -- `unbuild name` is the eliminator of the ilk or flock `name`.
    RawInduce String
  | -- `a:` leaveth a slot type to inference, as doth an omitted result.
    RawInferred
  | -- the source span of the expression inside.
    Located SourceSpan Expression
  deriving stock (Eq, Show)

-- the span the parser gave an expression, if any.
expressionSpan :: Expression -> Maybe SourceSpan
expressionSpan = \case
  Located span _ -> Just span
  _ -> Nothing

-- the span of a name that endeth an expression's span, as a field or the
-- family after `unbuild`, in utf-16 units.
trailingSpan :: SourceSpan -> String -> SourceSpan
trailingSpan (SourceSpan _ end) name = SourceSpan (end - utf16Length name) end

unlocated :: Expression -> Expression
unlocated = \case
  Located _ expression -> unlocated expression
  expression -> expression

{-# COMPLETE Name, Universe, Product, Lambda, Application, Ascription, Block, LiteralExpression, Wildcard, Cases, Match, Projection, Sorry, Induce, Inferred #-}

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

-- a law is an ordinary member whose type requireth an equality proof.
data FlockMember = FlockMember String Expression
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
        declarationBody :: Expression,
        -- `fast name: type ≔ body` may name itself without bound; its type
        -- endeth in a deed.
        declarationFixpoint :: Bool
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
  | -- `bizen:type { let member ≔ body }` constructeth an ordinary dictionary.
    -- the type's implicit slots are parameters and requirements; it endeth in a flock.
    BizenDeclaration
      { -- `bizen 10: …` writeth a priority; higher is tried first.
        bizenPriority :: Maybe Integer,
        -- `bizen fallback: …` is tried only for a goal stuck on an unknown input.
        bizenFallback :: Bool,
        bizenType :: Expression,
        bizenMembers :: [Declaration]
      }
  | -- `use path [alias]` importeth a module's shown names.
    ImportDeclaration
      { importPath :: String,
        importAlias :: Maybe String
      }
  | -- `show declaration` publisheth its names to importing modules.
    ShownDeclaration Declaration
  | -- `show a, b` publisheth visible names, including imported ones.
    ReExportDeclaration [String]
  | -- `orsetting name:type` assumeth a constant of a type without a proof.
    AssumptionDeclaration
      { assumptionName :: String,
        assumptionAnnotation :: Expression
      }
  | -- a top-level host binding: `let name:type ≔ 'key' fremmed`, optionally
    -- followed by its model, a definition that may call the binding itself.
    HostDeclaration
      { hostName :: String,
        hostAnnotation :: Expression,
        hostKey :: String,
        hostModel :: Maybe Expression
      }
  deriving stock (Eq, Show)

-- each name that occurreth again after its first occurrence, in order.
repeatedNames :: [String] -> [String]
repeatedNames names = [name | (index, name) <- zip [0 :: Int ..] names, name `elem` take index names]

-- a declaration without its `show` markers.
unshown :: Declaration -> Declaration
unshown = \case
  ShownDeclaration declaration -> unshown declaration
  declaration -> declaration

-- every constructor stateth its type, as in a GADT.
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
  Projection record _ -> [record]
  Sorry -> []
  Induce _ -> []
  Inferred -> []
  where
    declarationExpressions = \case
      Declaration {..} -> maybe [] pure declarationAnnotation ++ [declarationBody]
      _ -> []

-- names an expression useth but doth not bind. in a pattern, a name is a use
-- only when the supplied predicate recogniseth a constructor; any other name bindeth.
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
      expression -> Set.unions (map (go bound) (subexpressions expression))
    binders bound [] result = go bound result
    -- every annotation and local right-hand side seeth only earlier binders.
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

-- a fully parenthesised, location-free rendering for tests: an application
-- printeth its function first, as `(f a @t b)`.
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
  Projection record field -> sketch record ++ "." ++ field
  Sorry -> "sorry"
  Induce name -> "unbuild " ++ name
  Inferred -> "?"
  where
    parameter Parameter {..} = (if parameterPlicity == Implicit then "@" else "") ++ maybe "" (++ ": ") parameterName ++ sketch parameterType
    binder Binder {..} = (if binderPlicity == Implicit then "@" else "") ++ fromMaybe "_" binderName ++ maybe "" ((": " ++) . sketch) binderAnnotation
    argument Argument {..} = (if argumentPlicity == Implicit then "@" else "") ++ sketch argumentExpression
    row Row {..} = intercalate ", " (map sketch rowPatterns) ++ " ^ " ++ sketch rowBody
    declaration = \case
      Declaration {..} -> (if declarationFixpoint then "fast " else "let ") ++ declarationName ++ maybe "" ((": " ++) . sketch) declarationAnnotation ++ " ≔ " ++ sketch declarationBody ++ " "
      _ -> "declaration "
