-- | core terms printed in source syntax, for type inspection and messages.
-- universes print as `*` and implicit arguments are omitted, so a printed
-- term may lose information that the core keepeth.
module Tung.Dependent.Render
  ( renderMismatch,
    renderTermWith,
    renderMismatchWith,
  )
where

import Data.List (intercalate)
import Tung.Dependent.Literal (renderLiteral)
import Tung.Dependent.Syntax
import Tung.Identity (SymbolId (..))
import Tung.Name (lastQualifiedSegment)

-- the names of the enclosing binders, innermost first.
renderTermWith :: (SymbolId -> String) -> [String] -> Term -> String
renderTermWith = render

-- `cannot unify a with b`, for two terms under the same `depth` binders, whose
-- names are not known here.
renderMismatch :: Int -> Term -> Term -> String
renderMismatch = renderMismatchWith (lastQualifiedSegment . symbolName)

renderMismatchWith :: (SymbolId -> String) -> Int -> Term -> Term -> String
renderMismatchWith display depth left right = "cannot unify " ++ render display names left ++ " with " ++ render display names right
  where
    names = ["v" ++ show level | level <- [depth - 1, depth - 2 .. 0]] ++ ["v" ++ show index | index <- [depth .. depth + 99]]

render :: (SymbolId -> String) -> [String] -> Term -> String
render display names = \case
  Pi plicity domain codomain -> bracket display names [] (Pi plicity domain codomain)
  Lambda plicity domain body -> lambda display names [] (Lambda plicity domain body)
  Let _ value body ->
    let name = fresh names Nothing
     in "(let " ++ name ++ " ≔ " ++ render display names value ++ " yield " ++ render display (name : names) body ++ ")"
  term@Apply {} -> case spine term [] of
    (Global symbol _, value : rest)
      | Just field <- accessorField symbol ->
          application (atom display names value ++ "." ++ field) rest
    (function, arguments) -> application (atom display names function) arguments
  term -> atom display names term
  where
    application function [] = function
    application function (first : rest) = unwords (atom display names first : function : map (atom display names) rest)

-- a term that needeth no parentheses as an argument.
atom :: (SymbolId -> String) -> [String] -> Term -> String
atom display names = \case
  Local index -> if index < length names then names !! index else "?"
  Global symbol _ -> display symbol
  Sort _ -> "*"
  Meta _ _ -> "?"
  Literal _ value -> renderLiteral value
  RecordType fields -> "r{" ++ intercalate ", " [name ++ ": " ++ render display names field | (name, field) <- fields] ++ "}"
  Record fields -> "r{" ++ intercalate ", " [name ++ " ≔ " ++ render display names field | (name, field) <- fields] ++ "}"
  Project record name -> atom display names record ++ "." ++ name
  Field index value -> atom display names value ++ ".#" ++ show index
  term@(Pi {}) -> render display names term
  term@(Lambda {}) -> render display names term
  term@(Apply {})
    | (_, []) <- spine term [] -> render display names term
    | (Global symbol _, [_]) <- spine term [], Just _ <- accessorField symbol -> render display names term
  term -> "(" ++ render display names term ++ ")"

-- source names contain no dot; `type.field` is a hidden generated accessor.
-- its receiver and field suffice even when the type hath an imported alias.
accessorField :: SymbolId -> Maybe String
accessorField symbol = case break (== '.') (symbolName symbol) of
  (owner, '.' : field) | not (null owner), not (null field) -> Just field
  _ -> Nothing

-- explicit arguments only, in order.
spine :: Term -> [Term] -> (Term, [Term])
spine (Apply Explicit function argument) arguments = spine function (argument : arguments)
spine (Apply Implicit function _) arguments = spine function arguments
spine function arguments = (function, arguments)

-- `[@α: *, x: α, α]`. a binder that nothing mentioneth printeth only its type.
bracket :: (SymbolId -> String) -> [String] -> [String] -> Term -> String
bracket display names items = \case
  Pi plicity domain codomain ->
    let used = mentions 0 codomain
        name = fresh names (Just domain)
        written = render display names domain
        -- an unnamed implicit input of a non-type is a requirement.
        requirement = not used && not (sorted domain)
        item = case plicity of
          Implicit | requirement -> "@: " ++ written
          Implicit -> "@" ++ name ++ ": " ++ written
          Explicit | used -> name ++ ": " ++ written
          Explicit -> written
     in bracket display (name : names) (item : items) codomain
  result -> "[" ++ intercalate ", " (reverse (render display names result : items)) ++ "]"

lambda :: (SymbolId -> String) -> [String] -> [String] -> Term -> String
lambda display names binders = \case
  Lambda plicity domain body ->
    let name = fresh names (Just domain)
     in lambda display (name : names) (((if plicity == Implicit then "@" else "") ++ name) : binders) body
  body -> "{" ++ intercalate ", " (reverse binders) ++ " ^ " ++ render display names body ++ "}"

-- a type or a type function, such as `[*, *]`.
sorted :: Term -> Bool
sorted = \case
  Sort _ -> True
  Pi _ _ codomain -> sorted codomain
  _ -> False

-- type binders take greek letters, others latin ones; a name in scope is
-- never reused.
fresh :: [String] -> Maybe Term -> String
fresh names domain = case [name | name <- candidates, name `notElem` names] of
  name : _ -> name
  [] -> "x"
  where
    candidates
      | maybe False sorted domain = greek ++ [letter ++ show index | index <- [1 :: Int ..], letter <- greek]
      | otherwise = latin ++ [letter ++ show index | index <- [1 :: Int ..], letter <- latin]
    greek = map pure "αβγδεζηθ"
    latin = map pure "xyzwuv"

mentions :: Int -> Term -> Bool
mentions index = \case
  Local other -> other == index
  term -> or [mentions (index + binders) child | (binders, child) <- children term]
