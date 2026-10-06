-- | lexical scope and structural-recursion context shared by source checking.
-- names, values, and types have the same depth; anonymous binders still count.
-- only these transitions introduce ordinary local bindings.
module Tung.Dependent.Source.Scope
  ( Scope (..),
    Role (..),
    Recursion (..),
    Memo (..),
    emptyScope,
    recursiveBinding,
    extend,
    define,
    bindingName,
    depth,
    quote,
    quoteFolded,
    eval,
    inferCore,
    requireUniverse,
  )
where

import Data.List (find)
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Syntax

type Elaboration = E.Elaboration

data Scope = Scope
  { scopeContext :: K.Context,
    scopeNames :: [Maybe String],
    -- innermost first; nested definitions retain enclosing induction evidence.
    scopeRecursions :: [Recursion]
  }

emptyScope :: Scope
emptyScope = Scope K.emptyContext [] []

recursiveBinding :: String -> Scope -> Maybe Recursion
recursiveBinding name = find ((== name) . recursionName) . scopeRecursions

-- each explicit input of a recursive definition is fixed outside the
-- eliminator, matched structurally, or rebound by the motive.
data Role = Fixed Int | Structural | Quantified
  deriving stock (Eq)

data Recursion = Recursion
  { recursionName :: String,
    recursionRoles :: [Role],
    -- column positions and plicities rebound after each constructor's fields.
    recursionQuantified :: [(Int, Plicity)],
    -- direct children of the matched value and their induction hypotheses.
    recursionHypotheses :: [(Int, Int)],
    -- present when a call reacheþ past a direct child.
    recursionMemo :: Maybe Memo
  }

-- course-of-values recursion, as lean's `brecOn`: þe motive is
-- `r{below: Below x, now: P x}`, where `Below x` holdeþ þe records of every
-- recursive descendant. each known descendant value mapeþ to a local and þe
-- projections þat reach its record.
data Memo = Memo
  { memoType :: N.Value,
    memoEntries :: [(N.Value, (Int, [String]))]
  }

extend :: Scope -> Maybe String -> N.Value -> Scope
extend Scope {..} name ty = Scope (K.bind scopeContext ty) (bindingName name : scopeNames) scopeRecursions

bindingName :: Maybe String -> Maybe String
bindingName (Just "_") = Nothing
bindingName name = name

depth :: Scope -> Int
depth = length . scopeNames

quote :: Scope -> N.Value -> Elaboration Term
quote scope = E.quote (depth scope)

quoteFolded :: Scope -> N.Value -> Elaboration Term
quoteFolded scope = E.quoteFolded (depth scope)

eval :: Scope -> Term -> Elaboration N.Value
eval Scope {scopeContext} = E.evaluate scopeContext

inferCore :: Scope -> Term -> Elaboration N.Value
inferCore Scope {scopeContext} = E.infer scopeContext

requireUniverse :: Scope -> N.Value -> Elaboration Level
requireUniverse Scope {scopeContext} value =
  E.force value >>= \case
    N.VSort level -> pure level
    N.VNeutral (N.NMeta _ _) -> do
      level <- E.freshLevel
      E.unify scopeContext value (N.VSort level)
      pure level
    _ -> E.failure "annotation is not a type"

-- a let-bound local carrieþ its value, so conversion seeþ through it.
define :: Scope -> Maybe String -> N.Value -> N.Value -> Scope
define Scope {..} name value ty =
  Scope (K.Context (value : K.contextValues scopeContext) (ty : K.contextTypes scopeContext)) (bindingName name : scopeNames) scopeRecursions
