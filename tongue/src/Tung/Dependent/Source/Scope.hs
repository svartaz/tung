-- | lexical scope and structural-recursion context shared by source checking.
-- names, values, and types have the same depth; anonymous binders still count.
-- only these transitions introduce ordinary local bindings.
module Tung.Dependent.Source.Scope
  ( Scope (..),
    Role (..),
    IndexPattern (..),
    Recursion (..),
    Memo (..),
    emptyScope,
    recursiveBinding,
    extend,
    bindDomain,
    define,
    bindingName,
    depth,
    quote,
    quoteFolded,
    eval,
    evalArgument,
    inferCore,
    requireUniverse,
  )
where

import Data.List (find)
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Syntax
import Tung.Identity (SymbolId)

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
-- eliminator, matched structurally, rebound by the motive, or an index leaf
-- identified by its original input level.
data Role = Fixed Int | Structural | Quantified | Index Int
  deriving stock (Eq)

-- an index in constructor form over variables, as `n s` or `a ‥ empty`.
-- leaf levels identify the declaration's inputs, even after branch refinement.
data IndexPattern = IndexVariable Int | IndexConstructor SymbolId [IndexPattern]

data Recursion = Recursion
  { recursionName :: String,
    recursionRoles :: [Role],
    -- each child must match this declared shape before its hypothesis is used.
    recursionIndices :: [IndexPattern],
    -- column positions and plicities rebound after each constructor's fields.
    recursionQuantified :: [(Int, Plicity)],
    -- direct children of the matched value and their induction hypotheses.
    recursionHypotheses :: [(Int, Int)],
    -- present when a call reacheth past a direct child.
    recursionMemo :: Maybe Memo
  }

-- course-of-values recursion, as lean's `brecOn`: the motive is
-- `r{below: Below x, now: P x}`, where `Below x` holdeth the records of every
-- recursive descendant. joint records also retain ordinary nested containers;
-- only the chosen root's records may justify a call. each known descendant
-- mapeth to its checked target, a local, and its record projections. a function
-- field's projection taketh the same arguments as the field.
data Memo = Memo
  { memoRoot :: SymbolId,
    -- target indices precede the value in each joint record motive.
    memoTypes :: [(SymbolId, ([Plicity], N.Value))],
    memoEntries :: [(N.Value, (SymbolId, Int, [String]))]
  }

extend :: Scope -> Maybe String -> N.Value -> Scope
extend Scope {..} name ty = Scope (K.bind scopeContext ty) (bindingName name : scopeNames) scopeRecursions

-- the codomain and extended scope share the same fresh neutral input.
bindDomain :: Scope -> Maybe String -> N.Value -> N.Closure -> Elaboration (Scope, N.Value)
bindDomain scope name domain codomain =
  (extend scope name domain,) <$> E.instantiate codomain (N.VNeutral (N.NLocal (depth scope)))

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

-- an argument's worth, folded until forced.
evalArgument :: Scope -> Term -> Elaboration N.Value
evalArgument Scope {scopeContext} = E.evaluateGlued scopeContext

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

-- a let-bound local carrieth its value, so conversion seeth through it.
define :: Scope -> Maybe String -> N.Value -> N.Value -> Scope
define Scope {..} name value ty =
  Scope (K.Context (value : K.contextValues scopeContext) (ty : K.contextTypes scopeContext)) (bindingName name : scopeNames) scopeRecursions
