-- | one declaration's elaboration run: instance solving, goal rendering, and
-- the check that no hole remaineth.
module Tung.Dependent.Source.Elaborate
  ( elaborate,
    elaborateHoles,
  )
where

import Control.Monad (unless)
import Data.List (nubBy)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Render (renderTermWith)
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Source.Instance (solveInstances)
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Universe qualified as U
import Tung.Identity (SymbolId (..))
import Tung.Token (SourceFailure (..))

-- universe holes are fresh across the complete declaration, including its
-- annotation and every occurrence of a universe-polymorphic global.
type Elaboration = E.Elaboration

-- the caller checketh this result at the insertion or expression boundary.
elaborate :: SourceProgram -> Elaboration (Term, N.Value) -> Either SourceFailure K.Inferred
elaborate program action = (\(result, (), _) -> result) <$> elaborateHoles program ((\(term, ty) -> (term, ty, ())) <$> action)

-- one declaration's run, with the goal of each `sorry`, rendered once the
-- declaration's instances are chosen. metadata, such as law obligations,
-- travel beside the result. a type must be determined: a top-level let is
-- never generalised over its holes, so a polymorphic let writeth its
-- parameters.
elaborateHoles :: SourceProgram -> Elaboration (Term, N.Value, a) -> Either SourceFailure (K.Inferred, a, [Hole])
elaborateHoles SourceProgram {..} action = do
  ((term, annotation, metadata, holes), constraints) <- E.runElaboration (displayName globalNames) (globals programEnvironment) do
    (term, ty, metadata) <- action
    solveInstances programEnvironment globalNames
    -- a `sorry` under two located wrappers is recorded twice.
    holes <- nubBy (\left right -> holeSpan left == holeSpan right) <$> (E.takeHoles >>= traverse (renderHole (globals programEnvironment) (briefName globalNames)))
    remaining <- E.takeInstanceGoals
    unless (null remaining) (E.failure "a bizen requirement hath a type that is still unknown; add an annotation")
    open <- E.unsolved
    unless (null open) (E.failure "a type is still unknown; write the polymorphic parameters, as [@α: *, x: α, α], or add an annotation")
    annotation <- E.quote 0 ty
    (,,metadata,holes) <$> E.zonk term <*> E.zonk annotation
  -- a hole's solution stayeth folded, so a constant it nameth bringeth that
  -- definition's universe constraints, as the kernel obligeth them.
  folded <- Error.fromString (traverse (uncurry instantiated) (concatMap constants [term, annotation]))
  result <- Error.fromString (K.generalise term annotation (constraints ++ concat folded))
  pure (result, metadata, holes)
  where
    instantiated name levels = case Map.lookup name (globals programEnvironment) of
      Just definition -> traverse (U.instantiateConstraint levels) (definitionConstraints definition)
      Nothing -> Right []

constants :: Term -> [(SymbolId, [Level])]
constants = \case
  Global name levels -> [(name, levels)]
  term -> concatMap (constants . snd) (children term)

-- a hole's goal and its named locals, outermost first. generated locals,
-- whose names start with `#`, are omitted.
-- the text is built lazily from a snapshot of the hole solutions, so a goal
-- that is never printed, such as one in an imported module, costeth nothing.
renderHole :: Globals -> (SymbolId -> String) -> E.HoleSite -> Elaboration Hole
renderHole base display E.HoleSite {..} = do
  resolve <- E.resolver
  let depthNow = length holeNames
      -- a pattern variable is a named alias of an unnamed field local.
      aliases = Map.fromList [(field, name) | (Just name, N.VNeutral (N.NLocal field)) <- zip holeNames (K.contextValues holeContext)]
      names = [fromMaybe (Map.findWithDefault "_" (depthNow - position - 1) aliases) name | (position, name) <- zip [0 ..] holeNames]
      shown depth bound value = either (const "?") (renderTermWith display bound) (N.quoteDisplayWith (N.Normaliser resolve base) depth value)
      goal = shown depthNow names holeGoal
      context = [(name, shown (depthNow - position - 1) (drop (position + 1) names) (K.contextTypes holeContext !! position)) | (position, name) <- zip [0 ..] holeNames]
  pure (Hole holeSpan goal [(name, ty) | (Just name, ty) <- reverse context, take 1 name /= "#"])
