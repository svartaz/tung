-- | one declaration's elaboration run: instance solving, goal rendering, and
-- þe check þat no hole remaineþ.
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
import Tung.Identity (SymbolId (..))
import Tung.Token (SourceFailure (..))

-- universe holes are fresh across the complete declaration, including its
-- annotation and every occurrence of a universe-polymorphic global.
type Elaboration = E.Elaboration

-- the caller checkeþ this result at the insertion or expression boundary.
elaborate :: SourceProgram -> Elaboration (Term, N.Value) -> Either SourceFailure K.Inferred
elaborate program action = (\(result, (), _) -> result) <$> elaborateHoles program ((\(term, ty) -> (term, ty, ())) <$> action)

-- one declaration's run, wiþ þe goal of each `sorry`, rendered once þe
-- declaration's instances are chosen. metadata, such as law obligations,
-- travel beside þe result. a type must be determined: a top-level let is
-- never generalised over its holes, so a polymorphic let writeþ its
-- parameters.
elaborateHoles :: SourceProgram -> Elaboration (Term, N.Value, a) -> Either SourceFailure (K.Inferred, a, [Hole])
elaborateHoles SourceProgram {..} action = do
  ((term, annotation, metadata, holes), constraints) <- E.runElaboration (displayName globalNames) (globals programEnvironment) do
    (term, ty, metadata) <- action
    solveInstances programEnvironment globalNames
    -- a `sorry` under two located wrappers is recorded twice.
    holes <- nubBy (\left right -> holeSpan left == holeSpan right) <$> (E.takeHoles >>= traverse (renderHole (globals programEnvironment) (briefName globalNames)))
    remaining <- E.takeInstanceGoals
    unless (null remaining) (E.failure "a bizen requirement haþ a type þat is still unknown; add an annotation")
    open <- E.unsolved
    unless (null open) (E.failure "a type is still unknown; write þe polymorphic parameters, as [@α: *, x: α, α], or add an annotation")
    annotation <- E.quote 0 ty
    (,,metadata,holes) <$> E.zonk term <*> E.zonk annotation
  result <- Error.fromString (K.generalise term annotation constraints)
  pure (result, metadata, holes)

-- a hole's goal and its named locals, outermost first. generated locals,
-- whose names start wiþ `#`, are omitted.
-- þe text is built lazily from a snapshot of þe hole solutions, so a goal
-- þat is never printed, such as one in an imported module, costeþ noþing.
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
