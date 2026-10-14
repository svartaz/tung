-- | one declaration's elaboration run: instance solving, goal rendering, and
-- the check that no hole remaineth.
module Tung.Dependent.Source.Elaborate
  ( elaborateHoles,
    elaborateHolesReport,
    runWithHoles,
  )
where

import Control.Monad (unless)
import Data.Containers.ListUtils (nubOrd)
import Data.List (nubBy)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Elaboration qualified as E
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Error qualified as Error
import Tung.Dependent.Source.Instance (solveInstances)
import Tung.Dependent.Source.Render (renderTermIn)
import Tung.Dependent.Syntax hiding (Lambda, Literal)
import Tung.Dependent.Universe qualified as U
import Tung.Identity (SymbolId (..))
import Tung.Token (SourceFailure (..))

-- universe holes are fresh across the complete declaration, including its
-- annotation and every occurrence of a universe-polymorphic global.
type Elaboration = E.Elaboration

-- one declaration's run, with the goal of each `sorry`, rendered once the
-- declaration's instances are chosen. metadata, such as law obligations,
-- and resolved checking references travel beside the result. a type must be determined: a top-level let is
-- never generalised over its holes, so a polymorphic let writeth its
-- parameters.
elaborateHoles :: SourceProgram -> Elaboration (Term, N.Value, a) -> Either SourceFailure (K.Inferred, a, [Hole], Set.Set SymbolId)
elaborateHoles program action = fst (elaborateHolesReport program action)

-- keep diagnostic goals even when checking faileth. only the Right result may
-- cross the kernel boundary or enter the module environment.
elaborateHolesReport :: SourceProgram -> Elaboration (Term, N.Value, a) -> (Either SourceFailure (K.Inferred, a, [Hole], Set.Set SymbolId), Report)
elaborateHolesReport program@SourceProgram {..} action = (finish =<< checked, report)
  where
    (checked, report) = runWithHoles program (globals programEnvironment) do
      (term, ty, metadata) <- action
      solveInstances programEnvironment globalNames
      remaining <- E.takeInstanceGoals
      unless (null remaining) (E.failure "a bizen requirement hath an ilk that is still unknown; add an annotation")
      open <- E.unsolved
      unless (null open) (E.failure "an ilk is still unknown; write the polymorphic parameters, as [@α: *, x: α, α], or add an annotation")
      annotation <- E.quote 0 ty
      term <- E.zonk term
      annotation <- E.zonk annotation
      references <- E.takeReferences
      pure (term, annotation, metadata, references)
    finish ((term, annotation, metadata, references), constraints) = do
      -- folded solutions bring each global instantiation's constraints once.
      folded <- Error.fromString (traverse (uncurry instantiated) (nubOrd (concatMap constants [term, annotation])))
      result <- Error.fromString (K.generalise term annotation (constraints ++ concat folded))
      pure (result, metadata, reportHoles report, references)
    instantiated name levels = case Map.lookup name (globals programEnvironment) of
      Just definition -> traverse (U.instantiateConstraint levels) (definitionConstraints definition)
      Nothing -> Right []

-- the exception is caught inside inference so goal rendering can read its last
-- metavariable solutions. rejected speculative trials have already rolled back.
runWithHoles :: SourceProgram -> Globals -> Elaboration a -> (Either SourceFailure (a, [Constraint]), Report)
runWithHoles SourceProgram {globalNames} base action =
  case E.runElaboration (displayName globalNames) base do
    result <- E.recover action
    holes <- nubBy (\left right -> holeSpan left == holeSpan right) <$> (E.takeHoles >>= traverse (renderHole base render))
    names <- nubOrd <$> E.takeNames
    pure (result, Report holes names) of
    Left failure -> (Left failure, mempty)
    Right ((result, report), constraints) -> ((,constraints) <$> result, report)
  where
    render = renderTermIn base (briefName globalNames)

constants :: Term -> [(SymbolId, [Level])]
constants = \case
  Global name levels -> [(name, levels)]
  term -> concatMap (constants . snd) (children term)

-- a hole's goal and its named locals, outermost first. generated locals,
-- whose names start with `#`, are omitted.
-- the text is built lazily from a snapshot of the hole solutions, so a goal
-- that is never printed, such as one in an imported module, costeth nothing.
renderHole :: Globals -> (K.Context -> [String] -> Term -> String) -> E.HoleSite -> Elaboration Hole
renderHole base render E.HoleSite {..} = do
  resolve <- E.resolver
  let depthNow = length holeNames
      -- a pattern variable is a named alias of an unnamed field local.
      aliases = Map.fromList [(field, name) | (Just name, N.VNeutral (N.NLocal field)) <- zip holeNames (K.contextValues holeContext)]
      names = [fromMaybe (Map.findWithDefault "_" (depthNow - position - 1) aliases) name | (position, name) <- zip [0 ..] holeNames]
      outer count = K.Context (drop count (K.contextValues holeContext)) (drop count (K.contextTypes holeContext))
      shown count value =
        let current = outer count
         in either (const "?") (render current (drop count names)) (N.quoteDisplayWith (N.Normaliser resolve base) (depthNow - count) value)
      goal = shown 0 holeGoal
      context = [(name, shown (position + 1) (K.contextTypes holeContext !! position)) | (position, name) <- zip [0 ..] holeNames]
  pure (Hole holeSpan goal [(name, ty) | (Just name, ty) <- reverse context, take 1 name /= "#"])
