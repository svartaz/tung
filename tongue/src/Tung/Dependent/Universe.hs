-- | natural-number universes with successor, maximum, and exact constraints.
module Tung.Dependent.Universe
  ( normaliseLevel,
    satisfiable,
    Universes,
    universes,
    universeConstraints,
    constrain,
    trivial,
    entails,
    instantiateConstraint,
  )
where

import Data.Foldable (asum)
import Data.List qualified as List
import Data.Map.Strict qualified as Map
import Data.Maybe (isJust, mapMaybe)
import Data.Set qualified as Set
import Tung.Dependent.Syntax (Constraint (..), Level (..), constraintLevels, instantiateLevel)

data Atom = Zero | Parameter Int | Meta Int
  deriving stock (Eq, Ord)

-- an edge from x to y with weight c meaneth y - x <= c.
data Edge = Edge Atom Atom Integer
  deriving stock (Eq, Ord)

normaliseLevel :: Level -> Level
normaliseLevel = foldl1 LMax . map rebuild . Map.toAscList . levelAtoms
  where
    rebuild (atom, offset) = successors offset $ case atom of
      Zero -> LZero
      Parameter index -> LParam index
      Meta index -> LMeta index
    successors 0 level = level
    successors count level = successors (count - 1) (LSucc level)

-- max of variable-plus-offset atoms; natural variables dominate smaller constants.
levelAtoms :: Level -> Map.Map Atom Integer
levelAtoms level = case Map.lookup Zero atoms of
  Just constant
    | any (\(atom, offset) -> atom /= Zero && offset >= constant) (Map.toList atoms) ->
        Map.delete Zero atoms
  _ -> atoms
  where
    atoms = collect 0 level
    collect offset = \case
      LZero -> Map.singleton Zero offset
      LParam index -> Map.singleton (Parameter index) offset
      LMeta index -> Map.singleton (Meta index) offset
      LSucc inner -> collect (offset + 1) inner
      LMax left right -> Map.unionWith max (collect offset left) (collect offset right)

satisfiable :: [Constraint] -> Bool
satisfiable constraints = isJust (solve (constraintAtoms constraints) (constraintClauses constraints) [])

-- constraints with an assignment that satisfieth them, when one is known. a
-- new constraint that the assignment already satisfieth keepeth it, so only a
-- constraint that contradicteth the current assignment re-solveth the set.
data Universes = Universes [Constraint] (Maybe (Map.Map Atom Integer))

universeConstraints :: Universes -> [Constraint]
universeConstraints (Universes constraints _) = constraints

universes :: [Constraint] -> Universes
universes constraints = Universes constraints Nothing

-- 'Nothing' when the extended set is unsatisfiable.
constrain :: Constraint -> Universes -> Maybe Universes
constrain constraint (Universes constraints witness)
  | Just assignment <- witness, holds assignment constraint = Just (Universes next witness)
  | otherwise = Universes next . Just <$> solve (constraintAtoms next) (constraintClauses next) []
  where
    next = constraint : constraints

-- an atom the assignment doth not mention taketh the value of zero, which keepeth
-- every other constraint satisfied.
holds :: Map.Map Atom Integer -> Constraint -> Bool
holds assignment = \case
  LevelBelow left right -> value left <= value right
  LevelEqual left right -> value left == value right
  where
    base = Map.findWithDefault 0 Zero assignment
    value level = maximum [Map.findWithDefault base atom assignment + offset | (atom, offset) <- Map.toList (levelAtoms level)]

-- exact tautologies for natural levels: a variable-plus-offset atom requireth
-- the same variable at least as high on the right. a constant requireth an
-- offset at least as high, since every variable is nonnegative. an unmatched
-- variable can grow beyond every other atom, so no further case is universal.
trivial :: Constraint -> Bool
trivial = \case
  LevelBelow left right -> below left right
  LevelEqual left right -> below left right && below right left
  where
    below left right =
      let rightAtoms = levelAtoms right
       in and [maybe (atom == Zero && any (>= offset) (Map.elems rightAtoms)) (>= offset) (Map.lookup atom rightAtoms) | (atom, offset) <- Map.toList (levelAtoms left)]

entails :: [Constraint] -> Constraint -> Bool
entails assumptions conclusion =
  not (any (isJust . solve atoms clauses) (negatedBranches conclusion))
  where
    atoms = constraintAtoms (conclusion : assumptions)
    clauses = constraintClauses assumptions

constraintAtoms :: [Constraint] -> Set.Set Atom
constraintAtoms constraints = Set.fromList (Zero : concatMap atoms constraints)
  where
    atoms constraint = concatMap (Map.keys . levelAtoms) (constraintLevels constraint)

-- max(left) <= max(right) holdeth iff each left atom is below some right atom.
-- each clause chooseth one difference edge; no finite bound on universes is assumed.
constraintClauses :: [Constraint] -> [[Edge]]
constraintClauses = List.sortOn length . Set.toList . Set.fromList . mapMaybe simplify . concatMap clauses
  where
    clauses = \case
      LevelBelow left right -> below left right
      LevelEqual left right -> below left right ++ below right left
    below left right =
      [ [Edge rightAtom leftAtom (rightOffset - leftOffset) | (rightAtom, rightOffset) <- Map.toList (levelAtoms right)]
      | (leftAtom, leftOffset) <- Map.toList (levelAtoms left)
      ]
    simplify edges
      | any tautology edges = Nothing
      | otherwise = Just (Set.toList (Set.fromList [edge | edge@(Edge source target _) <- edges, source /= target]))
    tautology (Edge source target weight) = source == target && weight >= 0

-- negating <= selecteth a left atom strictly above every right atom.
-- integer strictness is represented exactly by subtracting one from the offset.
negatedBranches :: Constraint -> [[Edge]]
negatedBranches = \case
  LevelBelow left right -> above left right
  LevelEqual left right -> above left right ++ above right left
  where
    above left right =
      [ [Edge leftAtom rightAtom (leftOffset - rightOffset - 1) | (rightAtom, rightOffset) <- Map.toList (levelAtoms right)]
      | (leftAtom, leftOffset) <- Map.toList (levelAtoms left)
      ]

-- single-edge clauses are fixed before the search. a clause that the current
-- solution already satisfieth is tried first, which keepeth that solution and
-- needeth no new pass; every alternative is still tried on failure.
solve :: Set.Set Atom -> [[Edge]] -> [Edge] -> Maybe (Map.Map Atom Integer)
solve atoms clauses initial = case potentials atoms fixed of
  Nothing -> Nothing
  Just solution -> search solution fixed choices
  where
    (units, choices) = List.partition ((== 1) . length) clauses
    -- shifting a solution so Zero = 0 then maketh every other atom a natural.
    nonnegative = [Edge atom Zero 0 | atom <- Set.toList atoms, atom /= Zero]
    fixed = initial ++ nonnegative ++ concat units
    search solution _ [] = Just solution
    search solution edges (alternatives : rest) =
      let (kept, others) = List.partition (satisfied solution) alternatives
       in asum ([search solution (edge : edges) rest | edge <- take 1 kept] ++ map (extend edges rest) (drop 1 kept ++ others))
    extend edges rest edge = case potentials atoms (edge : edges) of
      Just solution -> search solution (edge : edges) rest
      Nothing -> Nothing
    satisfied solution (Edge source target weight) =
      Map.findWithDefault 0 target solution <= Map.findWithDefault 0 source solution + weight

-- bellman-ford starteth every vertex at zero, equivalent to a fresh source.
-- the distances solve every edge; a change on the nth pass proveth a negative
-- cycle, and integer weights give integral solutions.
potentials :: Set.Set Atom -> [Edge] -> Maybe (Map.Map Atom Integer)
potentials atoms edges = passes (Set.size atoms + 1) (Map.fromSet (const 0) atoms)
  where
    passes 0 _ = Nothing
    passes count distances =
      let (next, changed) = List.foldl' relax (distances, False) edges
       in if changed then passes (count - 1) next else Just next
    relax (distances, changed) (Edge source target weight) =
      let candidate = Map.findWithDefault 0 source distances + weight
       in if candidate < Map.findWithDefault 0 target distances
            then (Map.insert target candidate distances, True)
            else (distances, changed)

instantiateConstraint :: [Level] -> Constraint -> Either String Constraint
instantiateConstraint arguments constraint = do
  mapM_ checkArgument arguments
  case constraint of
    LevelEqual left right -> LevelEqual <$> replace left <*> replace right
    LevelBelow left right -> LevelBelow <$> replace left <*> replace right
  where
    replace level = normaliseLevel <$> instantiateLevel arguments level
    checkArgument = \case
      LParam index | index < 0 -> Left "unbound universe parameter"
      LMeta index | index < 0 -> Left "unresolved universe inference hole"
      LSucc level -> checkArgument level
      LMax left right -> checkArgument left >> checkArgument right
      _ -> Right ()
