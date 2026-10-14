-- | natural-number universes with successor, maximum, and exact constraints.
module Tung.Dependent.Universe
  ( normaliseLevel,
    satisfiable,
    satisfy,
    Universes,
    universes,
    universeConstraints,
    hasConstraint,
    constrain,
    trivial,
    entails,
    entailsAll,
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
satisfiable = isJust . satisfy

-- constraints with an assignment that satisfieth them, when one is known. a
-- new constraint that the assignment already satisfieth keepeth it, so only a
-- constraint that contradicteth the current assignment re-solveth the set.
-- the set answereth membership; the list keepeth insertion order. atoms and
-- simplified clauses grow with each constraint, since simplification is per
-- clause. a violated constraint first extendeth the last solution and its
-- edges; only when that faileth is the whole set searched again.
data Universes = Universes
  { universeConstraints :: [Constraint],
    universeKnown :: Set.Set Constraint,
    universeAtoms :: Set.Set Atom,
    universeClauses :: Set.Set [Edge],
    universeWitness :: Maybe Solution
  }

-- an assignment and the difference edges it was built on.
type Solution = (Map.Map Atom Integer, [Edge])

hasConstraint :: Constraint -> Universes -> Bool
hasConstraint constraint = Set.member constraint . universeKnown

universes :: [Constraint] -> Universes
universes constraints = Universes constraints (Set.fromList constraints) (constraintAtoms constraints) (Set.fromList (constraintClauses constraints)) Nothing

-- checking an initial set retaineth its witness for the following judgement.
satisfy :: [Constraint] -> Maybe Universes
satisfy constraints = resolve (universes constraints)

resolve :: Universes -> Maybe Universes
resolve current@Universes {..} = (\solution -> current {universeWitness = Just solution}) <$> solveFrom (maybe Map.empty fst universeWitness) universeAtoms (List.sortOn length (Set.toList universeClauses)) []

-- 'Nothing' when the extended set is unsatisfiable.
constrain :: Constraint -> Universes -> Maybe Universes
constrain constraint current@Universes {..}
  | Just (assignment, _) <- universeWitness, holds assignment constraint = Just added
  | Just solution <- universeWitness >>= extend = Just added {universeWitness = Just solution}
  | otherwise = resolve added
  where
    atoms = constraintAtoms [constraint]
    clauses = constraintClauses [constraint]
    added =
      current
        { universeConstraints = constraint : universeConstraints,
          universeKnown = Set.insert constraint universeKnown,
          universeAtoms = Set.union universeAtoms atoms,
          universeClauses = allClauses
        }
    allClauses = Set.union universeClauses (Set.fromList clauses)
    -- the new single edges join the last solution's edges, and every clause
    -- of several alternatives is searched from that solution.
    extend (assignment, edges) = do
      let fixed = [Edge atom Zero 0 | atom <- Set.toList atoms, atom /= Zero] ++ concat [clause | clause@[_] <- clauses] ++ edges
      solution <- potentials (Map.union assignment (Map.fromSet (const 0) atoms)) fixed
      search solution fixed (List.sortOn length [clause | clause <- Set.toList allClauses, length clause /= 1])

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
entails assumptions conclusion = entailsAll assumptions [conclusion]

-- a declaration's obligations share the same assumptions. prepare their clauses
-- once; each conclusion addeth only its own atoms and negated edges.
entailsAll :: [Constraint] -> [Constraint] -> Bool
entailsAll assumptions conclusions = all entailed conclusions
  where
    atoms = constraintAtoms assumptions
    clauses = constraintClauses assumptions
    entailed conclusion = all proved (constraintClauses [conclusion])
      where
        allAtoms = Set.union atoms (constraintAtoms [conclusion])
        proved target =
          any (`impliesClause` target) clauses
            || not (isJust (solveFrom Map.empty allAtoms clauses (map negateEdge target)))
    -- a premise disjunction implieth a target when every premise alternative
    -- hath a weaker target edge. uncovered clauses still use the exact solver.
    impliesClause premise target = all (\edge -> any (weaker edge) target) premise
    weaker (Edge source target weight) (Edge source' target' weight') =
      source == source' && target == target' && weight <= weight'
    -- integer strictness reverseth the edge and subtracteth one from its bound.
    negateEdge (Edge source target weight) = Edge target source (-weight - 1)

constraintAtoms :: [Constraint] -> Set.Set Atom
constraintAtoms constraints = Set.fromList (Zero : concatMap atoms constraints)
  where
    atoms constraint = concatMap (Map.keys . levelAtoms) (constraintLevels constraint)

-- max(left) <= max(right) holdeth iff each left atom is below some right atom.
-- each clause chooseth one difference edge; no finite bound on universes is assumed.
constraintClauses :: [Constraint] -> [[Edge]]
constraintClauses = simplifyClauses . concatMap clauses
  where
    clauses = \case
      LevelBelow left right -> below left right
      LevelEqual left right -> below left right ++ below right left
    below left right =
      [ [Edge rightAtom leftAtom (rightOffset - leftOffset) | (rightAtom, rightOffset) <- Map.toList (levelAtoms right)]
      | (leftAtom, leftOffset) <- Map.toList (levelAtoms left)
      ]

-- a self-edge is either a tautology or an impossible alternative. an empty
-- clause stayeth empty, since no choice can satisfy it.
simplifyClauses :: [[Edge]] -> [[Edge]]
simplifyClauses = List.sortOn length . Set.toList . Set.fromList . mapMaybe simplify
  where
    simplify edges
      | any tautology edges = Nothing
      | otherwise = Just (Set.toList (Set.fromList [edge | edge@(Edge source target _) <- edges, source /= target]))
    tautology (Edge source target weight) = source == target && weight >= 0

-- single-edge clauses are fixed first. branch on a shortest violated clause;
-- unchosen clauses stay available, since a later solution may invalidate one
-- that holdeth now. every alternative is still tried on failure. a seed only
-- starteth the search nearer a solution; feasibility doth not depend on it.
solveFrom :: Map.Map Atom Integer -> Set.Set Atom -> [[Edge]] -> [Edge] -> Maybe Solution
solveFrom seed atoms clauses initial = do
  solution <- potentials (Map.union (Map.restrictKeys seed atoms) (Map.fromSet (const 0) atoms)) fixed
  search solution fixed choices
  where
    (units, choices) = List.partition ((== 1) . length) clauses
    -- shifting a solution so Zero = 0 then maketh every other atom a natural.
    nonnegative = [Edge atom Zero 0 | atom <- Set.toList atoms, atom /= Zero]
    fixed = initial ++ nonnegative ++ concat units

-- branch on the first violated clause; a clause no alternative can satisfy
-- endeth the branch.
search :: Map.Map Atom Integer -> [Edge] -> [[Edge]] -> Maybe Solution
search solution edges remaining =
  case List.break (not . any (satisfied solution)) remaining of
    (_, []) -> Just (solution, edges)
    (before, alternatives : after)
      | any impossible remaining -> Nothing
      | otherwise -> asum (map (extend (before ++ after)) alternatives)
  where
    impossible alternatives =
      not (any (satisfied solution) alternatives)
        && all (not . isJust . potentials solution . (: edges)) alternatives
    extend rest edge = potentials solution (edge : edges) >>= \next -> search next (edge : edges) rest
    satisfied assignment (Edge source target weight) =
      Map.findWithDefault 0 target assignment <= Map.findWithDefault 0 source assignment + weight

-- bellman-ford starteth with finite distances for every vertex: zero for the
-- initial graph, or its existing solution when adding an edge. each seed is
-- equivalent to weighted edges from a fresh source. a change on the nth pass
-- proveth a negative cycle; integer weights give integral solutions.
potentials :: Map.Map Atom Integer -> [Edge] -> Maybe (Map.Map Atom Integer)
potentials initial edges = passes (Map.size initial + 1) initial
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

-- the arguments are checked and indexed once per partial application.
instantiateConstraint :: [Level] -> Constraint -> Either String Constraint
instantiateConstraint arguments = \constraint -> do
  checked
  case constraint of
    LevelEqual left right -> LevelEqual <$> replace left <*> replace right
    LevelBelow left right -> LevelBelow <$> replace left <*> replace right
  where
    checked = mapM_ checkArgument arguments
    instantiate = instantiateLevel arguments
    replace level = normaliseLevel <$> instantiate level
    checkArgument = \case
      LParam index | index < 0 -> Left "unbound universe parameter"
      LMeta index | index < 0 -> Left "unresolved universe inference hole"
      LSucc level -> checkArgument level
      LMax left right -> checkArgument left >> checkArgument right
      _ -> Right ()
