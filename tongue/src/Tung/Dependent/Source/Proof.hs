-- | assumption auditing over checked declarations. imports and cached
-- interfaces carry the core graph and resolved checking references, so no
-- source-level name search is needed.
module Tung.Dependent.Source.Proof
  ( DependencyKind (..),
    ProofDependency (..),
    ProofAudit,
    auditName,
    auditType,
    auditDependencies,
    auditProof,
    verifyProof,
  )
where

import Control.Monad (unless)
import Data.List (intercalate, sortOn)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Source.Environment
import Tung.Dependent.Source.Render (renderTermIn)
import Tung.Dependent.Syntax
import Tung.Identity (ModuleId (..), SymbolId (..))

data DependencyKind = SorryDependency | AxiomDependency | HostDependency String
  deriving stock (Eq, Ord, Show)

data ProofDependency = ProofDependency
  { dependencySymbol :: SymbolId,
    dependencyName :: String,
    dependencyType :: String,
    dependencyKind :: DependencyKind
  }
  deriving stock (Eq, Show)

-- construction stayeth private, including record labels: callers cannot
-- certify an unfinished declaration by replacing its dependency list.
data ProofAudit = ProofAudit String String [ProofDependency]
  deriving stock (Eq, Show)

auditName :: ProofAudit -> String
auditName (ProofAudit name _ _) = name

auditType :: ProofAudit -> String
auditType (ProofAudit _ ty _) = ty

auditDependencies :: ProofAudit -> [ProofDependency]
auditDependencies (ProofAudit _ _ dependencies) = dependencies

-- the closure is deliberately syntactic: unused imported declarations are
-- excluded, but a referenced dictionary retaineth every field, and an
-- inductive family retaineth its whole checked group and computation rules.
-- checking references retain inputs erased by normalisation. inspecting both
-- types and bodies also findeth holes hidden in annotations.
auditProof :: SourceProgram -> String -> Either String ProofAudit
auditProof program@SourceProgram {globalNames} name = do
  symbol <- resolve program name
  definition <- findDefinition symbol
  reached <- walk Set.empty [symbol]
  let dependencies =
        [ ProofDependency identity (label identity) (render (definitionType entry)) kind
        | identity <- Set.toList reached,
          Just entry <- [Map.lookup identity definitions],
          Just kind <- [dependency (definitionBody entry)]
        ]
  pure (ProofAudit name (render (definitionType definition)) (sortOn ordering dependencies))
  where
    definitions = globals (sourceEnvironment program)
    visible = Set.fromList [symbol | binding <- Map.elems (nameTable globalNames), Just symbol <- [bindingSymbol binding]]
    render = renderTermIn definitions (displayName globalNames) K.emptyContext []
    findDefinition symbol = maybe (Left ("missing checked definition '" ++ label symbol ++ "'")) Right (Map.lookup symbol definitions)
    walk seen [] = Right seen
    walk seen (symbol : rest)
      | Set.member symbol seen = walk seen rest
      | otherwise = do
          definition <- findDefinition symbol
          walk (Set.insert symbol seen) (definitionReferences definition ++ Set.toList (Map.findWithDefault Set.empty symbol (programReferences program)) ++ rest)
    dependency = \case
      Assumption -> Just AxiomDependency
      Host "sorry" _ -> Just SorryDependency
      Host key _ -> Just (HostDependency key)
      _ -> Nothing
    -- private transitive names need provenance even when a visible name in
    -- another module hath the same spelling. aliases resolve by identity.
    label symbol
      | Set.member symbol visible = displayName globalNames symbol
      | otherwise = case symbolModule symbol of
          SourceModule path -> path ++ "::" ++ symbolName symbol
          _ -> symbolName symbol
    ordering ProofDependency {..} = (dependencyKind, dependencyName, symbolModule dependencySymbol, symbolName dependencySymbol)

-- a missing policy alloweth named axioms. an explicit policy is resolved in
-- the root namespace, then compared by nominal identity, never by basename.
-- host operations are reported trust dependencies, not unfinished proofs.
verifyProof :: SourceProgram -> Maybe [String] -> ProofAudit -> Either String ()
verifyProof program allowed audited = do
  permitted <- traverse (fmap Set.fromList . traverse allow) allowed
  let problems =
        [ case dependencyKind of
            SorryDependency -> "unfinished proof: " ++ dependencyName
            _ -> "axiom is not allowed: " ++ dependencyName
        | ProofDependency {..} <- auditDependencies audited,
          case dependencyKind of
            SorryDependency -> True
            AxiomDependency -> maybe False (Set.notMember dependencySymbol) permitted
            HostDependency _ -> False
        ]
  unless (null problems) (Left (intercalate "\n" problems))
  where
    allow name = do
      symbol <- resolve program name
      case Map.lookup symbol (globals (sourceEnvironment program)) of
        Just Definition {definitionBody = Assumption} -> Right symbol
        _ -> Left ("allowed axiom '" ++ name ++ "' is not an orsetting")

resolve :: SourceProgram -> String -> Either String SymbolId
resolve SourceProgram {globalNames} name = case lookupName name globalNames of
  Just (AmbiguousName namespaces) -> Left (ambiguousName name namespaces)
  binding -> maybe (Left ("unknown name '" ++ name ++ "'")) Right (binding >>= bindingSymbol)

definitionReferences :: Definition -> [SymbolId]
definitionReferences Definition {definitionType, definitionBody} = termReferences definitionType ++ body definitionBody
  where
    body = \case
      Transparent term -> termReferences term
      Host _ model -> maybe [] (: []) model
      TypeConstructor info -> metadata info
      EliminationTarget info term -> termReferences term ++ metadata info
      DataConstructor family _ -> [family]
      Eliminator family -> [family]
      Assumption -> []
    metadata InductiveInfo {..} =
      inductiveFamilies
        ++ concat [constructor : concat [termReferences ty ++ maybe [] (: []) recursive | (_, ty, recursive) <- fields] | (constructor, fields) <- inductiveConstructorInfo]
        ++ concatMap termReferences inductiveRules

termReferences :: Term -> [SymbolId]
termReferences = \case
  Global symbol _ -> [symbol]
  Literal symbol _ -> [symbol]
  term -> concatMap (termReferences . snd) (children term)
