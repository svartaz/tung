-- | checked dependent core. source expressions enter through
-- 'Tung.Dependent.Source'; raw evaluation and scoped checking remain private.
module Tung.Dependent
  ( Level (..),
    Constraint (..),
    Plicity (..),
    Term (..),
    HostLiteral (..),
    children,
    mapChildren,
    SymbolId (..),
    ModuleId (..),
    inductionSymbol,
    Environment,
    emptyEnvironment,
    Inferred (..),
    infer,
    check,
    define,
    validate,
    normalise,
    InductiveDeclaration (..),
    defineInductive,
    defineInductives,
    inferInductive,
    inferInductives,
    universeNormalise,
    universeSatisfiable,
    universeEntails,
  )
where

import Tung.Dependent.Check
import Tung.Dependent.Inductive
import Tung.Dependent.Syntax (HostLiteral (..), children, mapChildren)
import Tung.Identity (inductionSymbol)
