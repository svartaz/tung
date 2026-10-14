-- | source-facing display of checked terms. primitive projections recover
-- their declared names from the receiver's type; conversion keepeth the core.
module Tung.Dependent.Source.Render (renderTermIn) where

import Control.Monad.Trans.State.Strict (evalStateT)
import Data.Functor.Identity (Identity (..))
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Tung.Dependent.Check qualified as K
import Tung.Dependent.Normalise qualified as N
import Tung.Dependent.Render (renderTermWith)
import Tung.Dependent.Syntax
import Tung.Dependent.Universe qualified as U
import Tung.Identity (SymbolId (..))

-- partially apply the globals and names once to share the accessor index
-- across a batch of goals or proof dependencies. failed or unnamed projections
-- keep their core spelling; display never changeth a typing result.
renderTermIn :: Globals -> (SymbolId -> String) -> K.Context -> [String] -> Term -> String
renderTermIn globals display = \context names term -> renderTermWith display names (walk (Just context) term)
  where
    accessors =
      Map.fromList
        [ ((symbol {symbolName = family}, index), symbol)
        | (symbol, Definition {definitionBody = Transparent body}) <- Map.toList globals,
          (family, '.' : field) <- [break (== '.') (symbolName symbol)],
          not (null family),
          not (null field),
          Field index (Local 0) <- [result body]
        ]
    result (Lambda _ _ body) = result body
    result term = term
    typed = either (const Nothing) Just . (`evalStateT` U.universes [])
    walk context = \case
      Pi plicity domain codomain -> Pi plicity (walk context domain) (walk (under context domain) codomain)
      Lambda plicity domain body -> Lambda plicity (walk context domain) (walk (under context domain) body)
      Let annotation value body ->
        let inner = do
              current <- context
              ty <- typed (K.evaluate globals current annotation)
              worth <- typed (K.evaluate globals current value)
              pure (K.Context (worth : K.contextValues current) (ty : K.contextTypes current))
         in Let (walk context annotation) (walk context value) (walk inner body)
      Field index value ->
        let receiver = walk context value
         in fromMaybe (Field index receiver) do
              current <- context
              ty <- typed (K.inferTerm globals current value)
              N.VNeutral neutral <- either (const Nothing) Just (N.forceWith (N.closed globals) ty)
              let (head, arguments) = N.neutralSpine neutral
              N.NGlobal family levels <- pure head
              accessor <- Map.lookup (family, index) accessors
              arguments' <- traverse (either (const Nothing) Just . N.quoteFoldedWith (N.closed globals) (K.contextDepth current) . snd) arguments
              pure (Apply Explicit (foldl (Apply Implicit) (Global accessor levels) arguments') receiver)
      term -> runIdentity (mapChildren (\_ -> Identity . walk context) term)
    -- the context is forced only at a projection, so ordinary display doth
    -- not evaluate binder domains or build the accessor index.
    under context domain = do
      current <- context
      K.bind current <$> typed (K.evaluate globals current domain)
