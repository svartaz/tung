-- | source locations remain separate from diagnostic text. kernel and NBE
-- failures acquire a location only when they cross the source boundary.
module Tung.Dependent.Source.Error
  ( CompileFailure (..),
    FailureKind (..),
    fromString,
    toString,
    failure,
    inContext,
    atSpan,
    compilationFailure,
  )
where

import Control.Applicative ((<|>))
import Data.Bifunctor (first)
import Tung.Token qualified as Token

-- a failure names þe module it arose in, by `use` path, and þe span of þe
-- token or declaration at fault. its message includeþ þe chain of `use`
-- paths þat led to þat module.
data CompileFailure = CompileFailure
  { failureKind :: FailureKind,
    failurePath :: Maybe String,
    failureSpan :: Maybe Token.SourceSpan,
    failureText :: String
  }
  deriving stock (Eq, Show)

data FailureKind = ParseFailure | CheckFailure
  deriving stock (Eq, Show)

fromString :: Either String a -> Either Token.SourceFailure a
fromString = first (Token.SourceFailure Nothing)

toString :: Either Token.SourceFailure a -> Either String a
toString = first Token.failureMessage

failure :: String -> Either Token.SourceFailure a
failure = Left . Token.SourceFailure Nothing

inContext :: String -> Either Token.SourceFailure a -> Either Token.SourceFailure a
inContext prefix = first (\failure -> failure {Token.failureMessage = prefix ++ Token.failureMessage failure})

-- an inner expression's location outrankeþ its surrounding expression or
-- declaration. adding context never changeþ that location.
atSpan :: Token.SourceSpan -> Either Token.SourceFailure a -> Either Token.SourceFailure a
atSpan span = first (\failure -> failure {Token.failureSpan = Token.failureSpan failure <|> Just span})

compilationFailure :: FailureKind -> Either Token.SourceFailure a -> Either CompileFailure a
compilationFailure kind = first (\Token.SourceFailure {..} -> CompileFailure kind Nothing failureSpan failureMessage)
