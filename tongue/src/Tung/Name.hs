-- | pure helpers for import namespaces and qualification.
module Tung.Name
  ( importAlias,
    importNamespace,
    lastQualifiedSegment,
  )
where

import Data.Maybe (fromMaybe)
import System.FilePath (stripExtension, takeFileName)

importNamespace :: String -> String
importNamespace path = fromMaybe path (stripExtension ".tung" path)

importAlias :: String -> Maybe String -> String
importAlias path = fromMaybe (takeWhile (/= '.') (takeFileName path))

splitQualifiedName :: String -> Maybe (String, String)
splitQualifiedName name = case break (== '~') (reverse name) of
  (member, '~' : namespace)
    | not (null namespace) && not (null member) ->
        Just (reverse namespace, reverse member)
  _ -> Nothing

lastQualifiedSegment :: String -> String
lastQualifiedSegment name = case break (== '@') (reverse name) of
  (member, '@' : _) | not (null member) -> reverse member
  _ -> maybe name snd (splitQualifiedName name)
