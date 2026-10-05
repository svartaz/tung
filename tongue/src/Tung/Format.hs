-- | authoritative two-space formatting for the cli and editor. the formatter
-- is structural so comments and incomplete source survive without parsing or
-- type checking; formatting is idempotent.
module Tung.Format (formatSource) where

import Data.Char (isDigit, isSpace)
import Data.List (dropWhileEnd, intercalate, isPrefixOf, isSuffixOf, mapAccumL, sortOn, stripPrefix)

data FormatState = FormatState
  { formatDepth :: !Int,
    formatLexicalState :: !LexicalState,
    formatContinuation :: !Int,
    formatContinuationBlocks :: ![(Int, Int)],
    -- structural base depth and unmatched square brackets in a split header.
    formatHeaderBracket :: !(Maybe (Int, Int))
  }

data LexicalState = Code | Text | BlockComment

formatSource :: String -> String
formatSource source =
  let (_, formatted) = mapAccumL formatLine initialState (sortUseBlocks (sourceLines source))
      result = intercalate "\n" formatted
   in if "\n" `isSuffixOf` source
        then dropWhileEnd (== '\n') result ++ "\n"
        else result

initialState :: FormatState
initialState = FormatState 0 Code 0 [] Nothing

sortUseBlocks :: [String] -> [String]
sortUseBlocks = go Code
  where
    go _ [] = []
    go Code lines'@(line : rest)
      | sortableUseLine line =
          let (uses, remaining) = span sortableUseLine lines'
           in sortOn trim uses ++ go Code remaining
      | otherwise = line : go (lineLexicalState Code line) rest
    go lexicalState (line : rest) = line : go (lineLexicalState lexicalState line) rest

    sortableUseLine line =
      let content = trim line
       in startsWord "use" content && case lineLexicalState Code content of
            Code -> True
            _ -> False

lineLexicalState :: LexicalState -> String -> LexicalState
lineLexicalState lexicalState line =
  let (_, _, next, _) = scanLine lexicalState line
   in next

formatLine :: FormatState -> String -> (FormatState, String)
formatLine state@FormatState {formatLexicalState = BlockComment} line =
  let (_, _, lexicalState, _) = scanLine BlockComment line
   in (state {formatLexicalState = lexicalState}, line)
formatLine state line
  | null content =
      let continuation = case formatHeaderBracket state of
            Just (base, count) -> max 0 (count - (formatDepth state - base))
            Nothing -> 0
       in (state {formatContinuation = continuation}, "")
  | otherwise =
      let closes = leadingClosures content
          startsDeclaration = declarationHead content
          startsComment = commentHead content
          lineContinuation
            | closes > 0 || startsDeclaration || startsComment = 0
            | formatHeaderBracket state /= Nothing && "]" `isPrefixOf` content = max 0 (formatContinuation state - 1)
            -- a top-level line þat is no declaration head continueþ þe
            -- previous declaration, as a body after `] ≔ {...}` doþ.
            | formatDepth state == 0 && formatHeaderBracket state == Nothing && not ("]" `isPrefixOf` content) = max 1 (formatContinuation state)
            | otherwise = formatContinuation state
          lineDepth = max 0 (formatDepth state - closes + lineContinuation)
          (delta, bracketDelta, lexicalState, code) = scanLine (formatLexicalState state) content
          oldDepth = formatDepth state
          -- a continued line opening a block keepeþ its continuation, unless
          -- it closeþ a header bracket, as `@a:*, head] {` doth.
          continuedBlock = lineContinuation > 0 && delta > 0 && not headerClosed
          balancedDepth = max 0 (oldDepth + delta + if continuedBlock then lineContinuation else 0)
          blocks =
            if continuedBlock
              then (oldDepth + lineContinuation, lineContinuation) : formatContinuationBlocks state
              else formatContinuationBlocks state
          (depth, remainingBlocks) = if delta < 0 then releaseBlocks balancedDepth blocks else (balancedDepth, blocks)
          headerBracket = case formatHeaderBracket state of
            Just (base, count) | count + bracketDelta > 0 -> Just (base, count + bracketDelta)
            Just _ -> Nothing
            Nothing
              | bracketDelta > 0
                  && any (`startsHead` code) ["let", "show let", "bizen", "flock", "show flock"]
                  && '≔' `notElem` code ->
                  Just (oldDepth, bracketDelta)
            Nothing -> Nothing
          headerClosed = case formatHeaderBracket state of
            Just _ -> headerBracket == Nothing
            Nothing -> False
          continuation
            | startsComment = formatContinuation state
            | headerClosed = if any (`isSuffixOf` code) ["]", "≔"] then 1 else 0
            | Just (base, count) <- headerBracket = max 0 (count - (depth - base))
            | "≔" `isSuffixOf` code = 1
            | closes > 0 = 0
            -- a trailing comma endeþ a row or item, and wiþ it its continuation.
            | "," `isSuffixOf` code = 0
            | delta == 0 && lineContinues code (lineContinuation > 0) = 1
            | lineContinuation > 0 && delta == 0 = max 2 lineContinuation
            | otherwise = 0
          next = FormatState depth lexicalState continuation remainingBlocks headerBracket
       in (next, replicate (lineDepth * 2) ' ' ++ content)
  where
    content = compactTypeColons (formatLexicalState state) (trim line)

-- ':' introduceth a type. it is written wiþ no space before it and one space
-- after it: `x: α`, or none when þe type is left to inference: `[x:, y:]`. retain quoted text, character literals, and comments byte
-- for byte.
compactTypeColons :: LexicalState -> String -> String
compactTypeColons started = reverse . go started []
  where
    go _ acc [] = acc
    go BlockComment acc ('*' : '/' : rest) = go Code ('/' : '*' : acc) rest
    go BlockComment acc (character : rest) = go BlockComment (character : acc) rest
    go Text acc ('\\' : character : rest) = go Text (character : '\\' : acc) rest
    go Text acc ('\'' : rest) = go Code ('\'' : acc) rest
    go Text acc (character : rest) = go Text (character : acc) rest
    go Code acc ('#' : rest) = reverse rest ++ '#' : acc
    go Code acc ('/' : '*' : rest) = go BlockComment ('*' : '/' : acc) rest
    go Code acc ('\'' : rest) = go Text ('\'' : acc) rest
    go Code acc ('`' : rest) =
      let remaining = characterLiteralTail rest
          literal = take (length rest - length remaining) rest
       in go Code (reverse literal ++ '`' : acc) remaining
    go Code acc (':' : rest) = case dropWhile isSpace rest of
      [] -> ':' : dropWhile isSpace acc
      -- `a:` before `,` or `]` leaveþ þe type to inference and needeþ no space.
      following@(next : _) | next `elem` ",]" -> go Code (':' : dropWhile isSpace acc) following
      following -> go Code (' ' : ':' : dropWhile isSpace acc) following
    go Code acc (character : rest) = go Code (character : acc) rest

releaseBlocks :: Int -> [(Int, Int)] -> (Int, [(Int, Int)])
releaseBlocks depth blocks@((closingDepth, extraDepth) : rest)
  | closingDepth == depth = releaseBlocks (max 0 (depth - extraDepth)) rest
  | otherwise = (depth, blocks)
releaseBlocks depth [] = (depth, [])

sourceLines :: String -> [String]
sourceLines = map (dropWhileEnd (== '\r')) . lines

trim :: String -> String
trim = dropWhile isSpace . dropWhileEnd isSpace

leadingClosures :: String -> Int
leadingClosures = length . takeWhile (`elem` ("})" :: String))

declarationHead :: String -> Bool
declarationHead line = any (`startsHead` line) ["use", "yield", "show", "let", "ilk", "flock", "bizen"]

commentHead :: String -> Bool
commentHead line = "#" `isPrefixOf` line || "/*" `isPrefixOf` line

-- a declaration keyword is followed by a space or, for `bizen`, ':'.
startsHead :: String -> String -> Bool
startsHead word line = startsWord word line || (word ++ ":") `isPrefixOf` line

startsWord :: String -> String -> Bool
startsWord word line = case stripPrefix word line of
  Just [] -> True
  Just (next : _) -> isSpace next
  Nothing -> False

-- a line ending in `≔` or a row's `^` continueþ on þe next line.
lineContinues :: String -> Bool -> Bool
lineContinues code continued =
  "≔" `isSuffixOf` code
    || "^" `isSuffixOf` code
    || (continued && ":" `isPrefixOf` code)

scanLine :: LexicalState -> String -> (Int, Int, LexicalState, String)
scanLine started input =
  let (delta, bracketDelta, lexicalState, reversedCode) = go 0 0 started True [] input
   in (delta, bracketDelta, lexicalState, dropWhileEnd isSpace (reverse reversedCode))
  where
    go delta bracketDelta lexicalState _ code [] = (delta, bracketDelta, lexicalState, code)
    go delta bracketDelta BlockComment collect code ('*' : '/' : rest) = go delta bracketDelta Code collect code rest
    go delta bracketDelta BlockComment collect code (_ : rest) = go delta bracketDelta BlockComment collect code rest
    go delta bracketDelta Text collect code ('\\' : _ : rest) = go delta bracketDelta Text collect code rest
    go delta bracketDelta Text collect code ('\'' : rest) = go delta bracketDelta Code collect code rest
    go delta bracketDelta Text collect code (_ : rest) = go delta bracketDelta Text collect code rest
    go delta bracketDelta Code _ code ('#' : _) = (delta, bracketDelta, Code, code)
    go delta bracketDelta Code _ code ('/' : '*' : rest) = go delta bracketDelta BlockComment False code rest
    go delta bracketDelta Code collect code ('\'' : rest) = go delta bracketDelta Text collect code rest
    go delta bracketDelta Code collect code ('`' : rest) =
      go delta bracketDelta Code collect code (characterLiteralTail rest)
    go delta bracketDelta Code collect code (character : rest)
      | character `elem` ("{(" :: String) = go (delta + 1) bracketDelta Code collect next rest
      | character `elem` ("})" :: String) = go (delta - 1) bracketDelta Code collect next rest
      | character == '[' = go delta (bracketDelta + 1) Code collect next rest
      | character == ']' = go delta (bracketDelta - 1) Code collect next rest
      | otherwise = go delta bracketDelta Code collect next rest
      where
        next = keep character collect code

    keep character collect code = if collect then character : code else code

characterLiteralTail :: String -> String
characterLiteralTail [] = []
characterLiteralTail ('\\' : rest) = case rest of
  [] -> []
  first : remaining
    | isDigit first ->
        let (_, afterDigits) = span isDigit rest
         in case afterDigits of
              ';' : after -> after
              _ -> afterDigits
    | otherwise -> remaining
characterLiteralTail (_ : rest) = rest
