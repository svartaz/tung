{-# LANGUAGE PatternSynonyms #-}

-- | source lexer. a name containeth any non-space character not reserved by
-- 'specialNameChars'; literals and comments are consumed before name parsing.
module Tung.Token
  ( Token (TIdent, TNatural, TInteger, TFloat, TUnicode, TText, TBraceKeyword, TLet, TFix, TExport, TImport, TType, TYield, TForeign, TClass, TInstance, TMatch, TSorry, TOrsend, TInduce, TFall, TLParen, TRParen, TLBracket, TRBracket, TLBrace, TRBrace, TColon, TComma, TSemicolon, TDot, TMapsTo, TEquals, TKindStar, TDollar, TAt),
    SourceSpan (..),
    LocatedToken (..),
    Piece (..),
    PieceKind (..),
    Placement (..),
    lexPieces,
    tokenSpan,
    consumedSpan,
    SourceFailure (..),
    lexTokens,
    lexLocatedTokens,
    lexLocatedTokensDetailed,
    lexLocatedPrefix,
    keywordNames,
    specialNameChars,
    unicodeScalar,
  )
where

import Control.Applicative (many, some)
import Data.Char (chr, isSpace, ord)
import Data.IntMap.Strict qualified as IntMap
import Data.List.NonEmpty qualified as NE
import Data.Maybe (fromMaybe, isJust)
import Data.Void (Void)
import GHC.TypeLits (Natural)
import Text.Megaparsec (Parsec)
import Text.Megaparsec qualified as M
import Text.Megaparsec.Char qualified as C
import Text.Megaparsec.Char.Lexer qualified as L

data SourceSpan = SourceSpan
  { spanStart :: !Int,
    spanEnd :: !Int
  }
  deriving (Eq, Ord, Show)

data SourceFailure = SourceFailure
  { failureSpan :: Maybe SourceSpan,
    failureMessage :: String
  }
  deriving (Eq, Show)

-- every suffix of the token stream carrieth its cursor boundary. span recovery
-- never walks the remaining input, including at end of input.
data TokenCursor = TokenCursor SourceSpan Int Int

data Token = Token !(Maybe TokenCursor) !TokenKind

data TokenKind
  = KTIdent String
  | KTNatural Natural
  | KTInteger Integer
  | KTFloat Double
  | KTUnicode Char
  | KTText String
  | KTLet
  | KTFix
  | KTExport
  | KTImport
  | KTType
  | KTYield
  | KTForeign
  | KTClass
  | KTInstance
  | KTMatch
  | KTSorry
  | KTOrsend
  | KTInduce
  | KTFall
  | KTBraceKeyword String
  | KTLParen
  | KTRParen
  | KTLBracket
  | KTRBracket
  | KTLBrace
  | KTRBrace
  | KTColon
  | KTComma
  | KTSemicolon
  | KTDot
  | KTMapsTo
  | KTEquals
  | KTKindStar
  | KTDollar
  | KTAt
  deriving (Eq, Show)

instance Eq Token where
  Token _ left == Token _ right = left == right

instance Show Token where
  show (Token _ kind) = drop 1 (show kind)

pattern TIdent :: String -> Token
pattern TIdent name <- Token _ (KTIdent name)
  where
    TIdent name = Token Nothing (KTIdent name)

pattern TNatural :: Natural -> Token
pattern TNatural value <- Token _ (KTNatural value)
  where
    TNatural value = Token Nothing (KTNatural value)

pattern TInteger :: Integer -> Token
pattern TInteger value <- Token _ (KTInteger value)
  where
    TInteger value = Token Nothing (KTInteger value)

pattern TFloat :: Double -> Token
pattern TFloat value <- Token _ (KTFloat value)
  where
    TFloat value = Token Nothing (KTFloat value)

pattern TUnicode :: Char -> Token
pattern TUnicode value <- Token _ (KTUnicode value)
  where
    TUnicode value = Token Nothing (KTUnicode value)

pattern TText :: String -> Token
pattern TText value <- Token _ (KTText value)
  where
    TText value = Token Nothing (KTText value)

pattern TBraceKeyword :: String -> Token
pattern TBraceKeyword name <- Token _ (KTBraceKeyword name)
  where
    TBraceKeyword name = Token Nothing (KTBraceKeyword name)

pattern TLet, TFix, TExport, TImport, TType, TYield, TForeign, TClass, TInstance, TMatch, TSorry, TOrsend, TInduce, TFall, TLParen, TRParen, TLBracket, TRBracket, TLBrace, TRBrace, TColon, TComma, TSemicolon, TDot, TMapsTo, TEquals, TKindStar, TDollar, TAt :: Token
pattern TLet <- Token _ KTLet where TLet = Token Nothing KTLet
pattern TFix <- Token _ KTFix where TFix = Token Nothing KTFix
pattern TExport <- Token _ KTExport where TExport = Token Nothing KTExport
pattern TImport <- Token _ KTImport where TImport = Token Nothing KTImport
pattern TType <- Token _ KTType where TType = Token Nothing KTType
pattern TYield <- Token _ KTYield where TYield = Token Nothing KTYield
pattern TForeign <- Token _ KTForeign where TForeign = Token Nothing KTForeign
pattern TClass <- Token _ KTClass where TClass = Token Nothing KTClass
pattern TInstance <- Token _ KTInstance where TInstance = Token Nothing KTInstance
pattern TMatch <- Token _ KTMatch where TMatch = Token Nothing KTMatch
pattern TSorry <- Token _ KTSorry where TSorry = Token Nothing KTSorry
pattern TOrsend <- Token _ KTOrsend where TOrsend = Token Nothing KTOrsend
pattern TInduce <- Token _ KTInduce where TInduce = Token Nothing KTInduce
pattern TFall <- Token _ KTFall where TFall = Token Nothing KTFall
pattern TLParen <- Token _ KTLParen where TLParen = Token Nothing KTLParen
pattern TRParen <- Token _ KTRParen where TRParen = Token Nothing KTRParen
pattern TLBracket <- Token _ KTLBracket where TLBracket = Token Nothing KTLBracket
pattern TRBracket <- Token _ KTRBracket where TRBracket = Token Nothing KTRBracket
pattern TLBrace <- Token _ KTLBrace where TLBrace = Token Nothing KTLBrace
pattern TRBrace <- Token _ KTRBrace where TRBrace = Token Nothing KTRBrace
pattern TColon <- Token _ KTColon where TColon = Token Nothing KTColon
pattern TComma <- Token _ KTComma where TComma = Token Nothing KTComma
pattern TSemicolon <- Token _ KTSemicolon where TSemicolon = Token Nothing KTSemicolon
pattern TDot <- Token _ KTDot where TDot = Token Nothing KTDot
pattern TMapsTo <- Token _ KTMapsTo where TMapsTo = Token Nothing KTMapsTo
pattern TEquals <- Token _ KTEquals where TEquals = Token Nothing KTEquals
pattern TKindStar <- Token _ KTKindStar where TKindStar = Token Nothing KTKindStar
pattern TDollar <- Token _ KTDollar where TDollar = Token Nothing KTDollar
pattern TAt <- Token _ KTAt where TAt = Token Nothing KTAt

{-# COMPLETE TIdent, TNatural, TInteger, TFloat, TUnicode, TText, TBraceKeyword, TLet, TFix, TExport, TImport, TType, TYield, TForeign, TClass, TInstance, TMatch, TSorry, TOrsend, TInduce, TFall, TLParen, TRParen, TLBracket, TRBracket, TLBrace, TRBrace, TColon, TComma, TSemicolon, TDot, TMapsTo, TEquals, TKindStar, TDollar, TAt #-}

tokenSpan :: Token -> Maybe SourceSpan
tokenSpan (Token cursor _) = (\(TokenCursor span _ _) -> span) <$> cursor

consumedSpan :: [Token] -> [Token] -> Maybe SourceSpan
consumedSpan (Token (Just (TokenCursor (SourceSpan start _) _ finalEnd)) _ : _) rest =
  let end = case rest of
        Token (Just (TokenCursor _ previousEnd _)) _ : _ -> previousEnd
        _ -> finalEnd
   in Just (SourceSpan start end)
consumedSpan _ _ = Nothing

withoutTokenSpan :: Token -> Token
withoutTokenSpan (Token _ kind) = Token Nothing kind

data LocatedToken = LocatedToken
  { locatedSpan :: !SourceSpan,
    locatedToken :: !Token
  }
  deriving (Eq, Show)

type Lexer = Parsec Void String

lexTokens :: String -> Either String [Token]
lexTokens = fmap (map (withoutTokenSpan . locatedToken)) . lexLocatedTokens

lexLocatedTokens :: String -> Either String [LocatedToken]
lexLocatedTokens = either (Left . failureMessage) Right . lexLocatedTokensDetailed

-- the strict lexer accepteth only a source that lexeth whole; its failure
-- message cometh from the same rules run strictly.
lexLocatedTokensDetailed :: String -> Either SourceFailure [LocatedToken]
lexLocatedTokensDetailed source
  | all ((/= Unlexed) . pieceKind) pieces = Right (piecesTokens pieces)
  | otherwise = case M.parse (spaceConsumer *> many (lexeme rawTokenParser) <* M.eof) "source" source of
      Left err ->
        let offset = utf16Offsets source IntMap.! M.errorOffset (NE.head (M.bundleErrors err))
         in Left (SourceFailure (Just (SourceSpan offset offset)) (M.errorBundlePretty err))
      Right _ -> Left (SourceFailure Nothing "the lexers disagree; this is a compiler fault")
  where
    pieces = lexPieces source

-- recovery readeth the complete tokens before an unfinished literal or comment.
lexLocatedPrefix :: String -> [LocatedToken]
lexLocatedPrefix = piecesTokens . takeWhile ((/= Unlexed) . pieceKind) . lexPieces

-- every character of a source belongeth to one piece, in order, so the pieces'
-- texts join to the source. where no rule accepteth a character, the rest of
-- its line is one unlexed piece, or the rest of the source for an unfinished
-- block comment, and lexing resumeth after it.
data Piece = Piece
  { pieceSpan :: !SourceSpan,
    pieceText :: String,
    pieceKind :: PieceKind
  }
  deriving (Eq, Show)

data PieceKind = Lexeme Token | Space | Comment Placement | Unlexed
  deriving (Eq, Show)

-- a comment on the line of the token before it traileth that token; any
-- other leadeth the next token.
data Placement = Leading | Trailing
  deriving (Eq, Show)

lexPieces :: String -> [Piece]
lexPieces source = place False False (map locate raw)
  where
    raw = either (const []) id (M.parse (concat <$> many (M.try ((: []) <$> piece) M.<|> unlexed)) "source" source)
    offsets = utf16Offsets source
    offset = (offsets IntMap.!)
    locate (start, finish, kind) = Piece (SourceSpan (offset start) (offset finish)) (take (finish - start) (drop start source)) kind
    unlexed = do
      start <- M.getOffset
      _ <- M.choice [() <$ (C.string "/*" *> M.takeRest), () <$ M.anySingle <* M.takeWhileP Nothing (/= '\n')]
      finish <- M.getOffset
      pure [(start, finish, Unlexed)]
    piece = do
      start <- M.getOffset
      kind <- M.choice [Space <$ C.space1, Comment Leading <$ lineComment, Comment Leading <$ blockComment, Lexeme <$> rawTokenParser]
      finish <- M.getOffset
      pure (start, finish, kind)
    place afterToken sameLine = \case
      [] -> []
      current@Piece {pieceKind, pieceText} : others -> case pieceKind of
        Lexeme _ -> current : place True True others
        Space -> current : place afterToken (sameLine && '\n' `notElem` pieceText) others
        Comment _ | afterToken && sameLine -> current {pieceKind = Comment Trailing} : place afterToken False others
        _ -> current : place afterToken False others

-- the tokens of the pieces, each knowing the end of the token before it.
piecesTokens :: [Piece] -> [LocatedToken]
piecesTokens pieces = attach 0 [(span, token) | Piece span _ (Lexeme token) <- pieces]
  where
    finalEnd = case [span | Piece span _ (Lexeme _) <- pieces] of
      [] -> 0
      spans -> spanEnd (last spans)
    attach _ [] = []
    attach previous ((span, Token _ kind) : rest) =
      LocatedToken span (Token (Just (TokenCursor span previous finalEnd)) kind) : attach (spanEnd span) rest

utf16Offsets :: String -> IntMap.IntMap Int
utf16Offsets source = IntMap.fromList (zip [0 ..] (scanl (+) 0 (map utf16Width source)))

utf16Width :: Char -> Int
utf16Width character = if ord character > 0xffff then 2 else 1

rawTokenParser :: Lexer Token
rawTokenParser =
  M.choice
    [ TInteger <$> M.try integerParser,
      TFloat <$> M.try floatParser,
      TNatural <$> M.try naturalParser,
      unicodeLiteralParser,
      textParser,
      specialOpenParser,
      M.try nameParser,
      singleTokenParser
    ]

specialOpenParser :: Lexer Token
specialOpenParser = M.try do
  marker <- M.choice (map C.string ["<", ">"])
  _ <- C.char '{'
  pure (TBraceKeyword marker)

singleTokenParser :: Lexer Token
singleTokenParser =
  M.choice
    [ TLParen <$ C.char '(',
      TRParen <$ C.char ')',
      TLBracket <$ C.char '[',
      TRBracket <$ C.char ']',
      TLBrace <$ C.char '{',
      TRBrace <$ C.char '}',
      TColon <$ C.char ':',
      TComma <$ C.char ',',
      TSemicolon <$ C.char ';',
      TDot <$ C.char '.',
      TMapsTo <$ C.char '^',
      TEquals <$ C.char '≔',
      TDollar <$ C.char '$',
      TAt <$ C.char '@'
    ]

-- an integer literal always hath a sign: `+3`, `-3`, `+0`. unsigned digits
-- are a natural number.
integerParser :: Lexer Integer
integerParser = do
  sign <- M.choice [id <$ C.char '+', negate <$ C.char '-']
  value <- L.decimal
  M.notFollowedBy (C.char '.' *> C.digitChar)
  pure (sign value)

naturalParser :: Lexer Natural
naturalParser = do
  value <- L.decimal
  M.notFollowedBy (C.char '.' *> C.digitChar)
  pure value

floatParser :: Lexer Double
floatParser = do
  sign <- M.optional (C.char '-')
  whole <- some C.digitChar
  _ <- C.char '.'
  frac <- some C.digitChar
  pure (read (maybe "" (: []) sign ++ whole ++ "." ++ frac))

unicodeLiteralParser :: Lexer Token
unicodeLiteralParser = do
  _ <- C.char '`'
  TUnicode <$> M.choice [escapedCodePointParser, scalarCodePointParser]

textParser :: Lexer Token
textParser = TText <$> (C.char '\'' *> many textCharParser <* C.char '\'')

textCharParser :: Lexer Char
textCharParser =
  M.choice
    [ escapedCodePointParser,
      M.satisfy (\codePoint -> codePoint /= '\'' && isUnicodeScalar codePoint)
    ]

escapedCodePointParser :: Lexer Char
escapedCodePointParser = do
  _ <- C.char '\\'
  M.choice
    [ '\n' <$ C.char 'n',
      '\r' <$ C.char 'r',
      '\t' <$ C.char 't',
      '\'' <$ C.char '\'',
      '\\' <$ C.char '\\',
      decimalEscapeParser
    ]

decimalEscapeParser :: Lexer Char
decimalEscapeParser = do
  digits <- some C.digitChar
  _ <- C.char ';'
  decimalCodePoint digits

decimalCodePoint :: String -> Lexer Char
decimalCodePoint digits = maybe (fail "decimal unicode escape must name a unicode scalar value") pure (unicodeScalar (read digits))

scalarCodePointParser :: Lexer Char
scalarCodePointParser = M.satisfy isUnicodeScalar

isUnicodeScalar :: Char -> Bool
isUnicodeScalar = isJust . unicodeScalar . toInteger . ord

-- literals and native integer conversion share this scalar-value boundary.
unicodeScalar :: Integer -> Maybe Char
unicodeScalar value
  | value >= 0 && value <= 0x10ffff && (value < 0xd800 || 0xdfff < value) = Just (chr (fromInteger value))
  | otherwise = Nothing

nameParser :: Lexer Token
nameParser = do
  name <- some (M.satisfy isNameChar)
  if not (validNameQualification name)
    then fail "'~' must separate one slash-free namespace and member"
    else pure (keywordOrIdent name)

validNameQualification :: String -> Bool
validNameQualification name = case break (== '~') name of
  (_, []) -> True
  ("", "~") -> True
  (namespace, '~' : member) ->
    not (null namespace)
      && not (null member)
      && '~' `notElem` member
      && '/' `notElem` name
  _ -> False

spaceConsumer :: Lexer ()
spaceConsumer = L.space C.space1 (() <$ lineComment) (() <$ blockComment)

lineComment :: Lexer String
lineComment = C.char '#' *> M.takeWhileP Nothing (/= '\n')

blockComment :: Lexer String
blockComment = C.string "/*" *> M.manyTill M.anySingle (C.string "*/")

lexeme :: Lexer a -> Lexer a
lexeme = L.lexeme spaceConsumer

-- `deed`, the type of actions, is lexed as a name but presented as a keyword.
keywordNames :: [String]
keywordNames = map fst keywordTokens ++ ["deed"]

keywordOrIdent :: String -> Token
-- only a standalone star is kind syntax; names such as ‥ remain whole.
keywordOrIdent "*" = TKindStar
keywordOrIdent name = fromMaybe (TIdent name) (lookup name keywordTokens)

keywordTokens :: [(String, Token)]
keywordTokens =
  [ ("let", TLet),
    ("fast", TFix),
    ("show", TExport),
    ("bring", TImport),
    ("ilk", TType),
    ("yield", TYield),
    ("fremmed", TForeign),
    ("flock", TClass),
    ("bizen", TInstance),
    ("match", TMatch),
    ("sorry", TSorry),
    ("orsetting", TOrsend),
    ("unbuild", TInduce),
    ("fall", TFall)
  ]

isNameChar :: Char -> Bool
isNameChar c = not (isSpace c) && c `notElem` specialNameChars

specialNameChars :: [Char]
specialNameChars = "#()[]{}:,;≔$`'@^."
