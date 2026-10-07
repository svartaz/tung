-- | the dependent frontend reuseth the compiler lexer. annotations and bodies
-- pass through one expression parser; unsupported legacy forms are rejected.
module Tung.Dependent.Source.Parse
  ( SourceSnapshot (..),
    sourceSnapshot,
    snapshotImportPaths,
    parseSource,
    parseProgram,
    parseExpression,
    SourceRole (..),
    parseSourceRoles,
  )
where

import Control.Monad (when)
import Data.Foldable (toList, traverse_)
import Data.List (isSuffixOf)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import GHC.Float (castDoubleToWord64)
import Tung.Dependent.Source.Syntax
import Tung.Dependent.Syntax (HostLiteral (..), Plicity (..))
import Tung.Token

-- a source snapshot shareth one lazy parse between import discovery and
-- compilation. failures stay located and are reported by the owning stage.
data SourceSnapshot = SourceSnapshot
  { snapshotText :: String,
    snapshotProgram :: Either SourceFailure ([(Maybe SourceSpan, Declaration)], Maybe Expression)
  }
  deriving stock (Eq, Show)

sourceSnapshot :: String -> SourceSnapshot
sourceSnapshot text = SourceSnapshot text (parseProgramLocated text)

snapshotImportPaths :: SourceSnapshot -> [FilePath]
snapshotImportPaths snapshot = case snapshotProgram snapshot of
  Left _ -> []
  Right (declarations, _) -> [importPath | (_, ImportDeclaration {importPath}) <- declarations]

-- token ranges and syntax roles from the shared expression parser.
data SourceRole = SourceRole SourceSpan String [String] deriving (Eq, Show)

-- roles survive a failure, so an unfinished buffer still colours its parsed
-- prefix. strict clients inspect only the result.
data Result a = Result (Either SourceFailure a) (Seq SourceRole)

instance Functor Result where
  fmap f (Result value roles) = Result (fmap f value) roles

instance Applicative Result where
  pure value = Result (Right value) Seq.empty
  function <*> value = do
    f <- function
    x <- value
    pure (f x)

instance Monad Result where
  Result (Left failure) roles >>= _ = Result (Left failure) roles
  Result (Right value) roles >>= next = retain roles (next value)

retain :: Seq SourceRole -> Result a -> Result a
retain roles (Result value more) = Result value (roles <> more)

resultEither :: Result a -> Either SourceFailure a
resultEither (Result value _) = value

type Parser a = [Token] -> Result (a, [Token])

failAt :: [Token] -> String -> Result a
failAt tokens message = Result (Left (SourceFailure (case tokens of token : _ -> tokenSpan token; [] -> Nothing) message)) Seq.empty

-- a failure without tokens of its own is reported at the given ones.
liftAt :: [Token] -> Either String a -> Result a
liftAt tokens = either (failAt tokens) pure

parseSource :: String -> Either String [Declaration]
parseSource = either (Left . failureMessage) (Right . fst) . parseProgramDetailed

-- declarations, optionally ended by `yield` and the expression to evaluate.
parseProgram :: String -> Either String ([Declaration], Maybe Expression)
parseProgram = either (Left . failureMessage) Right . parseProgramDetailed

parseProgramDetailed :: String -> Either SourceFailure ([Declaration], Maybe Expression)
parseProgramDetailed source = (\(found, yielded) -> (map snd found, yielded)) <$> parseProgramLocated source

-- each top-level declaration with the span of the name it declareth, or of its
-- keyword when it nameth nothing.
parseProgramLocated :: String -> Either SourceFailure ([(Maybe SourceSpan, Declaration)], Maybe Expression)
parseProgramLocated source = do
  tokens <- located source
  -- a failure at the end of the input pointeth just past the last token.
  let atEnd = \case
        Left failure@SourceFailure {failureSpan = Nothing}
          | Just SourceSpan {spanEnd} <- last (Nothing : map tokenSpan tokens) -> Left failure {failureSpan = Just (SourceSpan spanEnd spanEnd)}
        result -> result
  atEnd (resultEither (program tokens))
  where
    program tokens = do
      (found, rest) <- locatedDeclarations tokens
      case rest of
        TYield : afterYield -> (found,) . Just <$> whole expression afterYield
        _ -> (found, Nothing) <$ whole (\remaining -> pure ((), remaining)) rest

parseExpression :: String -> Either String Expression
parseExpression source = either (Left . failureMessage) Right (located source >>= resultEither . whole expression)

located :: String -> Either SourceFailure [Token]
located source = map locatedToken <$> lexLocatedTokensDetailed source

whole :: Parser a -> [Token] -> Result a
whole parser tokens = do
  (result, rest) <- parser tokens
  case rest of
    [] -> pure result
    _ -> failAt rest "unexpected token; expected a declaration or the end of the input"

declarations :: Parser [Declaration]
declarations tokens = (\(found, rest) -> (map snd found, rest)) <$> locatedDeclarations tokens

locatedDeclarations :: Parser [(Maybe SourceSpan, Declaration)]
locatedDeclarations = declarationsUsing oneDeclaration

declarationsUsing :: Parser Declaration -> Parser [(Maybe SourceSpan, Declaration)]
declarationsUsing parser tokens = case tokens of
  [] -> pure ([], [])
  TYield : _ -> pure ([], tokens)
  TRBrace : _ -> pure ([], tokens)
  _ -> do
    (declaration, following) <- parser tokens
    (remaining, ending) <- declarationsUsing parser following
    pure ((nameSpan tokens, declaration) : remaining, ending)
  where
    nameSpan = \case
      TExport : rest@(_ : _) -> nameSpan rest
      keyword : name@(TIdent _) : _ | keyword /= TExport -> tokenSpan name
      keyword : _ -> tokenSpan keyword
      [] -> Nothing

-- one declaration; `show` before a declaration wrapeth it.
oneDeclaration :: Parser Declaration
oneDeclaration tokens = case tokens of
  TLet : rest -> letDeclaration rest
  TType : rest -> inductiveDeclaration rest
  TClass : rest -> flockDeclaration rest
  TInstance : rest -> bizenDeclaration rest
  TOrsend : rest -> orsendDeclaration rest
  TImport : rest -> importDeclaration rest
  TExport : rest@(TLet : _) -> shown rest
  TExport : rest@(TType : _) -> shown rest
  TExport : rest@(TClass : _) -> shown rest
  TExport : rest@(TOrsend : _) -> shown rest
  TExport : rest@(TIdent _ : _) -> (\(names, following) -> (ReExportDeclaration names, following)) <$> reexported [] rest
  TExport : _ -> failAt tokens "show must precede a let, ilk, flock, or orsetting declaration or a name"
  _ -> failAt tokens "expected a declaration: let, ilk, flock, bizen, orsetting, use, or show"

-- `show a, b` re-exporteth visible names.
reexported :: [String] -> Parser [String]
reexported names tokens = case tokens of
  TIdent name : TComma : rest -> reexported (name : names) rest
  TIdent name : rest -> pure (reverse (name : names), rest)
  _ -> failAt tokens "expected a shown name"

-- `show` wrapeth exactly one following declaration.
shown :: Parser Declaration
shown tokens = (\(declaration, following) -> (ShownDeclaration declaration, following)) <$> oneDeclaration tokens

-- `flock name:[parameters, @:parent, *] { members }`. the signature endeth in `*`.
flockDeclaration :: Parser Declaration
flockDeclaration tokens@(TIdent name : TColon : rest) = do
  plainName tokens name
  markFirst "class" (["declaration"] ++ ["typeFunction" | case rest of TLBracket : _ -> True; _ -> False]) tokens
  (signature, afterSignature) <- typeRoles (atom rest)
  parameters <- case signature of
    Product parameters Universe -> pure parameters
    Universe -> pure []
    _ -> failAt rest "a flock signature endeth in '*'"
  case afterSignature of
    TLBrace : afterOpen -> do
      (members, remaining) <- flockMemberList afterOpen
      pure (FlockDeclaration name parameters members, remaining)
    _ -> failAt afterSignature "expected '{' after flock signature"
flockDeclaration tokens = failAt tokens "expected flock name and ':signature'"

-- members are `let name:type` without a body. a member whose bracketed type
-- endeth in an equation, `let name:[parameters, a = b]`, is a named law.
flockMemberList :: Parser [FlockMember]
flockMemberList tokens = case tokens of
  TRBrace : rest -> pure ([], rest)
  TLet : named@(TIdent name : TColon : rest)
    | Left failure <- resultEither (plainName named name) -> Result (Left failure) Seq.empty
    | TLBracket : items <- rest,
      Result (Right (law, afterLaw)) events <- lawItems name [] items -> do
        (members, remaining) <- flockMemberList afterLaw
        retain events (markFirst "call" ["declaration", "applied"] named >> pure (law : members, remaining))
    -- a bracket with an equation among its items is a law, even when malformed.
    | TLBracket : items <- rest,
      equation items,
      Result (Left failure) _ <- lawItems name [] items ->
        Result (Left failure) Seq.empty
    | otherwise -> do
        (ty, afterType) <- typeRoles (expression rest)
        markFirst "call" ["declaration", "applied"] named
        (members, remaining) <- flockMemberList afterType
        pure (FlockMember name ty : members, remaining)
  _ -> failAt tokens "expected a flock member or '}'"
  where
    -- `=` at the bracket's own depth, before it closeth.
    equation = go (0 :: Int)
      where
        go depth = \case
          [] -> False
          TRBracket : rest | depth == 0 -> False | otherwise -> go (depth - 1) rest
          token : rest
            | token `elem` [TLBracket, TLParen, TLBrace] -> go (depth + 1) rest
            | token `elem` [TRParen, TRBrace] -> go (depth - 1) rest
            | token == TIdent "=" && depth == 0 -> True
            | otherwise -> go depth rest
    -- binders, then the equation as the final item.
    -- `=` is the identity type applied as an infix name, so each side is
    -- one atom.
    -- a pattern slot, `x box: a box`, bindeth a hidden input that both sides
    -- of the equation match.
    lawItems name binders items
      | Result (Right (left, TIdent "=" : afterEquals)) events <- atom items = do
          (right, afterRight) <- retain events (atom afterEquals)
          let patterns = [(Name hidden, pattern) | (Parameter {parameterName = Just hidden}, Just pattern) <- binders]
              matched side
                | null patterns = side
                | otherwise = Match (map fst (reverse patterns)) [Row (map snd (reverse patterns)) side]
          distinctNames items [binder | (Parameter {parameterName = Just binder}, _) <- binders, binder /= "_"]
          case afterRight of
            TRBracket : remaining -> pure (FlockLaw name (reverse (map fst binders)) (matched left) (matched right), remaining)
            _ -> failAt afterRight "a law side with several terms needeth parentheses"
      | otherwise = do
          (item, afterItem) <- lawSlot (length binders) items
          when (parameterType (fst item) == Inferred) (failAt items "law parameters require types")
          case afterItem of
            TComma : more -> lawItems name (item : binders) more
            TIdent "=" : _ -> failAt afterItem "a law side with several terms needeth parentheses"
            _ -> failAt afterItem "a law endeth in an equation 'left = right'"
    lawSlot index items = case items of
      TAt : _ -> (\(item, rest) -> ((item, Nothing), rest)) <$> parameter items
      TIdent _ : TColon : _ -> (\(item, rest) -> ((item, Nothing), rest)) <$> parameter items
      _ -> do
        (value, afterValue) <- headerRoles (expression items)
        case afterValue of
          TColon : afterColon -> do
            (ty, remaining) <- typeRoles (expression afterColon)
            pure ((Parameter Explicit (Just ("#law" ++ show (index :: Int))) ty, Just value), remaining)
          _ -> pure ((Parameter Explicit Nothing value, Nothing), afterValue)

-- `bizen:type { lets }`. the type endeth before the opening brace, as match
-- scrutinees do. member bodies are ordinary declarations.
bizenDeclaration :: Parser Declaration
bizenDeclaration = bizenHeader False Nothing

-- `fallback` and a priority may precede the colon, in that order.
bizenHeader :: Bool -> Maybe Integer -> Parser Declaration
bizenHeader fallback priority tokens = case tokens of
  marker@(TIdent "fallback") : rest | not fallback, Nothing <- priority -> markRole "keyword" [] marker >> bizenHeader True priority rest
  TNatural value : rest | Nothing <- priority -> bizenHeader fallback (Just (toInteger value)) rest
  TColon : rest -> do
    (parts, afterType) <- typeRoles (applicationPartsUntil (== TLBrace) rest)
    ty <- liftAt rest (application parts)
    markClass ty
    case afterType of
      TLBrace : afterOpen -> do
        (located, afterMembers) <- declarationsUsing (memberRoles . oneDeclaration) afterOpen
        let members = map snd located
        case afterMembers of
          TRBrace : remaining -> pure (BizenDeclaration priority fallback ty members, remaining)
          _ -> failAt afterMembers "expected '}' after bizen members"
      _ -> failAt afterType "expected '{' after bizen type"
  _ -> failAt tokens "expected ':' after bizen"

-- `orsetting name: type` nameth an assumption. the type may not bind inputs.
orsendDeclaration :: Parser Declaration
orsendDeclaration tokens = case tokens of
  TIdent name : TColon : rest -> do
    plainName tokens name
    (ty, remaining) <- typeRoles (expression rest)
    markFirst (if callable ty then "function" else "variable") ["declaration"] tokens
    pure (AssumptionDeclaration name ty, remaining)
  _ -> failAt tokens "expected 'name:' after orsetting"

-- the path is one name with dotted segments; a following name is its alias.
importDeclaration :: Parser Declaration
importDeclaration tokens = case tokens of
  TIdent first : rest -> do
    markFirst "import" [] tokens
    result <- go first rest
    case result of
      (ImportDeclaration path _, _) | not (".tung" `isSuffixOf` path) -> failAt tokens ("use path '" ++ path ++ "' must end in '.tung'")
      _ -> pure result
  _ -> failAt tokens "expected a use path"
  where
    go path (TDot : TIdent segment : remaining) = go (path ++ "." ++ segment) remaining
    go path aliased@(TIdent alias : remaining)
      | any (`elem` "~/") alias = failAt aliased ("use alias '" ++ alias ++ "' must be one plain name")
      | otherwise = markFirst "namespace" ["declaration"] aliased >> pure (ImportDeclaration path (Just alias), remaining)
    go path remaining = pure (ImportDeclaration path Nothing, remaining)

inductiveDeclaration :: Parser Declaration
inductiveDeclaration tokens@(TIdent name : TColon : rest) = localTerms headerNames tokens do
  plainName tokens name
  markFirst "type" (["declaration"] ++ ["typeFunction" | case rest of TLBracket : _ -> True; _ -> False]) tokens
  -- the braces belong to the declaration. compound signatures can use a
  -- bracketed product or parentheses, leaving the opening brace unambiguous.
  (signature, afterSignature) <- typeRoles (atom rest)
  case afterSignature of
    TLBrace : afterOpen -> do
      (constructors, remaining) <- constructorDeclarations afterOpen
      pure (InductiveDeclaration name signature constructors, remaining)
    _ -> failAt afterSignature "expected '{' after ilk signature"
  where
    -- header parameters scope over the constructor annotations.
    headerNames = \case
      InductiveDeclaration {inductiveSignature = Product parameters _} -> valueNames parameters
      _ -> []
inductiveDeclaration tokens = failAt tokens "expected ilk name and ':signature'"

constructorDeclarations :: Parser [ConstructorDeclaration]
constructorDeclarations (TRBrace : rest) = pure ([], rest)
constructorDeclarations named@(TIdent name : TColon : tokens) = do
  plainName named name
  (annotation, afterAnnotation) <- typeRoles (expression tokens)
  markFirst (if callable annotation then "function" else "enumMember") ["declaration", "constructor"] named
  let constructor = ConstructorDeclaration name annotation
  case afterAnnotation of
    TComma : rest -> do
      (remaining, following) <- constructorDeclarations rest
      pure (constructor : remaining, following)
    TRBrace : rest -> pure ([constructor], rest)
    _ -> failAt afterAnnotation "expected ',' or '}' after constructor"
constructorDeclarations tokens@(TIdent name : _) = failAt tokens ("constructor '" ++ name ++ "' requireth a type, as in '" ++ name ++ ":type'")
constructorDeclarations tokens = failAt tokens "expected constructor name"

-- a let header is one name; arguments are annotation slots.
letDeclaration :: Parser Declaration
letDeclaration tokens = do
  (name, afterHeader) <- case tokens of
    TIdent name : rest -> (name, rest) <$ plainName tokens name
    _ -> failAt tokens "expected let name"
  (annotation, bodyTokens) <- case afterHeader of
    TColon : rest -> do
      (ty, afterType) <- typeRoles (letAnnotation rest)
      case afterType of
        TEquals : body -> pure (Just ty, body)
        _ -> failAt afterType "expected '≔' after let annotation"
    TEquals : body -> pure (Nothing, body)
    _ -> failAt afterHeader "expected ':' or '≔' after let name"
  let ty = fst <$> annotation
      typeDefinition = maybe False sorted ty
      modifiers = ["declaration"] ++ [if typeDefinition then "typeFunction" else "applied" | maybe False callable ty]
  markFirst (if typeDefinition then "type" else if maybe False callable ty then "function" else "variable") modifiers tokens
  case (bodyTokens, annotation) of
    (TText key : TForeign : remaining, Just (ty, written))
      | next : _ <- remaining,
        not (stopsExpression next) -> do
          (model, afterModel) <- expression remaining
          lowered <- liftAt remaining (lowerHeader annotation model)
          pure (HostDeclaration name ty key (Just lowered), afterModel)
      | any bindsInput written -> failAt bodyTokens "a fremmed annotation without a model cannot bind inputs"
      | otherwise -> pure (HostDeclaration name ty key Nothing, remaining)
    (TText _ : TForeign : _, Nothing) -> failAt bodyTokens "a fremmed binding requireth a type annotation"
    _ -> do
      (body, remaining) <- (if typeDefinition then typeRoles else id) (expression bodyTokens)
      when (not typeDefinition && not (maybe False callable ty) && callable body) (markFirst "function" ["declaration", "applied"] tokens)
      lowered <- liftAt bodyTokens (lowerHeader annotation body)
      pure (Declaration name (fst <$> annotation) lowered, remaining)

-- a let annotation is a type. a bracket may also bind patterns, `pattern: type`,
-- and omit its result when its last slot bindeth, as in `[x:] = x`; the result
-- is then inferred. each written slot is returned beside the product.
letAnnotation :: Parser (Expression, [Slot])
letAnnotation tokens@(TLBracket : rest) = localTerms (valueNames . map slotParameter . snd) tokens $ case slots rest of
  Result (Right (written, afterBracket@(TEquals : _))) events -> do
    emitRoles events
    distinctNames tokens [name | Slot {slotParameter = Parameter {parameterName = Just name}} <- written, name /= "_"]
    pure
      ( case reverse written of
          Slot parameter@Parameter {parameterPlicity = Explicit, parameterName = Nothing} Nothing : reversed ->
            (Product (map slotParameter (reverse reversed)) (parameterType parameter), reverse reversed)
          _ -> (Product (map slotParameter written) Inferred, written),
        afterBracket
      )
  _ -> unslotted tokens
  where
    slots items = do
      (item, afterItem) <- slot items
      case afterItem of
        TComma : more -> do
          (others, remaining) <- slots more
          pure (item : others, remaining)
        TRBracket : remaining -> pure ([item], remaining)
        _ -> failAt afterItem "expected ',' or ']' after bracket item"
    slot items = case items of
      TAt : _ -> (\(parameter, remaining) -> (Slot parameter Nothing, remaining)) <$> parameter items
      TIdent _ : TColon : _ -> (\(parameter, remaining) -> (Slot parameter Nothing, remaining)) <$> parameter items
      _ -> do
        let parsed = expression items
        (value, afterValue) <- deferred parsed
        case afterValue of
          TColon : afterColon -> do
            emitRoles (rolesOf (headerRoles parsed))
            (ty, remaining) <- slotType afterColon
            pure (Slot (Parameter Explicit Nothing ty) (Just value), remaining)
          _ -> emitRoles (rolesOf parsed) >> pure (Slot (Parameter Explicit Nothing value) Nothing, afterValue)
letAnnotation tokens = unslotted tokens

unslotted :: Parser (Expression, [Slot])
unslotted tokens = (\(ty, rest) -> ((ty, []), rest)) <$> expression tokens

-- a let annotation slot, with the pattern that bindeth it when written.
data Slot = Slot
  { slotParameter :: Parameter,
    slotPattern :: Maybe Expression
  }

-- an explicit named or pattern slot bindeth an input that a body can use.
bindsInput :: Slot -> Bool
bindsInput slot@Slot {slotParameter = Parameter {parameterPlicity}} = parameterPlicity == Explicit && binds slot

-- named slots, pattern slots, and `@` slots bind an input.
binds :: Slot -> Bool
binds Slot {slotParameter = Parameter {parameterPlicity, parameterName}, slotPattern} =
  parameterPlicity == Implicit || maybe False (const True) parameterName || maybe False (const True) slotPattern

-- written named slots, pattern slots, and `@:` requirements supply lambda
-- binders; bare slots describe a function supplied by the body. a written
-- discard remaineth distinct from a bare slot. pattern slots bind hidden
-- locals that the body matcheth. the declaration annotation supplieth each
-- domain during checking, so lowering doth not copy its expressions.
lowerHeader :: Maybe (Expression, [Slot]) -> Expression -> Either String Expression
lowerHeader annotation body = do
  let written = case annotation of
        Just (_, written@(_ : _)) -> written
        Just (Product inputs _, []) -> [Slot input Nothing | input <- inputs]
        _ -> []
      (leading, bare) = span binds written
      hidden index = "#slot" ++ show (index :: Int)
      binder (index, Slot {slotParameter = Parameter {parameterPlicity, parameterName}, slotPattern}) = case slotPattern of
        Just _ -> Binder Explicit (Just (hidden index)) Nothing
        Nothing -> Binder parameterPlicity (parameterName >>= bindingName) Nothing
      patterns = [(Name (hidden index), pattern) | (index, Slot {slotPattern = Just pattern}) <- zip [0 ..] leading]
      matched
        | null patterns = body
        | otherwise = Match (map fst patterns) [Row (map snd patterns) body]
  when (any binds bare) (Left "named slots and requirements must precede bare slots")
  pure (if null leading then body else Lambda (map binder (zip [0 ..] leading)) matched)

bindingName :: String -> Maybe String
bindingName "_" = Nothing
bindingName name = Just name

expression :: Parser Expression
expression tokens = do
  (parts, rest) <- applicationParts tokens
  initial <- liftAt tokens (application parts)
  markApplication initial
  (value, remaining) <- dollars initial rest
  pure (spanned tokens remaining value, remaining)

-- an expression with the span of the tokens it consumed.
spanned :: [Token] -> [Token] -> Expression -> Expression
spanned tokens rest value = maybe value (`Located` value) (consumedSpan tokens rest)

applicationParts :: Parser [Argument]
applicationParts = applicationPartsUntil (const False)

applicationPartsUntil :: (Token -> Bool) -> Parser [Argument]
applicationPartsUntil stop = go []
  where
    go accumulated [] = finish accumulated []
    go accumulated tokens@(token : _)
      | stopsExpression token || stop token = finish accumulated tokens
      | otherwise = do
          (argument, rest) <- parseArgument tokens
          go (argument : accumulated) rest
    finish [] rest = failAt rest "expected an expression"
    finish accumulated rest = pure (reverse accumulated, rest)

stopsExpression :: Token -> Bool
stopsExpression token = token `elem` [TLet, TType, TImport, TExport, TClass, TInstance, TOrsend, TYield, TComma, TColon, TSemicolon, TEquals, TMapsTo, TRParen, TRBracket, TRBrace, TDollar]

parseArgument :: Parser Argument
parseArgument (TAt : rest) = do
  (value, remaining) <- typeRoles (atom rest)
  pure (Argument Implicit value, remaining)
parseArgument tokens = do
  (value, rest) <- atom tokens
  pure (Argument Explicit value, rest)

-- a single atom standeth alone. otherwise the second value is the function,
-- except that an implicit argument after the first value already identifyeth it.
application :: [Argument] -> Either String Expression
application [Argument Explicit value] = pure value
application (Argument Explicit function : arguments@(Argument Implicit _ : _)) = pure (Application function arguments)
application (first : Argument Explicit function : rest) = pure (Application function (first : rest))
application _ = Left "implicit arguments requireth a function"

-- a dollar segment putteth its function first and supplieth the previous value
-- as its first explicit argument, matching the existing application notation.
dollars :: Expression -> Parser Expression
dollars = dollarsUntil (const False)

-- a match scrutinee's dollar segments end at the opening brace.
dollarsUntil :: (Token -> Bool) -> Expression -> Parser Expression
dollarsUntil stop value (TDollar : TLParen : rest) = do
  (parts, afterParts) <- applicationParts rest
  case (parts, afterParts) of
    (Argument Explicit function : arguments, TRParen : remaining) -> markFunction "call" function >> dollarsUntil stop (Application function (Argument Explicit value : arguments)) remaining
    _ -> failAt afterParts "expected function and ')' after '$('"
dollarsUntil stop value (TDollar : rest) = do
  (parts, remaining) <- applicationPartsUntil stop rest
  case parts of
    Argument Explicit function : arguments -> markFunction "call" function >> dollarsUntil stop (Application function (Argument Explicit value : arguments)) remaining
    _ -> failAt rest "expected function after '$'"
dollarsUntil _ value rest = pure (value, rest)

-- `.field` projections bind tighter than application.
atom :: Parser Expression
atom tokens = do
  (base, rest) <- atomBase tokens
  (value, remaining) <- projections base rest
  pure (spanned tokens remaining value, remaining)
  where
    projections value (TDot : token@(TIdent field) : rest) = markRole "property" [] token >> projections (Projection value field) rest
    projections value rest = pure (value, rest)

atomBase :: Parser Expression
atomBase tokens = case tokens of
  TKindStar : rest -> pure (Universe, rest)
  TIdent "_" : rest -> pure (Wildcard, rest)
  TSorry : rest -> pure (Sorry, rest)
  TInduce : token@(TIdent name) : rest -> markRole "type" [] token >> pure (Induce name, rest)
  TInduce : rest -> failAt rest "expected an ilk or flock name after 'unbuild'"
  TMatch : rest -> matchExpression rest
  token@(TIdent name) : rest -> markRole "term" [] token >> pure (Name name, rest)
  TLBracket : rest -> bracket rest
  TBraceKeyword marker : rest | marker `elem` ["<", ">"] -> composition marker rest
  TBraceKeyword "r" : rest -> record rest
  TLBrace : rest -> lambda rest
  TFall : rest -> fall rest
  TLParen : rest@(TLet : _) -> block rest
  TLParen : rest@(TImport : _) -> block rest
  TLParen : rest@(TExport : _) -> block rest
  TLParen : rest -> do
    (value, afterValue) <- expression rest
    case afterValue of
      TRParen : remaining -> pure (value, remaining)
      TColon : afterColon -> do
        (annotation, afterType) <- typeRoles (expression afterColon)
        case afterType of
          TRParen : remaining -> pure (Ascription value annotation, remaining)
          _ -> failAt afterType "expected ')' after annotation"
      _ -> failAt afterValue "expected ')' after expression"
  TNatural value : rest -> pure (LiteralExpression (NaturalValue value), rest)
  TInteger value : rest -> pure (LiteralExpression (IntegerValue value), rest)
  TFloat value : rest -> pure (LiteralExpression (FloatBits (castDoubleToWord64 value)), rest)
  TUnicode value : rest -> pure (LiteralExpression (UnicodeValue value), rest)
  TText _ : TForeign : _ -> failAt tokens "fremmed bindeth only an annotated top-level let"
  TText value : rest -> pure (LiteralExpression (TextValue value), rest)
  _ -> failAt tokens "expected an expression"

-- `r{a:t}` is a record type, `r{a = v}` a record, and `r{= base, a = v, - b}`
-- an update. `r{}` is the empty record.
record :: Parser Expression
record tokens = case tokens of
  TRBrace : rest -> pure (RecordExpression [], rest)
  TEquals : rest -> do
    (base, afterBase) <- expression rest
    (changes, remaining) <- recordItems change afterBase
    pure (RecordUpdate base changes, remaining)
  TIdent _ : TColon : _ -> fields TColon RecordTypeExpression tokens
  TIdent _ : TEquals : _ -> fields TEquals RecordExpression tokens
  _ -> failAt tokens "expected a record field"
  where
    fields separator build items = do
      (values, remaining) <- recordItems (field separator) (TComma : items)
      pure (build values, remaining)
    field separator items = case items of
      TIdent name : actual : rest | actual == separator -> do
        (value, remaining) <- (if separator == TColon then typeRoles else id) (expression rest)
        markFirst "property" [] items
        pure ((name, value), remaining)
      _ -> failAt items "expected a record field"
    change = \case
      TIdent "-" : TIdent name : rest -> pure (RemoveField name, rest)
      items -> do
        ((name, value), remaining) <- field TEquals items
        pure (SetField name value, remaining)

-- items follow commas until the closing brace.
recordItems :: Parser a -> Parser [a]
recordItems item tokens = case tokens of
  TRBrace : rest -> pure ([], rest)
  TComma : rest -> do
    (value, afterValue) <- item rest
    (values, remaining) <- recordItems item afterValue
    pure (value : values, remaining)
  _ -> failAt tokens "expected ',' or '}' in a record"

-- association is ordinary application sugar, independent of any list family.
-- the same expansion works for values, types, and functions returning types.
composition :: String -> Parser Expression
composition marker tokens = do
  (items, rest) <- compositionItems tokens
  case items of
    function : first : second : remaining -> do
      markFunction "call" function
      let combine left right = Application function [Argument Explicit left, Argument Explicit right]
          rightAssociated left [] = left
          rightAssociated left (next : following) = combine left (rightAssociated next following)
          value = if marker == "<" then foldl combine first (second : remaining) else rightAssociated first (second : remaining)
      pure (value, rest)
    _ -> failAt tokens "composition requireth a function and at least two operands"

compositionItems :: Parser [Expression]
compositionItems (TRBrace : rest) = pure ([], rest)
compositionItems tokens = do
  (item, afterItem) <- expression tokens
  case afterItem of
    TComma : rest -> do
      (items, remaining) <- compositionItems rest
      pure (item : items, remaining)
    TRBrace : rest -> pure ([item], rest)
    _ -> failAt afterItem "expected ',' or '}' after composition item"

bracket :: Parser Expression
bracket tokens = localTerms productNames tokens do
  (items, rest) <- bracketItems tokens
  distinctNames tokens [name | Parameter {parameterName = Just name} <- items, name /= "_"]
  case reverse items of
    Parameter Explicit Nothing result : reversed -> pure (Product (reverse reversed) result, rest)
    _ -> failAt tokens "brackets requireth a final result expression"
  where
    productNames = \case
      Product parameters _ -> valueNames parameters
      _ -> []

bracketItems :: Parser [Parameter]
bracketItems tokens = do
  (item, afterItem) <- parameter tokens
  case afterItem of
    TComma : rest -> do
      (items, remaining) <- bracketItems rest
      pure (item : items, remaining)
    TRBracket : rest -> pure ([item], rest)
    _ -> failAt afterItem "expected ',' or ']' after bracket item"

parameter :: Parser Parameter
parameter (TAt : token@(TIdent name) : TColon : rest) = namedParameter Implicit token name rest
-- `@:flock` is an anonymous requirement: an instance-searched implicit slot.
parameter (TAt : TColon : rest) = do
  (ty, remaining) <- typeRoles (expression rest)
  markClass ty
  pure (Parameter Implicit Nothing ty, remaining)
parameter tokens@(TAt : _) = failAt tokens "implicit parameters require '@name:type' or '@:requirement'"
parameter (token@(TIdent name) : TColon : rest) = namedParameter Explicit token name rest
parameter tokens = do
  (ty, rest) <- typeRoles (expression tokens)
  pure (Parameter Explicit Nothing ty, rest)

-- a declared name is unqualified; `~` only reacheth an import.
plainName :: [Token] -> String -> Result ()
plainName tokens name
  | '~' `elem` name && name /= "~" = failAt tokens ("declared name '" ++ name ++ "' must be unqualified")
  | otherwise = pure ()

-- a bracket nameth each slot once.
distinctNames :: [Token] -> [String] -> Result ()
distinctNames tokens names = case [name | (index, name) <- zip [0 :: Int ..] names, name `elem` take index names] of
  name : _ -> failAt tokens ("'" ++ name ++ "' nameth two slots of one bracket")
  [] -> pure ()

-- `name:` with nothing before the next item leaveth its type to inference.
namedParameter :: Plicity -> Token -> String -> Parser Parameter
namedParameter plicity token name tokens = do
  (ty, rest) <- typeRoles (slotType tokens)
  markRole (if sorted ty then "typeParameter" else "headerPattern") ["declaration"] token
  pure (Parameter plicity (Just name) ty, rest)

slotType :: Parser Expression
slotType tokens = case tokens of
  TComma : _ -> pure (Inferred, tokens)
  TRBracket : _ -> pure (Inferred, tokens)
  _ -> expression tokens

-- one row of plain binders is an ordinary lambda. several rows, `;`
-- alternatives, or non-variable patterns form a case function.
lambda :: Parser Expression
lambda (TRBrace : rest) = pure (Cases [], rest)
lambda tokens = do
  (groups, remaining) <- caseGroups tokens
  -- a lambda bindeth each name once; elaboration checketh pattern rows.
  case [name | [([items], _)] <- [groups], Just binders <- [traverse plainBinder items], name <- repeated [name | Binder {binderName = Just name} <- binders]] of
    name : _ -> failAt tokens ("'" ++ name ++ "' is bound twice in one row")
    [] -> pure ()
  pure case groups of
    [([items], body)] | Just binders <- traverse plainBinder items -> (Lambda binders body, remaining)
    _ -> (Cases [Row (map itemPattern items) body | (alternatives, body) <- groups, items <- alternatives], remaining)
  where
    plainBinder = \case
      Left binder -> Just binder
      Right (Name name) -> Just (Binder Explicit (bindingName name) Nothing)
      Right Wildcard -> Just (Binder Explicit Nothing Nothing)
      Right _ -> Nothing
    itemPattern = \case
      Left (Binder _ name _) -> maybe Wildcard Name name
      Right pattern -> pattern
    repeated names = [name | (index, name) <- zip [0 :: Int ..] names, name `elem` take index names]

-- rows end at '}'. each row hath `;`-separated alternatives before '^'.
caseGroups :: Parser [([[Either Binder Expression]], Expression)]
caseGroups tokens = do
  (alternatives, afterPatterns) <- rowAlternatives tokens
  case afterPatterns of
    TMapsTo : rest -> do
      (body, afterBody) <- expression rest
      case afterBody of
        TComma : more -> do
          (groups, remaining) <- caseGroups more
          pure ((alternatives, body) : groups, remaining)
        TRBrace : remaining -> pure ([(alternatives, body)], remaining)
        _ -> failAt afterBody "expected ',' or '}' after a case"
    _ -> failAt afterPatterns "expected '^' after patterns"

rowAlternatives :: Parser [[Either Binder Expression]]
rowAlternatives tokens = do
  (items, rest) <- rowItems tokens
  case rest of
    TSemicolon : more -> do
      (alternatives, remaining) <- rowAlternatives more
      pure (items : alternatives, remaining)
    _ -> pure ([items], rest)

rowItems :: Parser [Either Binder Expression]
rowItems tokens = do
  (item, rest) <- rowItem tokens
  case rest of
    TComma : more -> do
      (items, remaining) <- rowItems more
      pure (item : items, remaining)
    _ -> pure ([item], rest)

-- `@x`, `x:type`, and `x` are binders; any other expression is a pattern.
rowItem :: Parser (Either Binder Expression)
rowItem tokens = case tokens of
  TAt : rest -> lambdaBinder (TAt : rest) >>= \(item, remaining) -> pure (Left item, remaining)
  TIdent _ : TColon : _ -> lambdaBinder tokens >>= \(item, remaining) -> pure (Left item, remaining)
  _ -> do
    (pattern, remaining) <- patternRoles (expression tokens)
    pure (Right pattern, remaining)

-- `match a, b { rows }`. scrutinees end at the opening brace.
matchExpression :: Parser Expression
matchExpression tokens = do
  (scrutinees, afterScrutinees) <- scrutineeList tokens
  case afterScrutinees of
    -- `for known` nameth the equation between the scrutinee and each pattern.
    for@(TIdent "for") : named@(TIdent known : afterName) -> case scrutinees of
      [scrutinee] -> do
        markRole "keyword" [] for
        markFirst "parameter" ["declaration"] named
        (rows, remaining) <- rowsAfter afterName
        pure (MatchFor scrutinee known rows, remaining)
      _ -> failAt afterScrutinees "'for' nameth the equation of one scrutinee"
    TIdent "for" : afterFor -> failAt afterFor "expected an equation name after 'for'"
    _ -> do
      (rows, remaining) <- rowsAfter afterScrutinees
      pure (Match scrutinees rows, remaining)
  where
    rowsAfter = \case
      TLBrace : TRBrace : remaining -> pure ([], remaining)
      TLBrace : rest -> do
        (groups, remaining) <- caseGroups rest
        pure ([Row items body | (alternatives, body) <- groups, items <- map (map pattern) alternatives], remaining)
      afterHeader -> failAt afterHeader "expected '{' after match scrutinees"
    pattern = either (\(Binder _ name _) -> maybe Wildcard Name name) id
    -- `for` endeth the scrutinees only here; elsewhere it is an ordinary name.
    headerEnd = \case
      TLBrace -> True
      TIdent "for" -> True
      _ -> False
    scrutineeList ts = do
      (parts, afterParts) <- applicationPartsUntil headerEnd ts
      initial <- liftAt ts (application parts)
      (first, rest) <- dollarsUntil headerEnd initial afterParts
      case rest of
        TComma : more -> do
          (others, remaining) <- scrutineeList more
          pure (first : others, remaining)
        _ -> pure ([first], rest)

-- `fall params, result ^ body` is a lambda checked against its written
-- product. a bare slot bindeth an input that the body cannot name.
fall :: Parser Expression
fall tokens = do
  (items, afterItems) <- fallItems tokens
  case reverse items of
    Parameter Explicit Nothing result : reversed@(_ : _) -> do
      let parameters = reverse reversed
          binders = [Binder parameterPlicity (parameterName >>= bindingName) Nothing | Parameter {parameterPlicity, parameterName} <- parameters]
      (body, remaining) <- expression afterItems
      pure (Ascription (Lambda binders body) (Product parameters result), remaining)
    _ -> failAt tokens "fall requireth at least one input and a final result type"

fallItems :: Parser [Parameter]
fallItems tokens = do
  (item, afterItem) <- parameter tokens
  case afterItem of
    TComma : rest -> do
      (items, remaining) <- fallItems rest
      pure (item : items, remaining)
    TMapsTo : rest -> pure ([item], rest)
    _ -> failAt afterItem "expected ',' or '^' after fall item"

lambdaBinder :: Parser Binder
lambdaBinder (TAt : rest) = binder Implicit rest
lambdaBinder rest = binder Explicit rest

binder :: Plicity -> Parser Binder
binder plicity (TIdent name : TColon : rest) = do
  (annotation, remaining) <- typeRoles (expression rest)
  pure (Binder plicity (bindingName name) (Just annotation), remaining)
binder plicity (TIdent name : rest) = pure (Binder plicity (bindingName name) Nothing, rest)
binder _ tokens = failAt tokens "a typed or implicit binder requireth a name"

block :: Parser Expression
block tokens = do
  (bindings, rest) <- declarations tokens
  when (any isInductive bindings) (failAt tokens "ilk declarations must be top-level")
  when (any isHost bindings) (failAt tokens "fremmed bindings must be top-level")
  when (any isModuleLevel bindings) (failAt tokens "use and show must be top-level")
  case rest of
    TYield : afterYield -> do
      (body, afterBody) <- expression afterYield
      case afterBody of
        TRParen : remaining -> pure (Block bindings body, remaining)
        _ -> failAt afterBody "expected ')' after block result"
    _ -> failAt rest "expected 'yield' after local bindings"
  where
    isInductive InductiveDeclaration {} = True
    isInductive _ = False
    isHost HostDeclaration {} = True
    isHost _ = False
    isModuleLevel ImportDeclaration {} = True
    isModuleLevel ShownDeclaration {} = True
    isModuleLevel ReExportDeclaration {} = True
    isModuleLevel _ = False

-- successful speculative parses defer their events until a delimiter selecteth
-- the context; failures retain their parsed prefix.
deferred :: Result a -> Result a
deferred result@(Result (Left _) _) = result
deferred (Result value _) = Result value Seq.empty

rolesOf :: Result a -> Seq SourceRole
rolesOf (Result _ roles) = roles

emitRoles :: Seq SourceRole -> Result ()
emitRoles = Result (Right ())

markRole :: String -> [String] -> Token -> Result ()
markRole _ _ (TIdent "_") = pure ()
markRole role modifiers token = maybe (pure ()) (\span -> emitRoles (Seq.singleton (SourceRole span role modifiers))) (tokenSpan token)

markFirst :: String -> [String] -> [Token] -> Result ()
markFirst role modifiers = traverse_ (markRole role modifiers) . take 1

-- a member declaration keepeth its callable role; the editor presenteth it as a
-- method. nested declarations in its body retain their own roles.
memberRoles :: Result a -> Result a
memberRoles (Result value roles) = Result value $ case Seq.findIndexL binding roles of
  Just index -> Seq.adjust' member index roles
  Nothing -> roles
  where
    binding (SourceRole _ role modifiers) = role `elem` ["function", "variable"] && "declaration" `elem` modifiers
    member (SourceRole span "function" modifiers) = SourceRole span "call" modifiers
    member role = role

mapRoles :: (SourceRole -> SourceRole) -> Result a -> Result a
mapRoles f (Result value roles) = Result value (fmap f roles)

typeRoles :: Result a -> Result a
typeRoles = mapRoles \case
  SourceRole span role modifiers | role `elem` ["term", "call"], "local" `notElem` modifiers -> SourceRole span "type" modifiers
  role -> role

headerRoles :: Result a -> Result a
headerRoles = mapRoles \case
  SourceRole span role _ | role `elem` ["term", "call"] -> SourceRole span "headerPattern" []
  role -> role

patternRoles :: Result a -> Result a
patternRoles = mapRoles \case
  SourceRole span "term" _ -> SourceRole span "parameter" ["declaration"]
  SourceRole span "call" _ -> SourceRole span "enumMember" []
  role -> role

-- a name bound by a value slot stayeth a term where it occurreth in a later
-- type, as `a` in `[@a: α, @b: α, a = b]`. the `local` modifier keepeth an
-- enclosing type position from recolouring it. only the tokens the parser
-- consumed are scanned, so the names do not leak into later declarations.
localTerms :: (a -> [String]) -> [Token] -> Result (a, [Token]) -> Result (a, [Token])
localTerms bound tokens result@(Result (Right (value, remaining)) _)
  | null names = result
  | otherwise = mapRoles mark result
  where
    names = bound value
    spans = [span | token@(TIdent name) <- take (length tokens - length remaining) tokens, name `elem` names, Just span <- [tokenSpan token]]
    mark = \case
      SourceRole span role modifiers
        | span `elem` spans,
          role `elem` ["term", "type", "call"] ->
            SourceRole span (if role == "call" then "call" else "term") ("local" : filter (/= "local") modifiers)
      role -> role
localTerms _ _ result = result

-- the names of slots whose type is not a sort.
valueNames :: [Parameter] -> [String]
valueNames parameters = [name | Parameter {parameterName = Just name, parameterType} <- parameters, name /= "_", not (sorted parameterType)]

sorted :: Expression -> Bool
sorted Universe = True
sorted (Product _ result) = sorted result
sorted _ = False

callable :: Expression -> Bool
callable (Product (_ : _) _) = True
callable Lambda {} = True
callable Cases {} = True
callable _ = False

markApplication :: Expression -> Result ()
markApplication (Application function _) = markFunction "call" function
markApplication _ = pure ()

markClass :: Expression -> Result ()
markClass (Product _ result) = markClass result
markClass (Application function _) = markFunction "class" function
markClass expression = markFunction "class" expression

markFunction :: String -> Expression -> Result ()
markFunction role (Located span (Name name)) | name /= "_" = emitRoles (Seq.singleton (SourceRole span role ["applied"]))
markFunction role (Located _ value) = markFunction role value
markFunction role (Application function _) = markFunction role function
markFunction _ _ = pure ()

-- use the strict parser on each recovery chunk. unindented declaration heads
-- bound recovery work, so unfinished brackets cannot rescan the whole buffer.
parseSourceRoles :: String -> [SourceRole]
parseSourceRoles source =
  lexical ++ case parseChunk tokens of
    Result (Right _) events -> toList events
    Result (Left _) events -> toList events ++ concatMap (toList . rolesOf . parseChunk) (chunks tokens)
  where
    tokens = map locatedToken (lexLocatedPrefix source)
    lexical = [SourceRole span "keyword" [] | token <- tokens, token `elem` [TAt, TKindStar], Just span <- [tokenSpan token]]
    parseChunk input = do
      (_, rest) <- locatedDeclarations input
      case rest of
        TYield : afterYield -> () <$ whole expression afterYield
        _ -> () <$ whole (\remaining -> pure ((), remaining)) rest
    chunks [] = []
    chunks (token : rest) = let (body, remaining) = break boundary rest in (token : body) : chunks remaining
    boundary token =
      token `elem` [TLet, TType, TClass, TInstance, TOrsend, TImport, TExport, TYield]
        && maybe False ((`Set.member` starts) . spanStart) (tokenSpan token)
    starts = Set.fromList (0 : lineStarts 0 source)
    lineStarts _ [] = []
    lineStarts offset (character : rest)
      | character == '\n' || character == '\r' = next : lineStarts next rest
      | otherwise = lineStarts next rest
      where
        next = offset + if fromEnum character > 0xffff then 2 else 1
