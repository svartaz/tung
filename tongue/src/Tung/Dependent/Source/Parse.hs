-- | the dependent frontend reuseth the compiler lexer. annotations and bodies
-- pass through one expression parser; unsupported legacy forms are rejected.
module Tung.Dependent.Source.Parse
  ( SourceSnapshot (..),
    sourceSnapshot,
    recoverSnapshot,
    snapshotImportPaths,
    parseSource,
    parseProgram,
    parseExpression,
    SourceRole (..),
    parseSourceRoles,
    sourceTree,
    sourceSyntax,
  )
where

import Control.Monad (forM_, when)
import Data.Bifunctor (first)
import Data.Foldable (toList, traverse_)
import Data.List (isSuffixOf, nub)
import Data.Maybe (isJust)
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set qualified as Set
import GHC.Float (castDoubleToWord64)
import Tung.Concrete (NodeKind (..), Tree, concreteTree)
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
snapshotImportPaths snapshot =
  let (declarations, _, _) = recoverSnapshot snapshot
   in [importPath | (_, ImportDeclaration {importPath}) <- declarations]

-- token ranges and syntax roles from the shared expression parser.
data SourceRole = SourceRole SourceSpan String [String] deriving (Eq, Show)

-- roles and node marks survive a failure, so an unfinished buffer still
-- colours its parsed prefix. strict clients inspect only the result.
data Result a = Result (Either SourceFailure a) (Seq Mark)

-- a role for one token, the span of a concrete syntax node, or a local
-- binder's span with the span where it is seen.
data Mark = MarkRole SourceRole | MarkNode NodeKind SourceSpan | MarkScope SourceSpan SourceSpan

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

retain :: Seq Mark -> Result a -> Result a
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
parseProgramDetailed source = first (map snd) <$> parseProgramLocated source

-- each top-level declaration with the span of the name it declareth, or of its
-- keyword when it nameth nothing.
parseProgramLocated :: String -> Either SourceFailure ([(Maybe SourceSpan, Declaration)], Maybe Expression)
parseProgramLocated source = do
  tokens <- located source
  atEnd tokens (resultEither (program tokens))

-- a failure at the end of the input pointeth just past the last token.
atEnd :: [Token] -> Either SourceFailure a -> Either SourceFailure a
atEnd tokens = \case
  Left failure@SourceFailure {failureSpan = Nothing}
    | Just SourceSpan {spanEnd} <- last (Nothing : map tokenSpan tokens) -> Left failure {failureSpan = Just (SourceSpan spanEnd spanEnd)}
  result -> result

-- diagnostics may use complete declarations beside a parse error. only the
-- strict result may be compiled for execution or proof verification.
recoverSnapshot :: SourceSnapshot -> ([(Maybe SourceSpan, Declaration)], Maybe Expression, [SourceFailure])
recoverSnapshot SourceSnapshot {snapshotProgram = Right (declarations, yielded)} = (declarations, yielded, [])
recoverSnapshot SourceSnapshot {snapshotText, snapshotProgram = Left original} =
  let Recovery {..} = recover snapshotText
   in (recoveredDeclarations, recoveredYield, nub (original : recoveredFailures))

-- what one walk over a source recovereth: its complete declarations, a final
-- yield, the failures between them, and the marks for highlighting and the
-- concrete tree. a region the parser could not read is a broken node, and
-- its lines are parsed one by one for highlighting only.
data Recovery = Recovery
  { recoveredDeclarations :: [(Maybe SourceSpan, Declaration)],
    recoveredYield :: Maybe Expression,
    recoveredFailures :: [SourceFailure],
    recoveredMarks :: Seq Mark
  }

-- recovery resumeth at an unindented declaration outside every opened
-- delimiter; an unfinished literal, comment, or delimiter therefore limiteth it.
recover :: String -> Recovery
recover source = walk tokens
  where
    lexed = located source
    tokens = either (const (map locatedToken (lexLocatedPrefix source))) id lexed
    boundary = recoveryHead source
    walk [] = Recovery [] Nothing [] Seq.empty
    walk input@(TYield : _) = case marked DeclarationNode yielded input of
      Result (Right (yielded', [])) marks -> Recovery [] (Just yielded') [] marks
      Result (Right (_, rest)) _ -> failed input (Left (failureAt rest))
      Result (Left failure) _ -> failed input (Left failure)
    walk input = case marked DeclarationNode oneDeclaration input of
      Result (Right (declaration, following)) marks ->
        let rest = walk following
         in rest {recoveredDeclarations = (declarationNameSpan input, declaration) : recoveredDeclarations rest, recoveredMarks = marks <> recoveredMarks rest}
      Result (Left failure) _ -> failed input (Left failure)
    failureAt rest = SourceFailure (case rest of token : _ -> tokenSpan token; [] -> Nothing) "unexpected token; expected a declaration or the end of the input"
    failed input outcome =
      let following = resume input
          rest = walk following
          -- a lexical error already explaineth an incomplete token prefix.
          current = case (lexed, outcome) of
            (Left _, Left SourceFailure {failureSpan = Nothing}) -> []
            _ -> either pure (const []) (atEnd input outcome)
          broken = take (length input - length following) input
          lines' = concatMap (toList . rolesOf . program) (chunks broken)
          brokenNode = Seq.fromList [MarkNode BrokenNode span | Just span <- [consumedSpan input following]]
       in rest {recoveredFailures = current ++ recoveredFailures rest, recoveredMarks = brokenNode <> Seq.fromList lines' <> recoveredMarks rest}
    resume [] = []
    resume (token : rest) = seek (delimiters [] token) rest
    seek _ [] = []
    seek stack input@(token : rest)
      | null stack && boundary token = input
      | otherwise = seek (delimiters stack token) rest
    delimiters stack = \case
      TLParen -> TRParen : stack
      TLBracket -> TRBracket : stack
      TLBrace -> TRBrace : stack
      TBraceKeyword _ -> TRBrace : stack
      token | closing : rest <- stack, token == closing -> rest
      _ -> stack
    chunks [] = []
    chunks (token : rest) = let (body, remaining) = break boundary rest in (token : body) : chunks remaining

-- the concrete syntax tree of a source, complete or not.
sourceTree :: String -> Tree
sourceTree = (\(tree, _, _) -> tree) . sourceSyntax

-- the tree, the token roles, and the local scopes of one parse.
sourceSyntax :: String -> (Tree, [SourceRole], [(SourceSpan, SourceSpan)])
sourceSyntax source = (concreteTree (lexPieces source) [(kind, span) | MarkNode kind span <- marks], lexical ++ [role | MarkRole role <- marks], [(binder, scope) | MarkScope binder scope <- marks])
  where
    marks = toList case program (map locatedToken (lexLocatedPrefix source)) of
      Result (Right _) found -> found
      Result (Left _) _ -> recoveredMarks (recover source)
    lexical = [SourceRole span "keyword" [] | LocatedToken span token <- lexLocatedPrefix source, token `elem` [TAt, TKindStar]]

program :: [Token] -> Result ([(Maybe SourceSpan, Declaration)], Maybe Expression)
program tokens = do
  (found, rest) <- locatedDeclarations tokens
  case rest of
    TYield : _ -> (found,) . Just <$> whole (marked DeclarationNode yielded) rest
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

-- `yield` and the expression it yieldeth.
yielded :: Parser Expression
yielded = \case
  TYield : rest -> expression rest
  tokens -> failAt tokens "expected 'yield'"

-- each list requireth an item, including after a separator. a closed list also
-- consumeth its delimiter; other lists leave the following token to their owner.
separatedItems :: Token -> Parser a -> Parser [a]
separatedItems separator item tokens = do
  (first, rest) <- item tokens
  case rest of
    next : more | next == separator -> do
      (others, remaining) <- separatedItems separator item more
      pure (first : others, remaining)
    _ -> pure ([first], rest)

closedItems :: Token -> String -> Parser a -> Parser [a]
closedItems closing message item tokens = do
  (items, rest) <- separatedItems TComma item tokens
  case rest of
    next : remaining | next == closing -> pure (items, remaining)
    _ -> failAt rest message

locatedDeclarations :: Parser [(Maybe SourceSpan, Declaration)]
locatedDeclarations = declarationsUsing oneDeclaration

declarationsUsing :: Parser Declaration -> Parser [(Maybe SourceSpan, Declaration)]
declarationsUsing parser tokens = case tokens of
  [] -> pure ([], [])
  TYield : _ -> pure ([], tokens)
  TRBrace : _ -> pure ([], tokens)
  _ -> do
    (declaration, following) <- marked DeclarationNode parser tokens
    first ((declarationNameSpan tokens, declaration) :) <$> declarationsUsing parser following

declarationNameSpan :: [Token] -> Maybe SourceSpan
declarationNameSpan = \case
  TExport : rest@(_ : _) -> declarationNameSpan rest
  keyword : name@(TIdent _) : _ | keyword /= TExport -> tokenSpan name
  keyword : _ -> tokenSpan keyword
  [] -> Nothing

-- one declaration; `show` before a declaration wrapeth it.
oneDeclaration :: Parser Declaration
oneDeclaration tokens = case tokens of
  TLet : rest -> letDeclaration False rest
  TFix : rest -> letDeclaration True rest
  TType : rest -> inductiveDeclaration rest
  TClass : rest -> flockDeclaration rest
  TInstance : rest -> bizenDeclaration rest
  TOrsend : rest -> orsendDeclaration rest
  TImport : rest -> importDeclaration rest
  TExport : rest@(keyword : _) | keyword `elem` [TLet, TFix, TType, TClass, TOrsend] -> shown rest
  TExport : rest@(TIdent _ : _) -> first ReExportDeclaration <$> reexported [] rest
  TExport : _ -> failAt tokens "show must precede a let, fast, ilk, flock, or orsetting declaration or a name"
  _ -> failAt tokens "expected a declaration: let, fast, ilk, flock, bizen, orsetting, bring, or show"

-- `show a, b` re-exporteth visible names.
reexported :: [String] -> Parser [String]
reexported names tokens = case tokens of
  TIdent name : TComma : rest -> reexported (name : names) rest
  TIdent name : rest -> pure (reverse (name : names), rest)
  _ -> failAt tokens "expected a shown name"

-- `show` wrapeth exactly one following declaration.
shown :: Parser Declaration
shown tokens = first ShownDeclaration <$> oneDeclaration tokens

-- `flock name:[parameters, @:parent, *] { members }`. the signature endeth in `*`.
flockDeclaration :: Parser Declaration
flockDeclaration = scoped flockDeclarationBody

flockDeclarationBody :: Parser Declaration
flockDeclarationBody tokens@(TIdent name : TColon : rest) = localTerms memberNames tokens do
  plainName tokens name
  markFirst "class" (familyModifiers rest) tokens
  (signature, afterSignature) <- unscoped (typeRoles . atom) rest
  parameters <- case signature of
    Product parameters Universe -> pure parameters
    Universe -> pure []
    _ -> failAt rest "a flock signature endeth in '*'"
  case afterSignature of
    TLBrace : afterOpen -> first (FlockDeclaration name parameters) <$> flockMemberList afterOpen
    _ -> failAt afterSignature "expected '{' after flock signature"
  where
    -- value parameters and fields stay terms in the member types that use them.
    memberNames FlockDeclaration {flockParameters, flockMembers} =
      valueNames flockParameters ++ [name | FlockMember name ty <- flockMembers, not (sorted ty)]
    memberNames _ = []
flockDeclarationBody tokens = failAt tokens "expected flock name and ':signature'"

-- a family or flock with bracketed parameters is a type function.
familyModifiers :: [Token] -> [String]
familyModifiers signature = "declaration" : ["typeFunction" | TLBracket : _ <- [signature]]

-- all members use ordinary type expressions, including equality-valued laws.
flockMemberList :: Parser [FlockMember]
flockMemberList tokens = case tokens of
  TRBrace : rest -> pure ([], rest)
  TLet : named@(TIdent name : TColon : rest) -> do
    plainName named name
    (ty, afterType) <- typeRoles (expression rest)
    markNode DeclarationNode tokens afterType
    markFirst "call" ["declaration", "applied"] named
    first (FlockMember name ty :) <$> flockMemberList afterType
  _ -> failAt tokens "expected a flock member or '}'"

-- `bizen:type { lets }`. the type endeth before the opening brace, as match
-- scrutinees do. member bodies are ordinary declarations.
bizenDeclaration :: Parser Declaration
bizenDeclaration = scoped (bizenHeader False Nothing)

-- `fallback` and a priority may precede the colon, in that order.
bizenHeader :: Bool -> Maybe Integer -> Parser Declaration
bizenHeader fallback priority tokens = case tokens of
  marker@(TIdent "fallback") : rest | not fallback, Nothing <- priority -> markRole "keyword" [] marker >> bizenHeader True priority rest
  TNatural value : rest | Nothing <- priority -> bizenHeader fallback (Just (toInteger value)) rest
  TColon : rest -> do
    (parts, afterType) <- unscoped (typeRoles . applicationPartsUntil (== TLBrace)) rest
    ty <- liftAt rest (application parts)
    markClass ty
    case afterType of
      TLBrace : afterOpen -> do
        (located, afterMembers) <- declarationsUsing (memberRoles . oneDeclaration) afterOpen
        case afterMembers of
          TRBrace : remaining -> pure (BizenDeclaration priority fallback ty (map snd located), remaining)
          _ -> failAt afterMembers "expected '}' after bizen members"
      _ -> failAt afterType "expected '{' after bizen ilk"
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
      (ImportDeclaration path _, _) | not (".tung" `isSuffixOf` path) -> failAt tokens ("bring path '" ++ path ++ "' must end in '.tung'")
      _ -> pure result
  _ -> failAt tokens "expected a bring path"
  where
    go path (TDot : TIdent segment : remaining) = go (path ++ "." ++ segment) remaining
    go path aliased@(TIdent alias : remaining)
      | any (`elem` "~/") alias = failAt aliased ("bring alias '" ++ alias ++ "' must be one plain name")
      | otherwise = markFirst "namespace" ["declaration"] aliased >> pure (ImportDeclaration path (Just alias), remaining)
    go path remaining = pure (ImportDeclaration path Nothing, remaining)

inductiveDeclaration :: Parser Declaration
inductiveDeclaration = scoped inductiveDeclarationBody

inductiveDeclarationBody :: Parser Declaration
inductiveDeclarationBody tokens@(TIdent name : TColon : rest) = localTerms headerNames tokens do
  plainName tokens name
  markFirst "type" (familyModifiers rest) tokens
  -- the braces belong to the declaration. compound signatures can use a
  -- bracketed product or parentheses, leaving the opening brace unambiguous.
  (signature, afterSignature) <- unscoped (typeRoles . atom) rest
  case afterSignature of
    TLBrace : afterOpen -> first (InductiveDeclaration name signature) <$> constructorDeclarations afterOpen
    _ -> failAt afterSignature "expected '{' after ilk signature"
  where
    -- header parameters scope over the constructor annotations.
    headerNames = \case
      InductiveDeclaration {inductiveSignature = Product parameters _} -> valueNames parameters
      _ -> []
inductiveDeclarationBody tokens = failAt tokens "expected ilk name and ':signature'"

constructorDeclarations :: Parser [ConstructorDeclaration]
constructorDeclarations (TRBrace : rest) = pure ([], rest)
constructorDeclarations named@(TIdent name : TColon : tokens) = do
  plainName named name
  (annotation, afterAnnotation) <- typeRoles (expression tokens)
  markNode ItemNode named afterAnnotation
  markFirst (if callable annotation then "function" else "enumMember") ["declaration", "constructor"] named
  let constructor = ConstructorDeclaration name annotation
  case afterAnnotation of
    TComma : rest -> first (constructor :) <$> constructorDeclarations rest
    TRBrace : rest -> pure ([constructor], rest)
    _ -> failAt afterAnnotation "expected ',' or '}' after constructor"
constructorDeclarations tokens@(TIdent name : _) = failAt tokens ("constructor '" ++ name ++ "' requireth an ilk, as in '" ++ name ++ ":ilk'")
constructorDeclarations tokens = failAt tokens "expected constructor name"

-- a let header is one name; arguments are annotation slots. a `fast`
-- header is a let header with a required annotation.
letDeclaration :: Bool -> Parser Declaration
letDeclaration fixpoint = scoped (letDeclarationBody fixpoint)

letDeclarationBody :: Bool -> Parser Declaration
letDeclarationBody fixpoint tokens = do
  let keyword = if fixpoint then "fast" else "let"
  (name, afterHeader) <- case tokens of
    TIdent name : rest -> (name, rest) <$ plainName tokens name
    _ -> failAt tokens ("expected " ++ keyword ++ " name")
  (annotation, bodyTokens) <- case afterHeader of
    TColon : rest -> do
      (ty, afterType) <- unscoped (typeRoles . letAnnotation) rest
      case afterType of
        TEquals : body -> pure (Just ty, body)
        _ -> failAt afterType ("expected '≔' after " ++ keyword ++ " annotation")
    TEquals : _ | fixpoint -> failAt afterHeader "a fast declaration requireth an ilk annotation"
    TEquals : body -> pure (Nothing, body)
    _ -> failAt afterHeader ("expected ':' or '≔' after " ++ keyword ++ " name")
  let ty = fst <$> annotation
      typeDefinition = maybe False sorted ty
      modifiers = ["declaration"] ++ [if typeDefinition then "typeFunction" else "applied" | maybe False callable ty]
  markFirst (if typeDefinition then "type" else if maybe False callable ty then "function" else "variable") modifiers tokens
  case (bodyTokens, annotation) of
    (TText _ : TForeign : _, _) | fixpoint -> failAt bodyTokens "a fremmed binding is a let, not fast"
    (TText key : TForeign : remaining, Just (ty, written))
      | next : _ <- remaining,
        not (stopsExpression next) -> do
          (model, afterModel) <- expression remaining
          lowered <- liftAt remaining (lowerHeader annotation model)
          pure (HostDeclaration name ty key (Just lowered), afterModel)
      | any bindsInput written -> failAt bodyTokens "a fremmed annotation without a model cannot bind inputs"
      | otherwise -> pure (HostDeclaration name ty key Nothing, remaining)
    (TText _ : TForeign : _, Nothing) -> failAt bodyTokens "a fremmed binding requireth an ilk annotation"
    _ -> do
      (body, remaining) <- (if typeDefinition then typeRoles else id) (expression bodyTokens)
      when (not typeDefinition && not (maybe False callable ty) && callable body) (markFirst "function" ["declaration", "applied"] tokens)
      lowered <- liftAt bodyTokens (lowerHeader annotation body)
      pure (Declaration name (fst <$> annotation) lowered fixpoint, remaining)

-- a let annotation is a type. a bracket may also bind patterns, `pattern: type`,
-- and omit its result when its last slot bindeth, as in `[x:] = x`; the result
-- is then inferred. each written slot is returned beside the product.
letAnnotation :: Parser (Expression, [Slot])
letAnnotation tokens@(TLBracket : rest) = localTerms (valueNames . map slotParameter . snd) tokens $ case slots rest of
  Result (Right (parsedSlots, afterBracket@(TEquals : _))) events -> do
    emitRoles events
    let names = [name | Slot {slotParameter = Parameter {parameterName = Just name}} <- parsedSlots, name /= "_"]
        repeated name = length (filter (== name) names) > 1
        -- a repeated slot name may be a constructor, as in two `eftbend:`
        -- slots, so it becometh a pattern; matching rejecteth a variable
        -- bound twice once constructors are known.
        patterned = \case
          Slot parameter@Parameter {parameterPlicity = Explicit, parameterName = Just name} Nothing
            | repeated name -> Slot parameter (Just (Name name))
          other -> other
        written = map patterned parsedSlots
    distinctNames tokens [name | Slot {slotParameter = Parameter {parameterName = Just name}, slotPattern = Nothing} <- written, name /= "_"]
    pure
      ( case reverse written of
          Slot parameter@Parameter {parameterPlicity = Explicit, parameterName = Nothing} Nothing : reversed ->
            (Product (map slotParameter (reverse reversed)) (parameterType parameter), reverse reversed)
          _ -> (Product (map slotParameter written) Inferred, written),
        afterBracket
      )
  _ -> unslotted tokens
  where
    slots = closedItems TRBracket "expected ',' or ']' after bracket item" (marked ItemNode annotationSlot)
letAnnotation tokens = unslotted tokens

-- let annotations allow pattern slots. the colon selecteth a pattern
-- context only after its expression is parsed, so roles are emitted once.
annotationSlot :: Parser Slot
annotationSlot items = case items of
  TAt : _ -> named
  TIdent _ : TColon : _ -> named
  _ -> do
    let parsed = expression items
    (value, afterValue) <- deferred parsed
    case afterValue of
      TColon : afterColon -> do
        emitRoles (rolesOf (headerRoles parsed))
        (ty, remaining) <- typeRoles (slotType afterColon)
        pure (Slot (Parameter Explicit Nothing ty) (Just value), remaining)
      _ -> emitRoles (rolesOf parsed) >> pure (Slot (Parameter Explicit Nothing value) Nothing, afterValue)
  where
    named = first (`Slot` Nothing) <$> parameter items

unslotted :: Parser (Expression, [Slot])
unslotted tokens = first (,[]) <$> expression tokens

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
  parameterPlicity == Implicit || isJust parameterName || isJust slotPattern

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
stopsExpression token = token `elem` [TLet, TFix, TType, TImport, TExport, TClass, TInstance, TOrsend, TYield, TComma, TColon, TSemicolon, TEquals, TMapsTo, TRParen, TRBracket, TRBrace, TDollar]

parseArgument :: Parser Argument
parseArgument (TAt : rest) = first (Argument Implicit) <$> typeRoles (atom rest)
parseArgument tokens = first (Argument Explicit) <$> atom tokens

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
  TLBrace : rest -> lambda rest
  TFall : rest -> fall rest
  TLParen : rest@(keyword : _) | keyword `elem` [TLet, TFix, TImport, TExport] -> block rest
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
  (item, afterItem) <- marked ItemNode expression tokens
  case afterItem of
    TComma : rest -> first (item :) <$> compositionItems rest
    TRBrace : rest -> pure ([item], rest)
    _ -> failAt afterItem "expected ',' or '}' after composition item"

bracket :: Parser Expression
bracket = scoped bracketBody

bracketBody :: Parser Expression
bracketBody tokens = localTerms productNames tokens do
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
bracketItems = closedItems TRBracket "expected ',' or ']' after bracket item" (marked ItemNode parameter)

parameter :: Parser Parameter
parameter (TAt : token@(TIdent name) : TColon : rest) = namedParameter Implicit token name rest
-- `@:flock` is an anonymous requirement: an instance-searched implicit slot.
parameter (TAt : TColon : rest) = do
  (ty, remaining) <- typeRoles (expression rest)
  markClass ty
  pure (Parameter Implicit Nothing ty, remaining)
parameter tokens@(TAt : _) = failAt tokens "implicit parameters require '@name:ilk' or '@:requirement'"
parameter (token@(TIdent name) : TColon : rest) = namedParameter Explicit token name rest
parameter tokens = first (Parameter Explicit Nothing) <$> typeRoles (expression tokens)

-- a declared name is unqualified; `~` only reacheth an import.
plainName :: [Token] -> String -> Result ()
plainName tokens name
  | '~' `elem` name && name /= "~" = failAt tokens ("declared name '" ++ name ++ "' must be unqualified")
  | otherwise = pure ()

-- a bracket nameth each slot once.
distinctNames :: [Token] -> [String] -> Result ()
distinctNames tokens names = case repeatedNames names of
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
  -- a repeated bare name may be a constructor, as in `{eftbend, eftbend ^ …}`,
  -- so such a row is a case function; elaboration rejecteth a variable bound
  -- twice once constructors are resolved.
  pure case groups of
    [([items], body)]
      | Just binders <- traverse plainBinder items,
        null (repeatedNames [name | Binder {binderName = Just name} <- binders]) ->
          (Lambda binders body, remaining)
    _ -> (Cases [Row (map rowPattern items) body | (alternatives, body) <- groups, items <- alternatives], remaining)
  where
    plainBinder = \case
      Left binder -> Just binder
      Right (Name name) -> Just (Binder Explicit (bindingName name) Nothing)
      Right Wildcard -> Just (Binder Explicit Nothing Nothing)
      Right _ -> Nothing

-- rows end at '}'. each row hath `;`-separated alternatives before '^'.
caseGroups :: Parser [([[Either Binder Expression]], Expression)]
caseGroups = closedItems TRBrace "expected ',' or '}' after a case" (marked RowNode (scoped group))
  where
    group tokens = do
      (alternatives, afterPatterns) <- rowAlternatives tokens
      case afterPatterns of
        TMapsTo : rest -> first (alternatives,) <$> expression rest
        _ -> failAt afterPatterns "expected '^' after patterns"

rowAlternatives :: Parser [[Either Binder Expression]]
rowAlternatives = separatedItems TSemicolon rowItems

rowItems :: Parser [Either Binder Expression]
rowItems = separatedItems TComma rowItem

-- `@x`, `x:type`, and `x` are binders; any other expression is a pattern.
rowItem :: Parser (Either Binder Expression)
rowItem tokens = case tokens of
  TAt : _ -> first Left <$> lambdaBinder tokens
  TIdent _ : TColon : _ -> first Left <$> lambdaBinder tokens
  _ -> first Right <$> patternRoles (expression tokens)

-- a binder in a pattern row is a variable pattern.
rowPattern :: Either Binder Expression -> Expression
rowPattern = either (\(Binder _ name _) -> maybe Wildcard Name name) id

-- `match a, b { rows }`. scrutinees end at the opening brace.
matchExpression :: Parser Expression
matchExpression tokens = do
  (scrutinees, afterScrutinees) <- scrutineeList tokens
  first (Match scrutinees) <$> rowsAfter afterScrutinees
  where
    rowsAfter = \case
      TLBrace : TRBrace : remaining -> pure ([], remaining)
      TLBrace : rest -> do
        (groups, remaining) <- caseGroups rest
        pure ([Row (map rowPattern items) body | (alternatives, body) <- groups, items <- alternatives], remaining)
      afterHeader -> failAt afterHeader "expected '{' after match scrutinees"
    scrutineeList = separatedItems TComma scrutinee
    scrutinee ts = do
      (parts, afterParts) <- applicationPartsUntil (== TLBrace) ts
      initial <- liftAt ts (application parts)
      dollarsUntil (== TLBrace) initial afterParts

-- `fall params, result ^ body` is a lambda checked against its written
-- product. a bare slot bindeth an input that the body cannot name.
fall :: Parser Expression
fall = scoped fallBody

fallBody :: Parser Expression
fallBody tokens = do
  (items, afterItems) <- fallItems tokens
  case reverse items of
    Parameter Explicit Nothing result : reversed@(_ : _) -> do
      let parameters = reverse reversed
          binders = [Binder parameterPlicity (parameterName >>= bindingName) Nothing | Parameter {parameterPlicity, parameterName} <- parameters]
      (body, remaining) <- expression afterItems
      pure (Ascription (Lambda binders body) (Product parameters result), remaining)
    _ -> failAt tokens "fall requireth at least one input and a final result ilk"

fallItems :: Parser [Parameter]
fallItems = closedItems TMapsTo "expected ',' or '^' after fall item" parameter

lambdaBinder :: Parser Binder
lambdaBinder (TAt : rest) = binder Implicit rest
lambdaBinder rest = binder Explicit rest

-- a typed or implicit binder is a parameter of its row.
binder :: Plicity -> Parser Binder
binder plicity tokens@(TIdent name : TColon : rest) = do
  markFirst "parameter" ["declaration"] tokens
  (annotation, remaining) <- typeRoles (expression rest)
  pure (Binder plicity (bindingName name) (Just annotation), remaining)
binder plicity tokens@(TIdent name : rest) = markFirst "parameter" ["declaration"] tokens >> pure (Binder plicity (bindingName name) Nothing, rest)
binder _ tokens = failAt tokens "a typed or implicit binder requireth a name"

block :: Parser Expression
block tokens = do
  (located, rest) <- locatedDeclarations tokens
  let bindings = map snd located
  when (any isInductive bindings) (failAt tokens "ilk declarations must be top-level")
  when (any isHost bindings) (failAt tokens "fremmed bindings must be top-level")
  when (any isFixpoint bindings) (failAt tokens "fast declarations must be top-level")
  when (any isModuleLevel bindings) (failAt tokens "bring and show must be top-level")
  case rest of
    TYield : _ -> do
      (body, afterBody) <- marked ItemNode yielded rest
      case afterBody of
        TRParen : remaining -> do
          -- a local let is seen by the rest of its block, its own body included.
          forM_ (consumedSpan tokens remaining) \(SourceSpan _ end) ->
            emitRoles (Seq.fromList [MarkScope span (SourceSpan (spanStart span) end) | (Just span, Declaration {}) <- located])
          pure (Block bindings body, remaining)
        _ -> failAt afterBody "expected ')' after block result"
    _ -> failAt rest "expected 'yield' after local bindings"
  where
    isInductive InductiveDeclaration {} = True
    isInductive _ = False
    isHost HostDeclaration {} = True
    isHost _ = False
    isFixpoint Declaration {declarationFixpoint} = declarationFixpoint
    isFixpoint _ = False
    isModuleLevel ImportDeclaration {} = True
    isModuleLevel ShownDeclaration {} = True
    isModuleLevel ReExportDeclaration {} = True
    isModuleLevel _ = False

-- successful speculative parses defer their events until a delimiter selecteth
-- the context; failures retain their parsed prefix.
deferred :: Result a -> Result a
deferred result@(Result (Left _) _) = result
deferred (Result value _) = Result value Seq.empty

rolesOf :: Result a -> Seq Mark
rolesOf (Result _ roles) = roles

emitRoles :: Seq Mark -> Result ()
emitRoles = Result (Right ())

-- the node covering the tokens consumed between two token lists.
markNode :: NodeKind -> [Token] -> [Token] -> Result ()
markNode kind tokens rest = traverse_ (emitRoles . Seq.singleton . MarkNode kind) (consumedSpan tokens rest)

-- the binders a construct declareth are seen from themselves to the
-- construct's end, unless an inner construct already gave them a scope.
scoped :: Parser a -> Parser a
scoped parser tokens = case parser tokens of
  Result outcome@(Right (_, rest)) marks
    | Just (SourceSpan _ end) <- consumedSpan tokens rest ->
        let done = Set.fromList [binder | MarkScope binder _ <- toList marks]
            binders = [span | MarkRole (SourceRole span role _) <- toList marks, role `elem` ["typeParameter", "headerPattern", "parameter"], Set.notMember span done]
         in Result outcome (marks <> Seq.fromList [MarkScope span (SourceSpan (spanStart span) end) | span <- nub binders])
  result -> result

-- a declaration's header is seen by the whole declaration, so the header's
-- own bracket, which endeth with it, giveth its binders no narrower scope. an
-- inner construct's scope, as a lambda's or an inner bracket's, endeth
-- earlier and is kept.
unscoped :: Parser a -> Parser a
unscoped parser tokens = case parser tokens of
  Result outcome@(Right (_, rest)) marks
    | Just (SourceSpan _ end) <- consumedSpan tokens rest ->
        Result outcome (Seq.filter (\case MarkScope _ (SourceSpan _ scopeEnd) -> scopeEnd /= end; _ -> True) marks)
  result -> result

marked :: NodeKind -> Parser a -> Parser a
marked kind parser tokens = do
  (value, rest) <- parser tokens
  markNode kind tokens rest
  pure (value, rest)

markRole :: String -> [String] -> Token -> Result ()
markRole _ _ (TIdent "_") = pure ()
markRole role modifiers token = maybe (pure ()) (\span -> emitRoles (Seq.singleton (MarkRole (SourceRole span role modifiers)))) (tokenSpan token)

markFirst :: String -> [String] -> [Token] -> Result ()
markFirst role modifiers = traverse_ (markRole role modifiers) . take 1

-- a member keepeth its callable role; nested declarations keep their own roles.
memberRoles :: Result a -> Result a
memberRoles (Result value roles) = Result value $ case Seq.findIndexL binding roles of
  Just index -> Seq.adjust' member index roles
  Nothing -> roles
  where
    binding = \case
      MarkRole (SourceRole _ role modifiers) -> role `elem` ["function", "variable"] && "declaration" `elem` modifiers
      _ -> False
    member (MarkRole (SourceRole span "function" modifiers)) = MarkRole (SourceRole span "call" modifiers)
    member mark = mark

mapRoles :: (SourceRole -> SourceRole) -> Result a -> Result a
mapRoles f (Result value marks) = Result value (fmap mark marks)
  where
    mark = \case
      MarkRole role -> MarkRole (f role)
      node -> node

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
            SourceRole span (if role == "call" || "applied" `elem` modifiers then "call" else "term") ("local" : filter (/= "local") modifiers)
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
markFunction role (Located span (Name name)) | name /= "_" = emitRoles (Seq.singleton (MarkRole (SourceRole span role ["applied"])))
markFunction role (Located _ value) = markFunction role value
markFunction role (Application function _) = markFunction role function
markFunction _ _ = pure ()

-- unindented declaration heads bound recovery work, so unfinished brackets
-- cannot rescan the whole buffer.
parseSourceRoles :: String -> [SourceRole]
parseSourceRoles = (\(_, roles, _) -> roles) . sourceSyntax

-- both diagnostic recovery and highlighting resume only at source line starts.
-- lexer offsets use UTF-16 code units, including supplementary characters.
recoveryHead :: String -> Token -> Bool
recoveryHead source = boundary
  where
    boundary token =
      token `elem` [TLet, TFix, TType, TClass, TInstance, TOrsend, TImport, TExport, TYield]
        && maybe False ((`Set.member` starts) . spanStart) (tokenSpan token)
    starts = Set.fromList (0 : lineStarts 0 source)
    lineStarts _ [] = []
    lineStarts offset (character : rest)
      | character == '\n' || character == '\r' = next : lineStarts next rest
      | otherwise = lineStarts next rest
      where
        next = offset + if fromEnum character > 0xffff then 2 else 1
