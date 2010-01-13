
* Signature

> module ATP.Util.Lex 
>   ( -- * Parser constructors
>     genParser
>   , genParser'
>   , makeParser
>   , makeParser'
>   , genFileParser
>   , makeFileParser
>     -- * Lexers
>   , upperIdentifier
>   , lowerIdentifier
>   , identifier
>   , int
>   , integer
>   , reserved
>   , reservedOp
>   , parens
>   , brackets
>   , braces
>   , dot
>   , comma
>   , colon
>   , symbol
>   )
> where

* Imports

> import Prelude 
> import qualified ATP.Util.Monad as M
> import qualified Text.ParserCombinators.Parsec as P
> import Text.ParserCombinators.Parsec (Parser)
> import qualified Text.ParserCombinators.Parsec.Char as C
> import qualified Text.ParserCombinators.Parsec.Language as L
> import qualified Text.ParserCombinators.Parsec.Token as T

* Lexer

Use the Haskell lexer for identifier conventions.

> lang :: L.LanguageDef ()
> lang = L.emptyDef 
>   { L.reservedOpNames = [ "/\\", "∧"
>                         , "\\/", "∨" 
>                         , "==>", "⊃"
>                         , "<=>", "⇔"
>                         , "~", "¬"
>                         , "::", "+", "-", "*", "/", "^"
>                         , "=", "<", "<=", "≤", ">", ">=", "≥" 
>                         , ":-", "%"
>                         ] 
>   , L.reservedNames = [ "true", "⊤"
>                       , "false", "⊥"
>                       , "forall", "∀"
>                       , "exists", "∃"
>                       , "nil" ]
>   , L.commentLine = "--"
>   }

> lexer :: T.TokenParser () 
> lexer = T.makeTokenParser lang

> whiteSpace :: Parser ()
> whiteSpace = T.whiteSpace lexer

> comma, colon, dot :: Parser ()
> comma = M.ignore $ T.comma lexer
> colon = M.ignore $ T.colon lexer
> dot = M.ignore $ T.dot lexer

> parens, brackets, braces :: Parser a -> Parser a
> parens = T.parens lexer
> brackets = T.brackets lexer
> braces = T.braces lexer

> reservedOp :: String -> Parser ()
> reservedOp = T.reservedOp lexer

> identifier :: Parser String
> identifier = T.identifier lexer

> lowerIdentifier :: Parser String
> lowerIdentifier = T.lexeme lexer 
>                    (do x <- C.lower
>                        xs <- P.many (L.identLetter lang)
>                        return $ x : xs)

> upperIdentifier :: Parser String
> upperIdentifier = T.lexeme lexer
>                    (do x <- C.upper
>                        xs <- P.many (L.identLetter lang)
>                        return $ x : xs)

> reserved :: String -> Parser ()
> reserved = T.reserved lexer

> integer :: Parser Integer
> integer = T.integer lexer

> int :: Parser Int
> int = integer >>= return . fromIntegral

> symbol :: String -> Parser String
> symbol = T.symbol lexer

* Parsers

> genParser' :: Parser () -> Parser a -> String -> Maybe a
> genParser' space p input = 
>   case P.runParser p' () "" input of
>     Left _ -> Nothing
>     Right e -> Just e
>  where p' = do space
>                x <- p
>                P.eof 
>                return x

> genParser :: Parser () -> Parser a -> String -> a
> genParser space p input = 
>   case P.runParser p' () "" input of
>     Left err -> error $ "Parse error: " ++ show err
>     Right e -> e
>  where p' = do space
>                x <- p
>                P.eof 
>                return x

> makeParser' :: Parser a -> String -> Maybe a
> makeParser' = genParser' whiteSpace

> makeParser :: Parser a -> String -> a
> makeParser = genParser whiteSpace

> genFileParser :: Parser () -> Parser a -> String -> IO a
> genFileParser space p file = 
>   do res <- P.parseFromFile p' file 
>      case res of 
>        Left err -> fail $ show err
>        Right e -> return e
>  where p' = do space
>                x <- p
>                P.eof 
>                return x

> makeFileParser ::Parser a -> String -> IO a
> makeFileParser = genFileParser whiteSpace

