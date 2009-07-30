
Lexing utilities.

> module Lex ( whiteSpace
>            , symbol
>            , parens
>            , reservedOp
>            , identifier
>            , reserved
>            , natural
>            , lexeme
>            )
>   where

> import Prelude hiding (until)
> import qualified Data.Char as Char

Parsec 

> import Text.ParserCombinators.Parsec(Parser)
> import qualified Text.ParserCombinators.Parsec.Token as T
> import qualified Text.ParserCombinators.Parsec.Language as L

Lexer

> lexer :: T.TokenParser () 
> lexer = T.makeTokenParser 
>   (L.haskellDef { L.reservedOpNames = ["/\\","\\/","==>","<=>","~", "::", 
>                                        "+", "-", "*", "/", "^", "=", "<",
>                                        "<=", "<", ">", ">="] 
>                 , L.reservedNames = ["true", "false", "forall", "exists", "nil"]
>                 })

> whiteSpace :: Parser ()
> whiteSpace = T.whiteSpace lexer

> symbol :: String -> Parser String
> symbol = T.symbol lexer

> parens :: Parser a -> Parser a
> parens = T.parens lexer

> reservedOp :: String -> Parser ()
> reservedOp = T.reservedOp lexer

> identifier :: Parser String
> identifier = T.identifier lexer

> reserved :: String -> Parser ()
> reserved = T.reserved lexer

> natural :: Parser Integer
> natural = T.natural lexer

> lexeme :: Parser a -> Parser a
> lexeme = T.lexeme lexer
