
{-# LANGUAGE DeriveDataTypeable #-}

> module Formula ( Formula(..)
>                , parse
>                )
>                  where

> import Prelude 

Template Haskell

> import qualified Language.Haskell.TH as TH
> import qualified Data.Typeable as Typeable
> import Data.Typeable (Typeable)
> import qualified Data.Data as Data
> import Data.Data (Data)
> import qualified Data.Generics as Generics

Parsec 

> import qualified Text.ParserCombinators.Parsec as P
> import Text.ParserCombinators.Parsec (Parser, (<|>), (<?>))
> import qualified Text.ParserCombinators.Parsec.Expr as E
> import qualified Text.ParserCombinators.Parsec.Token as T
> import qualified Text.ParserCombinators.Parsec.Language as L

> data Formula = Atom String
>              | Top
>              | Bot
>              | Not Formula
>              | And Formula Formula
>              | Or Formula Formula
>              | Imp Formula Formula
>              | Iff Formula Formula
>              | AntiQuote String
>   deriving(Show, Typeable, Data)

Lexer

> lexer :: T.TokenParser () 
> lexer = T.makeTokenParser 
>   (L.haskellDef { L.reservedOpNames = ["/\\","\\/","==>","<=>","~"] 
>                 , L.reservedNames = ["true", "false"]
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

> lexeme :: Parser a -> Parser a
> lexeme = T.lexeme lexer

Parser

> formula :: Parser Formula
> formula = E.buildExpressionParser table atomic <?> "formula" 

let f x =
    5

> table :: E.OperatorTable Char () Formula
> table = [ [op "/\\" And E.AssocRight] 
>         , [op "\\/" Or  E.AssocRight]
>         , [op "==>" Imp E.AssocRight]
>         , [op "<=>" Imp E.AssocRight]
>         ] 
>   where op s f assoc = E.Infix (do{ reservedOp s; return f }) assoc 
 
> antiExpr = lexeme $ do{ symbol "$"; id <- identifier; return $ AntiQuote id }

> atomic :: Parser Formula
> atomic = do reserved "true"
>             return Top
>      <|> antiExpr
>      <|> do reserved "false"
>             return Bot
>      <|> do p <- identifier
>             return $ Atom p
>      <|> do symbol "~" 
>             f <- atomic  
>             return $ Not f
>      <|> parens formula 
>      <?> "atomic formula"

instance  Monad Maybe  where
    (Just x) >>= k      = k x
    Nothing  >>= _      = Nothing

    (Just _) >>  k      = k
    Nothing  >>  _      = Nothing

    return              = Just
    fail _              = Nothing

> parse :: Monad m => String -> m Formula
> parse input = 
>   case P.runParser p () "" input of
>     Left err -> fail $ show err
>     Right e -> return e
>  where p = do whiteSpace
>               x <- formula
>               P.eof 
>               return x
