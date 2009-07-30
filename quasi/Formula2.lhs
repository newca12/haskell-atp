
{-# LANGUAGE DeriveDataTypeable #-}

> module Formula2 ( Formula(..)
>                 , Prop(..)
>                 , Term(..)
>                 , Fol(..)
>                 , parseProp
>                 , parse
>                 )

> where

> import Prelude 
> import qualified Language.Haskell.TH as TH
> import qualified Data.Typeable as Typeable
> import Data.Typeable (Typeable)
> import qualified Data.Data as Data
> import Data.Data (Data)
> import qualified Text.ParserCombinators.Parsec as P
> import Text.ParserCombinators.Parsec (Parser, (<|>), (<?>))
> import qualified Text.ParserCombinators.Parsec.Expr as E
> import qualified Text.ParserCombinators.Parsec.Token as T
> import qualified Text.ParserCombinators.Parsec.Language as L
> import qualified Text.ParserCombinators.Parsec.Combinator as C

Formulas

> data Formula a = Atom a
>                | Top
>                | Bot
>                | Not (Formula a)
>                | And (Formula a) (Formula a)
>                | Or (Formula a) (Formula a)
>                | Imp (Formula a) (Formula a)
>                | Iff (Formula a) (Formula a)
>                | All String (Formula a)
>                | Ex String (Formula a)
>   deriving(Show, Typeable, Data)

Propositional variables.

> data Prop = P String
>   deriving (Eq, Show)

First order terms

> data Term = Var String
>           | Fn String [Term]
>   deriving (Eq, Show)

> data Fol = R String [Term]
>   deriving (Eq, Show)

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

Formula parser

> formula :: Parser a -> Parser (Formula a)
> formula p = E.buildExpressionParser formulaTable (atomicFormula p) <?> "formula" 

> formulaTable :: E.OperatorTable Char () (Formula a)
> formulaTable = [ [op "/\\" And E.AssocRight] 
>                , [op "\\/" Or  E.AssocRight]
>                , [op "==>" Imp E.AssocRight]
>                , [op "<=>" Imp E.AssocRight]
>                ] 
>   where op s f assoc = E.Infix (do { reservedOp s; return f }) assoc 

> atomicFormula :: Parser a -> Parser (Formula a)
> atomicFormula p = do reserved "true"
>                      return Top
>               <|> do reserved "false"
>                      return Bot
>               <|> do v <- p
>                      return $ Atom v
>               <|> do symbol "~" 
>                      f <- atomicFormula p
>                      return $ Not f
>               <|> do reserved "forall"
>                      x <- identifier
>                      symbol "."
>                      b <- formula p
>                      return $ All x b
>               <|> do reserved "exists"
>                      x <- identifier
>                      symbol "."
>                      b <- formula p
>                      return $ Ex x b
>               <|> parens (formula p)
>               <?> "atomic formula"

Prop parser

> prop :: Parser Prop
> prop = do p <- identifier
>           return $ P p

Term parser

> term :: Parser Term
> term = E.buildExpressionParser termTable atomicTerm <?> "term" 

> termTable :: E.OperatorTable Char () Term
> termTable = [ [op "^"  (fn "^")  E.AssocLeft] 
>             , [op "/"  (fn "/")  E.AssocLeft]
>             , [op "*"  (fn "*")  E.AssocRight]
>             , [op "-"  (fn "-")  E.AssocLeft]
>             , [op "+"  (fn "+")  E.AssocRight]
>             , [op "::" (fn "::") E.AssocRight]
>             ] 
>   where op s f assoc = E.Infix (do { reservedOp s; return f }) assoc 
>         fn op t1 t2 = Fn op [t1, t2]

> atomicTerm :: Parser Term
> atomicTerm = parens term
>          <|> do n <- natural
>                 return $ Fn (show n) []
>          <|> do reserved "nil" 
>                 return $ Fn "nil" []
>          <|> do symbol "-" 
>                 t <- atomicTerm
>                 return $ Fn "-" [t]
>          <|> P.try (do f <- identifier
>                        ts <- parens $ C.sepBy term (symbol ",")
>                        return $ Fn f ts)
>          <|> do x <- identifier
>                 return $ Var x
>          <?> "atomic term"

Atomic first order formula parser

> fol :: Parser Fol
> fol = P.try (do t1 <- term
>                 op <- C.choice (map symbol ["=", ">", ">=", "<", "<="])
>                 t2 <- term
>                 return $ R op [t1, t2])
>   <|> P.try (do p <- identifier
>                 ts <- parens $ C.sepBy term (symbol ",")
>                 return $ R p ts)
>   <|> do p <- identifier
>          return $ R p []
>   <?> "relation"

Package it up.

> run :: Show a => Parser a -> String -> Either P.ParseError a
> run p input = P.parse p "" input

> runLex :: Show a => Parser a -> String -> Either P.ParseError a
> runLex p input = run
>   (do whiteSpace
>       x <- p 
>       P.eof 
>       return x) input 

> parseProp :: String -> Either P.ParseError (Formula Prop)
> parseProp = runLex (formula prop)

> parse :: String -> Either P.ParseError (Formula Fol)
> parse = runLex (formula fol)

