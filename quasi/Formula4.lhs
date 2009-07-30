
{-# LANGUAGE DeriveDataTypeable #-}

> module Formula4 ( Formula(..)
>                 , Prop(..)
>                 , Term(..)
>                 , Fol(..)
>                 , f
>                 , p
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
 
> import qualified Data.Generics as G
> import qualified Language.Haskell.TH as TH
> import qualified Language.Haskell.TH.Quote as Q
> import Language.Haskell.TH.Quote (QuasiQuoter(..))

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
>                | AntiQuote String
>   deriving(Show, Typeable, Data)

Propositional variables.

> data Prop = P String
>   deriving (Eq, Show, Typeable, Data)

First order terms

> data Term = Var String
>           | Fn String [Term]
>   deriving (Eq, Show, Typeable, Data)

> data Fol = R String [Term]
>   deriving (Eq, Show, Typeable, Data)

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

> antiExpr :: Parser (Formula a)
> antiExpr = lexeme $ do{ symbol "$"; id <- identifier; return $ AntiQuote id }

> atomicFormula :: Parser a -> Parser (Formula a)
> atomicFormula p = do reserved "true"
>                      return Top
>               <|> do reserved "false"
>                      return Bot
>               <|> antiExpr
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

> parseProp :: Parser Prop
> parseProp = do p <- identifier
>                return $ P p

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

> parseFol :: Parser Fol
> parseFol = 
>       P.try (do t1 <- term
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

> makeParser :: Monad m => Parser a -> String -> m (Formula a)
> makeParser atomParser input = 
>   case P.runParser p () "" input of
>     Left err -> fail $ show err
>     Right e -> return e
>  where p = do whiteSpace
>               x <- formula atomParser
>               P.eof 
>               return x

> parsePropFormula :: Monad m => String -> m (Formula Prop)
> parsePropFormula = makeParser parseProp

> parseFolFormula :: Monad m => String -> m (Formula Fol)
> parseFolFormula = makeParser parseFol

Prop

> quoteFormExpP :: String -> TH.ExpQ
> quoteFormPatP :: String -> TH.PatQ

> prop, p :: QuasiQuoter
> prop = QuasiQuoter quoteFormExpP quoteFormPatP
> p = prop

> quoteFormExpP s = do form <- parsePropFormula s
>                      Q.dataToExpQ (const Nothing `G.extQ` antiFormExpP) form

> antiFormExpP :: Formula Prop -> Maybe (TH.Q TH.Exp)

> antiFormExpP (AntiQuote v) = Just $ TH.varE (TH.mkName v)
> antiFormExpP _             = Nothing


> quoteFormPatP s =  do form <- parsePropFormula s
>                       Q.dataToPatQ (const Nothing `G.extQ` antiFormPatP) form

> antiFormPatP :: Formula Prop -> Maybe (TH.Q TH.Pat)
> antiFormPatP (AntiQuote v) = Just $ TH.varP  (TH.mkName v)
> antiFormPatP _             = Nothing

Fol

> fol, f :: QuasiQuoter
> fol = QuasiQuoter quoteFormExpF quoteFormPatF
> f = fol

> quoteFormExpF s = do form <- parseFolFormula s
>                      Q.dataToExpQ (const Nothing `G.extQ` antiFormExpF) form

> antiFormExpF :: Formula Fol -> Maybe (TH.Q TH.Exp)

> antiFormExpF (AntiQuote v) = Just $ TH.varE (TH.mkName v)
> antiFormExpF _             = Nothing


> quoteFormPatF s =  do form <- parseFolFormula s
>                       Q.dataToPatQ (const Nothing `G.extQ` antiFormPatF) form

> antiFormPatF :: Formula Fol -> Maybe (TH.Q TH.Pat)
> antiFormPatF (AntiQuote v) = Just $ TH.varP  (TH.mkName v)
> antiFormPatF _             = Nothing
