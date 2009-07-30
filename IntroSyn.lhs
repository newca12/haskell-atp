
A simple expression language.  Abstract syntax.

E ::= P + E | P
P ::= A + P | A
A ::= ( E ) | Int | Var

Int = [0-9]+
Var = [a-zA-Z][a-zA-Z0-9]*

Note that by this grammar, '+' and '*' are right associative.

> module IntroSyn ( Expr(..)
>                 , expr
>                 ) where

> import Prelude
> import qualified Data.Char as Char

Parsing 

> import qualified Text.ParserCombinators.Parsec as P
> import Text.ParserCombinators.Parsec (Parser, (<|>), (<?>))
> import qualified Text.ParserCombinators.Parsec.Expr as E
> import qualified Lex

Quotations 
 
> import qualified Data.Generics as G
> import Data.Generics(Typeable, Data)
> import qualified Language.Haskell.TH as TH
> import qualified Language.Haskell.TH.Quote as Q
> import Language.Haskell.TH.Quote (QuasiQuoter(..))

Printing

> import qualified Text.PrettyPrint.HughesPJClass as PP
> import Text.PrettyPrint.HughesPJClass(Pretty, (<+>))

-- -----------------------------------------------------------------------------
--  Syntax                                                                      
-- -----------------------------------------------------------------------------

> data Expr = Var String
>           | Const Integer
>           | Add Expr Expr
>           | Mul Expr Expr
>           | AntiQuote String
>   deriving (Typeable, Data)

For example

Add (Mul (Const 2) (Var "x")) (Var "y")

-- -----------------------------------------------------------------------------
--  Parsing                                                                     
-- -----------------------------------------------------------------------------

> parseExpr :: Parser Expr
> parseExpr = E.buildExpressionParser table atomic <?> "expr" 

> table :: E.OperatorTable Char () Expr
> table = [ [op "*" Mul E.AssocRight] 
>         , [op "+" Add E.AssocRight]
>         ] 
>   where op s f assoc = E.Infix (do{ Lex.reservedOp s; return f }) assoc 
  
> antiExpr :: Parser Expr
> antiExpr = Lex.lexeme $ do Lex.symbol "$"
>                            id <- Lex.identifier
>                            return $ AntiQuote ("id:" ++ id)
>                     <|> do Lex.symbol "^"
>                            id <- Lex.identifier
>                            return $ AntiQuote ("co:" ++ id)

> atomic :: Parser Expr
> atomic = do n <- Lex.natural
>             return $ Const n
>      <|> antiExpr
>      <|> do x <- Lex.identifier
>             return $ Var x
>      <|> Lex.parens parseExpr
>      <?> "atomic expr"

> parse :: Monad m => String -> m Expr
> parse input = 
>   case P.runParser p () "" input of
>     Left err -> fail $ show err
>     Right e -> return e
>  where p = do Lex.whiteSpace
>               x <- parseExpr
>               P.eof 
>               return x

-- -----------------------------------------------------------------------------
--  Quotations                                                                  
-- -----------------------------------------------------------------------------

> quoteExprExp :: String -> TH.ExpQ
> quoteExprPat :: String -> TH.PatQ

> expr :: QuasiQuoter
> expr = QuasiQuoter quoteExprExp quoteExprPat

> quoteExprExp s = do e <- parse s
>                     Q.dataToExpQ (const Nothing `G.extQ` antiExprExp) e

> antiExprExp :: Expr -> Maybe (TH.Q TH.Exp)
> antiExprExp (AntiQuote v) = 
>   let (front, back) = splitAt 3 v in
>   case front of 
>     "id:" -> Just $ TH.varE (TH.mkName back)
>     "co:" -> Just $ TH.appE (TH.conE $ TH.mkName "Const") (TH.varE $ TH.mkName back) 
> antiExprExp _ = Nothing


> quoteExprPat s =  do e <- parse s
>                      Q.dataToPatQ (const Nothing `G.extQ` antiExprPat) e

> antiExprPat :: Expr -> Maybe (TH.Q TH.Pat)
> antiExprPat (AntiQuote v) = 
>   let (front, back) = splitAt 3 v in
>   case front of 
>     "id:" -> Just $ TH.varP (TH.mkName back)
>     "co:" -> Just $ TH.conP (TH.mkName "Const") [TH.varP (TH.mkName back)]
> antiExprPat _ = Nothing

-- -----------------------------------------------------------------------------
--  Printing                                                                    
-- -----------------------------------------------------------------------------

Print "+" and "*" as right associative by including
a precedence argument.

We use the Hughes pretty printing library for layout.

> instance Show Expr where
>   show = PP.prettyShow

> instance Pretty Expr where
>   pPrint = pp' 0

> pp' :: Int -> Expr -> PP.Doc
> pp' _ (Var s) = PP.text s
> pp' _ (Const n) = PP.integer n
> pp' pr (Add e1 e2) = 
>      let doc1 = pp' 3 e1 
>          doc2 = pp' 2 e2 
>          doc3 = doc1 <+> PP.text "+" <+> doc2 in
>      if pr > 2 then PP.parens doc3 else doc3
> pp' pr (Mul e1 e2) = 
>      let doc1 = pp' 5 e1 
>          doc2 = pp' 4 e2 
>          doc3 = doc1 <+> PP.text "*" <+> doc2 in
>      if pr > 4 then PP.parens doc3 else doc3
> pp' _ (AntiQuote _) = error "unfilled antiquote"

