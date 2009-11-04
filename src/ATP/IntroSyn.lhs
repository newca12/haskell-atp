
A simple expression language.  Abstract syntax.

E ::= P + E | P
P ::= A + P | A
A ::= ( E ) | Int | Var

Int = [0-9]+
Var = [a-zA-Z][a-zA-Z0-9]*

Note that by this grammar, '+' and '*' are right associative.

Expressions can be constructed using Template Haskell syntax.
E.g.

[$exp| 1 + 2 |]
[$exp| x + 2 * y |]

In pattern matching, to antiquote an Expr, use $e.  To antiquote a
Const use ^c. E.g.

case e of
 [$expr| $x + $y |] -> (x, y)
 [$expr| ^n + ^m |] -> n + m

* Signature

Note that we only export the abstract syntax and the quasiquoter,
so the module can be imported unqualified.

> module ATP.IntroSyn
>   ( Expr(..)
>   , expr
>   ) 
> where

* Imports

> import Prelude hiding (id)
> import qualified ATP.Util.TH as TH'
> import qualified ATP.Util.Lex as Lex
> import qualified ATP.Util.Parse as P
> import ATP.Util.Parse (Parse, Parser, (<|>), (<?>))
> import qualified ATP.Util.Print as PP
> import ATP.Util.Print(Pretty, (<+>))
> import qualified Data.Char as Char
> import qualified Data.Generics as G
> import Data.Generics(Typeable, Data)
> import qualified Language.Haskell.TH as TH
> import qualified Language.Haskell.TH.Quote as Q
> import Language.Haskell.TH.Quote (QuasiQuoter(..))

* Syntax

> data Expr = Var String
>           | Const Integer
>           | Add Expr Expr
>           | Mul Expr Expr
>   deriving (Typeable, Data)

For example

Add (Mul (Const 2) (Var "x")) (Var "y")

* Parsing

> instance Parse Expr where
>   parser = parseExpr

> parseExpr :: Parser Expr
> parseExpr = P.buildExpressionParser table atomic <?> "expr" 

> table :: P.OperatorTable Char () Expr
> table = [ [op "*" Mul P.AssocRight] 
>         , [op "+" Add P.AssocRight]
>         ] 
>   where op s f assoc = P.Infix (do{ Lex.reservedOp s; return f }) assoc 

> antiExpr :: Parser Expr
> antiExpr = do Lex.symbol "$"
>               id <- Lex.identifier
>               return $ Var("$" ++ id)
>        <|> do Lex.symbol "^"
>               id <- Lex.identifier
>               return $ Var("^" ++ id)

> atomic :: Parser Expr
> atomic = do n <- Lex.integer
>             return $ Const n
>      <|> antiExpr
>      <|> do x <- Lex.identifier
>             return $ Var x
>      <|> Lex.parens parseExpr
>      <?> "atomic expr"

> parse :: String -> Expr
> parse = Lex.makeParser parseExpr

* Quotations

> quoteExprExp :: String -> TH.ExpQ
> quoteExprPat :: String -> TH.PatQ

The quasiquoter for Exprs.  It is the only export besides the syntax
for Exprs.

> expr :: QuasiQuoter
> expr = QuasiQuoter quoteExprExp quoteExprPat

> quoteExprExp s = Q.dataToExpQ (const Nothing `G.extQ` antiExprExp) (parse s)

Quote as an expression.

> antiExprExp :: Expr -> Maybe TH.ExpQ
> antiExprExp (Var v) = 
>   case v of 
>     '$':back -> Just $ TH'.varE back
>     '^':back -> Just $ TH'.conE "Const" [TH'.varE back]
>     _ -> Just $ TH'.varE v
> antiExprExp _ = Nothing

Quote as a pattern.

> quoteExprPat s = Q.dataToPatQ (const Nothing `G.extQ` antiExprPat) (parse s)

> antiExprPat :: Expr -> Maybe TH.PatQ
> antiExprPat (Var v) = 
>   case v of 
>     '$':back -> Just $ TH'.varP back
>     '^':back -> Just $ TH'.conP "Const" [TH'.varP back]
>     "_" -> Just $ TH.wildP
>     _ -> Just $ TH'.varP v
> antiExprPat _ = Nothing

* Printing

Print "+" and "*" as right associative by including
a precedence argument.

We use the Hughes pretty printing library for layout.

> instance Pretty Expr where
>   pPrint = pp 0

> instance Show Expr where
>   show = PP.render . PP.pPrint

> pp :: Int -> Expr -> PP.Doc
> pp _ (Var s) = PP.text s
> pp _ (Const n) = PP.integer n
> pp pr (Add e1 e2) = 
>      let doc1 = pp 3 e1 
>          doc2 = pp 2 e2 
>          doc3 = doc1 <+> PP.text "+" <+> doc2 in
>      if pr > 2 then PP.parens doc3 else doc3
> pp pr (Mul e1 e2) = 
>      let doc1 = pp 5 e1 
>          doc2 = pp 4 e2 
>          doc3 = doc1 <+> PP.text "*" <+> doc2 in
>      if pr > 4 then PP.parens doc3 else doc3
