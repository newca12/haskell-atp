
> module Lam where

> import Prelude hiding (exp)
> import qualified Data.List as List
> import Data.List ( (\\), union )
> import qualified Text.ParserCombinators.Parsec as P
> import Text.ParserCombinators.Parsec ( GenParser, Parser, (<|>) )

> data Var = V String
>   deriving Eq

> data Exp = Var Var
>          | Lam Var Exp
>          | App Exp Exp

> instance Show Exp where
>   show (Var (V x)) = x
>   show (Lam (V x) e) = "\\" ++ x ++ ". " ++ show e
>   show (App e1 e2) = paren e1 (show e1) ++ " " ++ paren e2 (show e2)
>     where paren (Var _) s = s
>           paren _       s = "(" ++ s ++ ")"

> allBinders :: [Var]
> allBinders = [V [x] | x <- ['a'..'z']] ++
>              [V (x:show i) | x <- ['a'..'z'], i <- [1 :: Integer ..]]

> free :: Exp -> [Var]
> free (Var x) = [x]
> free (Lam x e) = free e \\ [x]
> free (App e1 e2) = free e1 ++ free e2

> occurs :: Exp -> [Var]
> occurs (Var x) = [x]
> occurs (Lam x e) = 
>   if x `elem` xs then xs else x : xs
>     where xs = occurs e
> occurs (App e1 e2) = occurs e1 `union` occurs e2

e[x |-> e']

> subst :: Exp -> Var -> Exp -> Exp
> subst e x e' = subst' (allBinders \\ occurs e `union` occurs e') e x e'
>   where 
>     subst' :: [Var] -> Exp -> Var -> Exp -> Exp
>     subst' fresh e x e' = 
>       case e of 
>         Var x' | x == x'   -> e'
>                | otherwise -> e
>         Lam x' b | x == x'           -> e
>                  | x' `elem` free e' -> Lam y (subst' fresh' b' x e')
>                  | otherwise         -> Lam x' (subst' fresh b x e') 
>           where y:fresh' = fresh
>                 b' = subst' [] b x' (Var y)
>         App e1 e2 -> App e1' e2'
>           where e1' = subst' fresh e1 x e'
>                 e2' = subst' fresh e2 x e'

> eval :: Exp -> Exp
> eval e = 
>   case e of 
>     Var _ -> e
>     Lam _ _ -> e
>     App e1 e2 -> 
>       case eval e1 of
>         Lam x e1' -> eval (subst e1' x e2)
>         e1' -> App e1' (eval e2)

> small, large, idchar :: Parser Char
> small = P.lower <|> P.char '_'
> large = P.upper
> idchar = small <|> large <|> P.char '\''

> parens :: Parser a -> Parser a
> parens = P.between (symbol "(") (symbol ")")

> lexeme :: Parser a -> Parser a
> lexeme p = do x <- p
>               whiteSpace
>               return x

> symbol :: String -> Parser String
> symbol = lexeme . P.string

> whiteSpace, ident :: Parser String
> whiteSpace = P.many $ P.oneOf " \t"

> ident = lexeme $ 
>   do c <- small
>      cs <- P.many idchar
>      return $ c:cs

> var :: Parser Var
> var = do x <- ident
>          return $ V x

> aexp, exp :: Parser Exp

f e_1 .. e_n

> exp = do es <- P.many aexp 
>          return $ foldl1 App es

> aexp = P.try $ do v <- var
>                   return $ Var v
>            <|> do symbol "\\"
>                   v <- var
>                   symbol "."
>                   e <- exp
>                   return $ Lam v e
>            <|> parens exp

> parse :: Monad m => String -> m Exp 
> parse s = 
>   case P.runParser p () "" s of
>     Left err -> fail $ show err
>     Right e  -> return e
>  where p = do e <- exp
>               P.eof
>               return e

> parseEval :: Monad m => String -> m Exp
> parseEval s = do
>   e <- parse s
>   return $ eval e
