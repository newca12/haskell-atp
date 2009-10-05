
* Signature

> module FormulaSyn 
>   ( Var, Vars
>   , Formula(..)
>   , Func, Term(..)
>   , Pred, Rel(R)
>   , Clause, Clauses
>     -- Quotations
>   , term, fol
>   )
> where

* Imports

> import Prelude 
> import qualified Data.List as List
> import qualified Data.Maybe as Maybe

Parsing 

> import qualified Lex
> import qualified Text.ParserCombinators.Parsec as P
> import Text.ParserCombinators.Parsec (Parser, (<|>), (<?>))
> import qualified Text.ParserCombinators.Parsec.Expr as E
 
Quotations

> import qualified Language.Haskell.TH as TH
> import Language.Haskell.TH(ExpQ, PatQ)
> import qualified Language.Haskell.TH.Quote as Q
> import Language.Haskell.TH.Quote (QuasiQuoter(..))
> import qualified Data.Generics as G
> import Data.Generics (Data, Typeable)

Printing 

> import qualified Text.PrettyPrint.HughesPJClass as PP
> import Text.PrettyPrint.HughesPJClass(Pretty(pPrint), (<+>), (<>))

* Syntax

○ Formulas

> type Var = String

> type Func = String

> data Term = Var String
>           | Fn Func [Term]
>   deriving (Eq, Ord, Data, Typeable)

> instance Num Term where
>   t1 + t2 = Fn "+" [t1, t2]
>   t1 - t2 = Fn "-" [t1, t2]
>   t1 * t2 = Fn "*" [t1, t2]
>   negate t = Fn "-" [t]
>   abs _ = error "Unimplemented" 
>   signum _ = error "Unimplemented" 
>   fromInteger n = Fn (show n) []

> instance Fractional Term where
>   fromRational r = Fn (show r) []

○ Relations

> type Pred = String

> data Rel = R Pred [Term]
>   deriving (Eq, Ord, Data, Typeable)

○ Formulas

> data Formula = Atom Rel
>              | Top
>              | Bot
>              | Not Formula
>              | And Formula Formula 
>              | Or Formula Formula 
>              | Imp Formula Formula
>              | Iff Formula Formula
>              | All Var Formula
>              | Ex Var Formula
>   deriving(Eq, Ord, Data, Typeable)

○ Useful abbreviations

> type Vars = [Var]
> type Clause = [Formula]
> type Clauses = [Clause]

* Parsing

Encode a quotation in an atom.  This avoids needing a separate data
clause for antiquotes.

> isQuote :: String -> Bool
> isQuote ('$':_) = True
> isQuote ('^':_) = True
> isQuote _ = False

> encode :: String -> Rel
> encode s = R s []

> decode :: Rel -> Maybe String 
> decode (R s _) = if isQuote s then Just s else Nothing

○ Formulas

> formula :: Parser Formula
> formula = E.buildExpressionParser formulaTable atomicFormula <?> "formula" 

> formulaTable :: E.OperatorTable Char () Formula
> formulaTable = [ [op "/\\" And E.AssocRight] 
>                , [op "\\/" Or  E.AssocRight]
>                , [op "==>" Imp E.AssocRight]
>                , [op "<=>" Iff E.AssocRight]
>                ] 
>   where op s f assoc = E.Infix (do { Lex.reservedOp s; return f }) assoc 

> ident :: Parser String
> ident = Lex.identifier <|> Lex.symbol "_"

> var :: Parser Var
> var = do Lex.symbol "$"
>          x <- ident
>          return $ ("$" ++ x)
>   <|> ident

> atomicFormula :: Parser Formula
> atomicFormula = do Lex.reserved "true"
>                    return Top
>             <|> do Lex.reserved "false"
>                    return Bot
>             <|> do Lex.symbol "~"
>                    f <- atomicFormula
>                    return $ Not $ f
>             <|> do Lex.symbol "$"
>                    x <- ident
>                    return $ Atom $ encode ("$" ++ x)
>             <|> do Lex.symbol "^"
>                    x <- ident
>                    return $ Atom $ encode ("^" ++ x)
>             <|> do Lex.symbol "_"
>                    return $ Atom $ encode "$_"
>             <|> do Lex.reserved "forall"
>                    xs <- P.many1 var
>                    Lex.symbol "."
>                    b <- formula 
>                    return $ foldr All b xs
>             <|> do Lex.reserved "exists"
>                    xs <- P.many1 var
>                    Lex.symbol "."
>                    b <- formula 
>                    return $ foldr Ex b xs
>             <|> Lex.parens formula
>             <|> do v <- parseRel
>                    return $ Atom v
>             <?> "atomic formula"

○ Terms

> termp :: Parser Term
> termp = E.buildExpressionParser termTable atomicTerm <?> "term" 

> termTable :: E.OperatorTable Char () Term
> termTable = [ [op "^"  (fn "^")  E.AssocLeft] 
>             , [op "/"  (fn "/")  E.AssocLeft]
>             , [op "*"  (fn "*")  E.AssocRight]
>             , [op "-"  (fn "-")  E.AssocLeft]
>             , [op "+"  (fn "+")  E.AssocRight]
>             , [op "::" (fn "::") E.AssocRight]
>             ] 
>   where op s f assoc = E.Infix (do { Lex.reservedOp s; return f }) assoc 
>         fn op t1 t2 = Fn op [t1, t2]

> atomicTerm :: Parser Term
> atomicTerm = Lex.parens termp
>          <|> do n <- Lex.natural
>                 return $ Fn (show n) []
>          <|> do Lex.reserved "nil" 
>                 return $ Fn "nil" []
>          <|> do Lex.symbol "-" 
>                 t <- atomicTerm
>                 return $ Fn "-" [t]
>          <|> P.try (do f <- ident
>                        ts <- Lex.parens $ P.sepBy termp (Lex.symbol ",")
>                        return $ Fn f ts)
>          <|> do x <- ident
>                 return $ Var x
>          <?> "atomic term"

○ Relations

> parseRel :: Parser Rel
> parseRel = 
>       P.try (do t1 <- termp
>                 op <- P.choice (map (P.try . Lex.symbol) ["=", ">=", ">", "<=", "<"])
>                 t2 <- termp
>                 return $ R op [t1, t2])
>   <|> P.try (do p <- ident
>                 ts <- Lex.parens $ P.sepBy termp (Lex.symbol ",")
>                 return $ R p ts)
>   <|> do p <- ident
>          return $ R p []
>   <?> "relation"

Package it up.

> makeParser :: Monad m => Parser a -> String -> m a
> makeParser p input = 
>   case P.runParser p' () "" input of
>     Left err -> fail $ show err
>     Right e -> return e
>  where p' = do Lex.whiteSpace
>                x <- p
>                P.eof 
>                return x

> parseFormula :: Monad m => String -> m Formula
> parseFormula = makeParser formula

> parseTerm :: Monad m => String -> m Term
> parseTerm = makeParser termp

* Quotations

%%% Top level quasiquoters

Formula 

> fol :: QuasiQuoter
> fol = QuasiQuoter quoteExpF quotePatF

> quoteExpF :: String -> TH.ExpQ 
> quoteExpF = quoteE . Maybe.fromJust . parseFormula 

> quotePatF :: String -> TH.PatQ 
> quotePatF = quoteP . Maybe.fromJust . parseFormula

Term 

> term :: QuasiQuoter
> term = QuasiQuoter quoteExpT quotePatT

> quoteExpT :: String -> TH.ExpQ 
> quoteExpT = quoteT . Maybe.fromJust . parseTerm

> quotePatT :: String -> TH.PatQ 
> quotePatT = quoteT' . Maybe.fromJust . parseTerm

> quoteT :: Data a => a -> TH.ExpQ
> quoteT = Q.dataToExpQ (const Nothing)

> quoteT' :: Data a => a -> TH.PatQ
> quoteT' = Q.dataToPatQ (const Nothing)

%%% Basic quotations

Expressions

> quoteE :: Formula -> TH.ExpQ
> quoteE = Q.dataToExpQ (G.mkQ Nothing quoteE')

> quoteE' :: Formula -> Maybe TH.ExpQ 
> quoteE' p = case p of 
>   Atom a ->
>    case decode a of 
>      Nothing -> Nothing
>      Just q  -> Just $ antiE q
>   All x p -> Just $ foldl1 TH.appE [TH.conE (TH.mkName "All"), boundE x, quoteE p]
>   Ex x p -> Just $ foldl1 TH.appE [TH.conE (TH.mkName "Ex"), boundE x, quoteE p]
>   _ -> Nothing

> antiE :: String -> TH.ExpQ
> antiE v = case v of
>   '$':back -> TH.varE $ TH.mkName back
>   '^':back -> TH.appE (TH.conE $ TH.mkName "Atom") (TH.varE $ TH.mkName back)
>   _ -> error ("Impossible: " ++ v) 

> boundE :: Var -> TH.ExpQ
> boundE ('$':x) = TH.varE $ TH.mkName x 
> boundE x = TH.stringE x

Patterns 

> quoteP :: Formula -> TH.PatQ
> quoteP = Q.dataToPatQ (G.mkQ Nothing quoteP')

> quoteP' :: Formula -> Maybe TH.PatQ
> quoteP' p = case p of 
>   Atom a -> 
>    case decode a of 
>      Nothing -> Nothing
>      Just q -> Just $ antiP q
>   All x p -> Just $ TH.conP (TH.mkName "All") [boundP x, quoteP p]
>   Ex x p -> Just $ TH.conP (TH.mkName "Ex") [boundP x, quoteP p]
>   _ -> Nothing

> antiP :: String -> TH.PatQ
> antiP v = case v of
>   "$_"  -> TH.wildP
>   '$':x -> TH.varP $ TH.mkName x
>   "^_"  -> TH.conP (TH.mkName "Atom") [TH.wildP]
>   '^':x -> TH.conP (TH.mkName "Atom") [TH.varP $ TH.mkName x]
>   _ -> error ("Impossible: " ++ v)

> boundP :: Var -> TH.PatQ
> boundP ('$':x) = TH.varP $ TH.mkName x
> boundP x = TH.litP $ TH.stringL x

* Printing

Formulas

> instance Show Formula where
>   show = PP.prettyShow

> instance Pretty Formula where
>   pPrint = ppForm 0

> ppForm :: Int -> Formula -> PP.Doc
> ppForm pr f = case f of 
>   Bot -> PP.text "false"
>   Top -> PP.text "true"
>   Atom m -> pPrint m
>   Not p -> paren (pr > 10) (ppPrefixFm 10) "~" p
>   And p q -> paren (pr > 8) (ppInfixFm 8 "/\\") p q
>   Or p q -> paren (pr > 6) (ppInfixFm 6 "\\/") p q
>   Imp p q -> paren (pr > 4) (ppInfixFm 4 "==>") p q
>   Iff p q -> paren (pr > 2) (ppInfixFm 2 "<=>") p q
>   All _ _ -> paren (pr > 0) ppQuant "forall" (stripQuant f)
>   Ex _ _ -> paren (pr > 0) ppQuant "exists" (stripQuant f)

> ppPrefixFm :: Int -> String -> Formula -> PP.Doc
> ppPrefixFm pr sym p = PP.text sym <> ppForm pr p

> ppInfixFm :: Int -> String -> Formula -> Formula -> PP.Doc
> ppInfixFm pr sym p q = PP.sep[PP.hsep[ppForm (pr+1) p, PP.text sym], 
>                               ppForm pr q] 

> ppQuant :: String -> (Vars, Formula) -> PP.Doc
> ppQuant name (bvs, bod) = 
>   PP.hang 
>     (PP.text name <+> PP.sep (map PP.text bvs) <> PP.text ".") 
>       2 (ppForm 0 bod)

> paren :: Bool -> (a -> b -> PP.Doc) -> a -> b -> PP.Doc
> paren p f x y = 
>   if p then PP.parens d else d
>     where d = f x y 

> stripQuant :: Formula -> (Vars, Formula)
> stripQuant fm = case fm of 
>   All x (yp@(All _ _)) -> (x:xs, q)
>     where (xs,q) = stripQuant yp 
>   Ex x (yp@(Ex _ _)) -> (x:xs, q)
>     where (xs,q) = stripQuant yp 
>   All x p -> ([x], p)
>   Ex x p -> ([x], p)
>   _ -> ([], fm)

Terms

> instance Show Term where
>   show = PP.prettyShow

> instance Pretty Term where
>   pPrint = ppTerm' 0

> ppTerm' :: Int -> Term -> PP.Doc
> ppTerm' prec tm = case tm of  
>   Var x -> PP.text x
>   Fn "^" [tm1, tm2] -> ppInfixTm True prec 24 "^" tm1 tm2
>   Fn "/" [tm1, tm2] -> ppInfixTm True prec 22 "/" tm1 tm2
>   Fn "*" [tm1, tm2] -> ppInfixTm True prec 20 "*" tm1 tm2
>   Fn "-" [tm1, tm2] -> ppInfixTm True prec 18 "-" tm1 tm2
>   Fn "+" [tm1, tm2] -> ppInfixTm True prec 16 "+" tm1 tm2
>   Fn "::" [tm1, tm2] -> ppInfixTm True prec 14 "::" tm1 tm2
>   Fn f [] -> PP.text f
>   Fn f xs -> PP.text f <> ppArgs xs

> ppArgs :: [Term] -> PP.Doc
> ppArgs xs =
>   PP.parens (PP.sep (PP.punctuate (PP.text ",") (map (ppTerm' 0) xs)))

> ppInfixTm :: Bool -> Int -> Int -> String -> Term -> Term -> PP.Doc
> ppInfixTm isleft oldprec newprec sym p q = 
>   let pprec = if isleft then newprec else newprec + 1
>       qprec = if isleft then newprec + 1 else newprec
>       doc1 = ppTerm' pprec p
>       doc2 = ppTerm' qprec q 
>       doc = PP.sep[doc1, PP.text sym, doc2] in
>   if oldprec > newprec then PP.parens doc else doc

Fol

> instance Show Rel where
>     show = PP.prettyShow

> instance Pretty Rel where
>   pPrint (R p []) = PP.text p
>   pPrint (R p args) = 
>     if List.elem p ["=", "<", "<=", ">", ">="] && length args == 2 
>     then ppInfixTm False 12 12 p (args !! 0) (args !! 1)
>     else PP.text p <> ppArgs args
