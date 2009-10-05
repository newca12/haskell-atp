
* Signature

> module ATP.FormulaSyn 
>   ( Var, Vars
>   , Formula(..)
>   , Func, Term(..)
>   , Pred, Rel(R)
>   , Clause, Clauses
>   , Env
>   , (¬), (∧), (∨), (⇔), (⊃), (¥), (∃), (⊤), (⊥)
>     -- * Quotations
>   , term
>   , form
>   )
> where

* Imports

> import Prelude 
> import qualified Data.List as List
> import qualified Data.Maybe as Maybe
> import Data.Map (Map)
> import qualified Language.Haskell.TH as TH
> import Language.Haskell.TH(ExpQ, PatQ)
> import qualified Language.Haskell.TH.Quote as Q
> import Language.Haskell.TH.Quote (QuasiQuoter(..))
> import qualified Data.Generics as G
> import Data.Generics (Data, Typeable)

> import qualified ATP.Util.Lex as Lex
> import qualified ATP.Util.Parse as P
> import ATP.Util.Parse (Parse, parse)
> import qualified ATP.Util.TH as TH'
> import ATP.Util.Parse (Parser, (<|>), (<?>))
> import qualified ATP.Util.Print as PP
> import ATP.Util.Print (Pretty(pPrint), (<+>), (<>))

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
>   fromInteger n = Fn (show n) []
>   abs _ = error "Unimplemented" 
>   signum _ = error "Unimplemented" 

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
> type Env = Map Var Term

* Infix ops

> infixr 8 ∧
> infixr 7 ∨
> infixr 6 ⊃
> infixr 5 ⇔

> (⊤) :: Formula
> (⊤) = Top

> (⊥) :: Formula
> (⊥) = Bot

> (¬) :: Formula -> Formula 
> (¬) = Not

> (∧) :: Formula -> Formula -> Formula 
> (∧) = And

> (∨) :: Formula -> Formula -> Formula 
> (∨) = Or

> (⊃) :: Formula -> Formula -> Formula 
> (⊃) = Imp

> (⇔) :: Formula -> Formula -> Formula 
> (⇔) = Iff

> (¥) :: Var -> Formula -> Formula 
> (¥) = All

> (∃) :: Var -> Formula -> Formula 
> (∃) = Ex

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

> var :: Parser Var
> var = do Lex.symbol "$"
>          x <- Lex.identifier
>          return $ ("$" ++ x)
>   <|> Lex.identifier

○ Terms

> termp :: Parser Term
> termp = P.buildExpressionParser termTable atomicTerm <?> "term" 

> termTable :: P.OperatorTable Char () Term
> termTable = [ [op "^"  (fn "^")  P.AssocLeft] 
>             , [op "/"  (fn "/")  P.AssocLeft]
>             , [op "*"  (fn "*")  P.AssocRight]
>             , [op "-"  (fn "-")  P.AssocLeft]
>             , [op "+"  (fn "+")  P.AssocRight]
>             , [op "::" (fn "::") P.AssocRight]
>             ] 
>   where op s f assoc = P.Infix (do { Lex.reservedOp s; return f }) assoc 
>         fn f t1 t2 = Fn f [t1, t2]

> atomicTerm :: Parser Term
> atomicTerm = Lex.parens termp
>          <|> do Lex.reserved "nil" 
>                 return $ Fn "nil" []
>          <|> do Lex.reservedOp "-" 
>                 t <- atomicTerm
>                 return $ Fn "-" [t]
>          <|> do n <- Lex.integer
>                 return $ Fn (show n) []
>          <|> P.try (do f <- Lex.identifier
>                        ts <- Lex.parens $ P.sepBy termp (Lex.symbol ",")
>                        return $ Fn f ts)
>          <|> do x <- Lex.identifier
>                 return $ Var x
>          <?> "atomic term"

○ Relations

> parseRel :: Parser Rel
> parseRel = 
>       P.try (do t1 <- termp
>                 op <- P.choice (map (P.try . Lex.symbol)
>                                ["=", ">=", "≥", ">", "<=", "≤", "<"])
>                 t2 <- termp
>                 return $ R op [t1, t2])
>   <|> P.try (do p <- Lex.identifier
>                 ts <- Lex.parens $ P.sepBy termp (Lex.symbol ",")
>                 return $ R p ts)
>   <|> do p <- Lex.identifier
>          return $ R p []
>   <?> "relation"

○ Formulas

> formula :: Parser Formula
> formula = P.buildExpressionParser formulaTable atomicFormula <?> "formula" 

> formulaTable :: P.OperatorTable Char () Formula
> formulaTable = [ [ op "∧" And P.AssocRight
>                  , op "/\\" And P.AssocRight ] 
>                , [ op "\\/" Or  P.AssocRight
>                  , op "∨" Or  P.AssocRight ]
>                , [ op "==>" Imp P.AssocRight
>                  , op "⊃" Imp P.AssocRight ]
>                , [ op "<=>" Iff P.AssocRight
>                  , op "⇔" Iff P.AssocRight ]
>                ] 
>   where op s f assoc = P.Infix (do { Lex.reservedOp s; return f }) assoc 

> atomicFormula :: Parser Formula
> atomicFormula = do Lex.reserved "true" <|> Lex.reserved "⊤"
>                    return Top
>             <|> do Lex.reserved "false" <|> Lex.reserved "⊥"
>                    return Bot
>             <|> do (Lex.reserved "~" <|> Lex.reserved "¬")
>                    f <- atomicFormula
>                    return $ Not $ f
>             <|> do Lex.symbol "$"
>                    x <- Lex.identifier
>                    return $ Atom $ encode ("$" ++ x)
>             <|> do Lex.symbol "^"
>                    x <- Lex.identifier
>                    return $ Atom $ encode ("^" ++ x)
>             <|> do Lex.symbol "_"
>                    return $ Atom $ encode "$_"
>             <|> do Lex.reserved "forall" <|> Lex.reserved "∀"
>                    xs <- P.many1 var
>                    Lex.symbol "."
>                    b <- formula 
>                    return $ foldr All b xs
>             <|> do Lex.reserved "exists" <|> Lex.reserved "∃"
>                    xs <- P.many1 var
>                    Lex.symbol "."
>                    b <- formula 
>                    return $ foldr Ex b xs
>             <|> do v <- parseRel
>                    return $ Atom v
>             <|> Lex.parens formula
>             <?> "atomic formula"

Package it up.

> instance Parse Formula where
>   parser = formula

> instance Parse Term where
>   parser = termp

* Quotations

** Terms

> term :: QuasiQuoter
> term = QuasiQuoter quoteExpT quotePatT

> parseTerm :: String -> Term
> parseTerm = Lex.makeParser termp

> quoteExpT :: String -> TH.ExpQ 
> quoteExpT = quoteT . parseTerm

> quotePatT :: String -> TH.PatQ 
> quotePatT = quoteT' . parseTerm

> quoteT :: Data a => a -> TH.ExpQ
> quoteT = Q.dataToExpQ (const Nothing)

> quoteT' :: Data a => a -> TH.PatQ
> quoteT' = Q.dataToPatQ (const Nothing)

** Formulas

> form :: QuasiQuoter
> form = QuasiQuoter quoteExpF quotePatF

> quoteExpF :: String -> TH.ExpQ 
> quoteExpF = quoteE . parse

> quotePatF :: String -> TH.PatQ 
> quotePatF = quoteP . parse

*** Expressions

> quoteE :: Formula -> TH.ExpQ
> quoteE = Q.dataToExpQ (G.mkQ Nothing quoteE')

> quoteE' :: Formula -> Maybe TH.ExpQ 
> quoteE' p = case p of 
>   Atom a ->
>    case decode a of 
>      Nothing -> Nothing
>      Just q  -> Just $ antiE q
>   All x p' -> Just $ TH'.conE "All" [boundE x, quoteE p']
>   Ex x p' -> Just $ TH'.conE "Ex" [boundE x, quoteE p']
>   _ -> Nothing

> antiE :: String -> TH.ExpQ
> antiE v = case v of
>   '$':back -> TH'.varE back
>   '^':back -> TH'.conE "Atom" [TH'.varE back]
>   _ -> error ("Impossible: " ++ v) 

> boundE :: Var -> TH.ExpQ
> boundE ('$':x) = TH'.varE x 
> boundE x = TH.stringE x

*** Patterns 

> quoteP :: Formula -> TH.PatQ
> quoteP = Q.dataToPatQ (G.mkQ Nothing quoteP')

> quoteP' :: Formula -> Maybe TH.PatQ
> quoteP' p = case p of 
>   Atom a -> 
>    case decode a of 
>      Nothing -> Nothing
>      Just q -> Just $ antiP q
>   All x p' -> Just $ TH'.conP "All" [boundP x, quoteP p']
>   Ex x p' -> Just $ TH'.conP "Ex" [boundP x, quoteP p']
>   _ -> Nothing

> antiP :: String -> TH.PatQ
> antiP v = case v of
>   "$_"  -> TH.wildP
>   '$':x -> TH'.varP x
>   "^_"  -> TH'.conP "Atom" [TH.wildP]
>   '^':x -> TH'.conP "Atom" [TH'.varP x]
>   _ -> error ("Impossible: " ++ v)

> boundP :: Var -> TH.PatQ
> boundP ('$':x) = TH'.varP x
> boundP x = TH.litP $ TH.stringL x

* Printing

Terms

> instance Show Term where
>   show = PP.prettyShow

> instance Pretty Term where
>   pPrint = ppTerm' 0

> ppTerm' :: Int -> Term -> PP.Doc
> ppTerm' prec t = case t of  
>   Var x -> PP.text x
>   Fn "^" [t1, t2] -> ppInfixTm True prec 24 "^" t1 t2
>   Fn "/" [t1, t2] -> ppInfixTm True prec 22 "/" t1 t2
>   Fn "*" [t1, t2] -> ppInfixTm True prec 20 "*" t1 t2
>   Fn "-" [t1, t2] -> ppInfixTm True prec 18 "-" t1 t2
>   Fn "+" [t1, t2] -> ppInfixTm True prec 16 "+" t1 t2
>   Fn "::" [t1, t2] -> ppInfixTm True prec 14 "::" t1 t2
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

Relations

> instance Show Rel where
>     show = PP.prettyShow

> instance Pretty Rel where
>   pPrint (R p []) = PP.text p
>   pPrint (R p args) = 
>     if List.elem p ["=", "<", "<=", ">", ">="] && length args == 2 
>     then ppInfixTm False 12 12 p (args !! 0) (args !! 1)
>     else PP.text p <> ppArgs args

Formulas

> instance Show Formula where
>   show = PP.prettyShow

> instance Pretty Formula where
>   pPrint = ppForm 0

> ppForm :: Int -> Formula -> PP.Doc
> ppForm pr f = case f of 
>   Bot -> PP.text "⊥"
>   Top -> PP.text "⊤"
>   Atom m -> pPrint m
>   Not p -> paren (pr > 10) (ppPrefixFm 10) "¬" p
>   And p q -> paren (pr > 8) (ppInfixFm 8 "∧") p q
>   Or p q -> paren (pr > 6) (ppInfixFm 6 "∨") p q
>   Imp p q -> paren (pr > 4) (ppInfixFm 4 "⊃") p q
>   Iff p q -> paren (pr > 2) (ppInfixFm 2 "⇔") p q
>   All _ _ -> paren (pr > 0) ppQuant "∀" (stripQuant f)
>   Ex _ _ -> paren (pr > 0) ppQuant "∃" (stripQuant f)

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
> stripQuant f = case f of 
>   All x (yp@(All _ _)) -> (x:xs, q)
>     where (xs,q) = stripQuant yp 
>   Ex x (yp@(Ex _ _)) -> (x:xs, q)
>     where (xs,q) = stripQuant yp 
>   All x p -> ([x], p)
>   Ex x p -> ([x], p)
>   _ -> ([], f)
