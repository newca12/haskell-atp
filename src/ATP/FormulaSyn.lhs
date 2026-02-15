
* Signature

> module ATP.FormulaSyn 
>   ( Var, Vars
>   , Formula(..)
>   , Func, Term(..)
>   , Pred, Rel(R)
>   , Clause, Clauses
>   , Env
>   , (¬), (∧), (∨), (⇔), (⊃), (¥), (∃), (⊤), (⊥)
>   , (≤), (≥), (≺), (≻), (≡), (≠)
>     -- * Quotations
>   , term
>   , form
>     -- (%) needs to be exported for Rational templates to work.
>   , (Data.Ratio.%)
>   )
> where

* Imports

> import ATP.Util.Prelude hiding (pred)
> import qualified ATP.Util.TH as TH'
> import qualified ATP.Util.Lex as Lex
> import qualified ATP.Util.Parse as P
> import ATP.Util.Parse (Parse, parse, parser, Parser, (<|>), (<?>))            
> import qualified ATP.Util.Print as PP
> import ATP.Util.Print (Print)
> import qualified Data.Generics as G
> import Data.Generics (Data, Typeable)
> import qualified Data.Map as Map
> import Data.Map (Map)
> import qualified Data.List as List
> import qualified Language.Haskell.TH as TH
> import qualified Language.Haskell.TH.Quote as Q
> import Language.Haskell.TH.Quote (QuasiQuoter(..))
> import qualified Data.Ratio

* Syntax

○ Formulas

> type Var = String

> type Func = String

> data Term = Var String
>           | Num Rational
>           | Fn Func [Term]
>   deriving (Eq, Ord, Show, Data, Typeable)

> instance Num Term where
>   t1 + t2 = Fn "+" [t1, t2]
>   t1 - t2 = Fn "-" [t1, t2]
>   t1 * t2 = Fn "*" [t1, t2]
>   negate t = Fn "-" [t]
>   fromInteger = Num . fromInteger
>   abs _ = error "Unimplemented" 
>   signum _ = error "Unimplemented" 

○ Relations

> type Pred = String

> data Rel = R Pred [Term]
>   deriving (Eq, Ord, Show, Data, Typeable)

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
>   deriving(Eq, Ord, Show, Data, Typeable)

○ Useful abbreviations

> type Vars = [Var]
> type Clause = [Formula]
> type Clauses = [Clause]
> type Env = Map Var Term

> instance {-# OVERLAPPING #-} Print Env where
>   pPrint m = PP.set (map pr $ Map.toList m)
>     where pr (x, t) = PP.hsep [pPrint x, PP.text "↦", pPrint t]

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

> (≺) :: Term -> Term -> Formula
> s ≺ t = Atom $ R "<" [s, t]

> (≤) :: Term -> Term -> Formula
> s ≤ t = Atom $ R "≤" [s, t]

> (≻) :: Term -> Term -> Formula
> s ≻ t = Atom $ R ">" [s, t]

> (≥) :: Term -> Term -> Formula
> s ≥ t = Atom $ R "≥" [s, t]

> (≡) :: Term -> Term -> Formula
> s ≡ t = Atom $ R "=" [s, t]

> (≠) :: Term -> Term -> Formula
> s ≠ t = Not $ s ≡ t

* Parsing

> instance Parse Term where
>   parser = termp

> instance Parse Formula where
>   parser = formula

Encode a quotation in an atom.  This avoids needing a separate data
clause for antiquotes.

> isQuote :: String -> Bool
> isQuote ('$':_) = True
> isQuote ('^':_) = True
> isQuote "_" = True
> isQuote _ = False

> encodeRel :: String -> Rel
> encodeRel s = R s []

> decodeRel :: Rel -> Maybe String 
> decodeRel (R s _) = if isQuote s then Just s else Nothing

> var :: Parser Var
> var = do _ <- Lex.symbol "$"
>          x <- Lex.identifier
>          return $ ("$" ++ x)
>   <|> do _ <- Lex.symbol "^"
>          x <- Lex.identifier
>          return $ ("^" ++ x)
>   <|> Lex.identifier

** Terms

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
>          <|> do r <- parser
>                 return $ Num r
>          <|> P.try (do f <- Lex.identifier
>                        ts <- Lex.parens $ P.sepBy termp (Lex.symbol ",")
>                        return $ Fn f ts)
>          <|> (var >>= return . Var)
>          <?> "atomic term"

** Relations

> parseRel :: Parser Rel
> parseRel = 
>       P.try (do t1 <- P.parser
>                 op <- P.choice (map (P.try . Lex.symbol)
>                                ["=", ">=", "≥", ">", "≻", "<=", "≤", "<", "≺"])
>                 let op' = case op of
>                             ">=" -> "≥"
>                             "<=" -> "≤"
>                             "≻" -> ">"
>                             "≺" -> "<"
>                             _ -> op
>                 t2 <- P.parser
>                 return $ R op' [t1, t2])
>   <|> P.try (do p <- Lex.identifier
>                 ts <- Lex.parens $ P.sepBy termp (Lex.symbol ",")
>                 return $ R p ts)
>   <|> do p <- Lex.identifier
>          return $ R p []
>   <?> "relation"

** Formulas

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
>             <|> do Lex.reserved "forall" <|> Lex.reserved "∀"
>                    xs <- P.many1 var
>                    Lex.dot
>                    b <- formula 
>                    return $ foldr All b xs
>             <|> do Lex.reserved "exists" <|> Lex.reserved "∃"
>                    xs <- P.many1 var
>                    Lex.dot
>                    b <- formula 
>                    return $ foldr Ex b xs
>             <|> do v <- parseRel
>                    return $ Atom v
>             <|> do _ <- Lex.symbol "$"
>                    x <- Lex.identifier
>                    return $ Atom $ encodeRel ("$" ++ x)
>             <|> do _ <- Lex.symbol "^"
>                    x <- Lex.identifier
>                    return $ Atom $ encodeRel ("^" ++ x)
>             <|> do _ <- Lex.symbol "_"
>                    return $ Atom $ encodeRel "$_"
>             <|> Lex.parens formula
>             <?> "atomic formula"

* Quotations

** Terms

> term :: QuasiQuoter
> term = QuasiQuoter quoteExpT quotePatT undefined undefined

> quoteExpT :: String -> TH.ExpQ 
> quoteExpT = quoteTE . parse

> quotePatT :: String -> TH.PatQ 
> quotePatT = quoteTP . parse

| Expressions

> quoteTE :: Term -> TH.ExpQ
> quoteTE = Q.dataToExpQ (G.mkQ Nothing quoteTE')

> quoteTE' :: Term -> Maybe TH.ExpQ 
> quoteTE' t = case t of 
>   Var x -> if isQuote x then Just $ antiTE x else Nothing
>   Num k -> 
>     let n = Data.Ratio.numerator k
>         d = Data.Ratio.denominator k
>     in Just $ TH'.conE "Num" [TH.appE (TH'.appE "%" (TH.litE $ TH.IntegerL n)) (TH.litE $ TH.IntegerL d)]
>   _ -> Nothing

> antiTE :: String -> TH.ExpQ
> antiTE v = case v of
>   '$':back -> TH'.varE back
>   '^':back -> TH'.conE "Var" [TH'.varE back]
>   _ -> error ("Impossible: " ++ v) 

| Patterns 

> quoteTP :: Term -> TH.PatQ
> quoteTP = Q.dataToPatQ (G.mkQ Nothing quoteTP')

> quoteTP' :: Term -> Maybe TH.PatQ
> quoteTP' p = case p of 
>   Var x -> if isQuote x then Just $ antiTP x else Nothing
>   _ -> Nothing

> antiTP :: String -> TH.PatQ
> antiTP v = case v of
>   "_"  -> TH.wildP
>   "$_" -> TH.wildP
>   '$':x -> TH'.varP x
>   '^':x -> TH'.conP "Var" [TH'.varP x]
>   _ -> error ("Impossible: " ++ v)

** Formulas

> form :: QuasiQuoter
> form = QuasiQuoter quoteExpF quotePatF undefined undefined

> quoteExpF :: String -> TH.ExpQ 
> quoteExpF = quoteFE . parse

> quotePatF :: String -> TH.PatQ 
> quotePatF = quoteFP . parse

| Expressions

> quoteFE :: Formula -> TH.ExpQ
> quoteFE = Q.dataToExpQ (G.mkQ Nothing quoteFE')

> quoteFE' :: Formula -> Maybe TH.ExpQ 
> quoteFE' p = case p of 
>   Atom a@(R pred ts) -> case decodeRel a of 
>      Just q -> Just $ antiFE q
>      Nothing -> Just $ TH'.conE "Atom" [TH'.conE "R" [TH.stringE pred, TH.listE (map quoteTE ts)]] 
>   All x p' -> Just $ TH'.conE "All" [boundFE x, quoteFE p']
>   Ex x p' -> Just $ TH'.conE "Ex" [boundFE x, quoteFE p']
>   _ -> Nothing

> antiFE :: String -> TH.ExpQ
> antiFE v = case v of
>   '$':back -> TH'.varE back
>   '^':back -> TH'.conE "Atom" [TH'.varE back]
>   _ -> error ("Impossible: " ++ v) 

> boundFE :: Var -> TH.ExpQ
> boundFE ('$':x) = TH'.varE x 
> boundFE x = TH.stringE x

| Patterns 

> quoteFP :: Formula -> TH.PatQ
> quoteFP = Q.dataToPatQ (G.mkQ Nothing quoteFP')

> quoteFP' :: Formula -> Maybe TH.PatQ
> quoteFP' p = case p of 
>   Atom a@(R pred ts) -> 
>    case decodeRel a of 
>      Just q -> Just $ antiFP q
>      Nothing -> Just $ TH'.conP "Atom" [TH'.conP "R" [TH.litP $ TH.stringL pred, TH.listP (map quoteTP ts)]] 
>   All x p' -> Just $ TH'.conP "All" [boundFP x, quoteFP p']
>   Ex x p' -> Just $ TH'.conP "Ex" [boundFP x, quoteFP p']
>   _ -> Nothing

> antiFP :: String -> TH.PatQ
> antiFP v = case v of
>   "_"  -> TH.wildP
>   "$_"  -> TH.wildP
>   '$':x -> TH'.varP x
>   "^_"  -> TH'.conP "Atom" [TH.wildP]
>   '^':x -> TH'.conP "Atom" [TH'.varP x]
>   _ -> error ("Impossible: " ++ v)

> boundFP :: Var -> TH.PatQ
> boundFP ('$':x) = TH'.varP x
> boundFP x = TH.litP $ TH.stringL x

* Printing

Terms

> instance Print Term where
>   pPrint = ppTerm' 0

> ppTerm' :: Int -> Term -> PP.Doc
> ppTerm' prec t = case t of  
>   Var x -> PP.text x
>   Num r -> pPrint r
>   Fn "^" [t1, t2] -> ppInfixTm True prec 24 "^" t1 t2
>   Fn "/" [t1, t2] -> ppInfixTm True prec 22 "/" t1 t2
>   Fn "*" [t1, t2] -> ppInfixTm False prec 20 "*" t1 t2
>   Fn "-" [t1, t2] -> ppInfixTm True prec 18 "-" t1 t2
>   Fn "+" [t1, t2] -> ppInfixTm False prec 16 "+" t1 t2
>   Fn "::" [t1, t2] -> ppInfixTm False prec 14 "::" t1 t2
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

> isInfixRel :: Rel -> Bool
> isInfixRel (R p ts) = 
>   List.elem p ["=", "<", "≺", "<=", "≤", ">", "≻", ">=", "≥"] && length ts == 2 

> instance Print Rel where
>   pPrint (R p []) = PP.text p
>   pPrint r@(R p args) = 
>       if isInfixRel r
>       then ppInfixTm False 12 12 p' (args !! 0) (args !! 1)
>       else PP.text p <> ppArgs args
>     where p' = case p of 
>                  "<=" -> "≤"
>                  ">=" -> "≥"
>                  "≺" -> "<"
>                  "≻" -> ">"
>                  _ -> p

Formulas

> instance Print Formula where
>   pPrint = ppForm 0

Since all infix formulas associate to the right, we don't need
to complicate the printer with associativity.

> ppForm :: Int -> Formula -> PP.Doc
> ppForm pr f = case f of 
>   Bot -> PP.text "⊥"
>   Top -> PP.text "⊤"
>   Atom m -> PP.paren (pr > 12) $ pPrint m
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
> ppInfixFm pr sym p q = 
>   let lev :: Int = if sym == "∧" || sym == "∨" then 0 else 2 in 
>   PP.hang (ppForm (pr+1) p <+> PP.text sym)
>     lev (ppForm pr q)

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
