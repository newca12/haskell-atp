
> module Equal ( isEq
>              , mkEq
>              , destEq
>              , lhs
>              , rhs
>              , equalitize
>              ) where
                        
> import Prelude 
> import qualified ListSet
> import ListSet((\\))
> import Formulas(Formula(..), (==>), Sym)
> import qualified Formulas as F
> import qualified Fol
> import Fol(Fol(..),Term(..))
> import qualified Parse

> isEq :: Formula Fol -> Bool
> isEq (Atom(R "=" _)) = True
> isEq _ = False

> mkEq :: Term -> Term -> Formula Fol
> mkEq s t = Atom(R "=" [s,t])

> destEq :: Formula Fol -> (Term, Term)
> destEq (Atom(R "=" [s,t])) = (s, t)
> destEq _ = error "not an equality"

> lhs :: Formula Fol -> Term
> lhs = fst . destEq 
>             

> rhs :: Formula Fol -> Term
> rhs = snd . destEq 

> predicates :: Formula Fol -> [(Sym, Int)]
> predicates = F.atomUnion (\(R p args) -> [(p, length args)])

> functionCongruence :: (Sym, Int) -> [Formula Fol]
> functionCongruence (f,n) =
>   if n == 0 then [] else
>   let argnamesX = map (("x" ++) . show) [1..n]
>       argnamesY = map (("y" ++) . show) [1..n]
>       argsX = map Var argnamesX
>       argsY = map Var argnamesY
>       ant = F.listConj (zipWith mkEq argsX argsY)
>       con = mkEq (Fn f argsX) (Fn f argsY) in
>  [foldr Forall (ant ==> con) (argnamesX ++ argnamesY)]

> predicateCongruence :: (Sym, Int) -> [Formula Fol]
> predicateCongruence (p,n) =
>   if n == 0 then [] else
>   let argnamesX = map (("x" ++) . show) [1..n]
>       argnamesY = map (("y" ++) . show) [1..n]
>       argsX = map Var argnamesX
>       argsY = map Var argnamesY
>       ant = F.listConj (zipWith mkEq argsX argsY)
>       con = Atom(R p argsX) ==> Atom(R p argsY) in
>  [foldr Forall (ant ==> con) (argnamesX ++ argnamesY)]

> equivalenceAxioms :: [Formula Fol]
> equivalenceAxioms = 
>   map Parse.parse ["forall x. x = x", "forall x y z. x = y /\\ x = z ==> y = z"]

> equalitize :: Formula Fol -> Formula Fol
> equalitize fm = 
>   let allpreds = predicates fm in
>   if not (elem ("=",2) allpreds) then fm else
>   let preds = allpreds \\ [("=",2)]
>       funcs = Fol.functions fm
>       axioms = foldr (ListSet.union . functionCongruence) 
>                  (foldr (ListSet.union . predicateCongruence) equivalenceAxioms preds)
>                    funcs in
>   F.listConj axioms ==> fm

