
* Signature

> module ATP.Equal
>   ( isEq
>   , mkEq
>   , destEq
>   , lhs
>   , rhs
>   , equalitize
>   )
> where

* Imports

> import ATP.Util.Prelude 
> import qualified ATP.Fol as Fol
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\))

* Equality

> isEq :: Formula -> Bool
> isEq (Atom(R "=" _)) = True
> isEq _ = False

> mkEq :: Term -> Term -> Formula
> mkEq s t = Atom(R "=" [s,t])

> destEq :: Formula -> (Term, Term)
> destEq (Atom(R "=" [s,t])) = (s, t)
> destEq _ = error "not an equality"

> lhs :: Formula -> Term
> lhs = fst . destEq 

> rhs :: Formula -> Term
> rhs = snd . destEq 

> predicates :: Formula -> [(Pred, Int)]
> predicates = F.atomUnion (\(R p args) -> [(p, length args)])

> functionCongruence :: (Pred, Int) -> [Formula]
> functionCongruence (f,n) =
>   if n == 0 then [] else
>   let argnamesX = map (("x" ++) . show) [1..n]
>       argnamesY = map (("y" ++) . show) [1..n]
>       argsX = map Var argnamesX
>       argsY = map Var argnamesY
>       ant = F.listConj (zipWith mkEq argsX argsY)
>       con = mkEq (Fn f argsX) (Fn f argsY) in
>  [foldr All (ant ⊃ con) (argnamesX ++ argnamesY)]

> predicateCongruence :: (Pred, Int) -> [Formula]
> predicateCongruence (p,n) =
>   if n == 0 then [] else
>   let argnamesX = map (("x" ++) . show) [1..n]
>       argnamesY = map (("y" ++) . show) [1..n]
>       argsX = map Var argnamesX
>       argsY = map Var argnamesY
>       ant = F.listConj (zipWith mkEq argsX argsY)
>       con = Atom(R p argsX) ⊃ Atom(R p argsY) in
>  [foldr All (ant ⊃ con) (argnamesX ++ argnamesY)]

> equivalenceAxioms :: [Formula]
> equivalenceAxioms = 
>   [ [form| ∀ x. x = x |]
>   , [form| ∀ x y z. x = y ∧ x = z ⊃ y = z |]
>   ]

> equalitize :: Formula -> Formula
> equalitize fm = 
>   let allpreds = predicates fm in
>   if not (elem ("=",2) allpreds) then fm else
>   let preds = allpreds \\ [("=",2)]
>       funcs = Fol.functions fm
>       axioms = foldr (Set.union . functionCongruence) 
>                  (foldr (Set.union . predicateCongruence) equivalenceAxioms preds)
>                    funcs in
>   F.listConj axioms ⊃ fm

