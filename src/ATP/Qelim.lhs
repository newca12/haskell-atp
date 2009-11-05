
* Signature

> module ATP.Qelim
>   ( cnnf
>   , lift
>     -- * Hidden
>   , qelim
>   )
> where

* Imports

> import Prelude 
> import qualified ATP.Decidable as Decidable
> import qualified ATP.Fol as Fol
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Skolem as Skolem
> import qualified Data.List as List

* Quantifier Elimination

> lift :: (Vars -> Formula -> Formula) 
>      -> (Formula -> Formula) 
>      -> (Vars -> Formula -> Formula) 
>      -> Formula -> Formula 
> lift afn nfn qfn fm = 
>   Skolem.simplify $ qelift (Fol.fv fm) (Decidable.miniscope fm)
>   where qelift vars f = case f of
>           Atom _ -> afn vars f
>           Not p -> (¬) $ qelift vars p
>           And p q -> qelift vars p ∧ qelift vars q
>           Or p q -> qelift vars p ∨ qelift vars q
>           Imp p q -> qelift vars p ⊃ qelift vars q
>           Iff p q -> qelift vars p ⇔ qelift vars q
>           All x p -> (¬) $ qelift vars $ (∃) x $ (¬) p
>           Ex x p -> let djs = F.disjuncts $ nfn $ qelift (x:vars) p in
>                         F.listDisj (map (qelim (qfn vars) x) djs)
>           _ -> f 

> qelim :: (Formula -> Formula) -> Var -> Formula -> Formula 
> qelim bfn x p = 
>   let cjs = F.conjuncts p 
>       (ycjs, ncjs) = List.partition (List.elem x . Fol.fv) cjs in
>   if ycjs == [] then p else
>   let q = bfn (Ex x (F.listConj ycjs)) in
>   foldr And q ncjs

> cnnf :: (Formula -> Formula) -> Formula -> Formula 
> cnnf lfn = Skolem.simplify . cnnf' . Skolem.simplify
>   where cnnf' f = case f of 
>           [$form| $p ∧ $q |] -> p' ∧ q'
>             where p' = cnnf' p
>                   q' = cnnf' q
>           [$form| $p ∨ $q |] -> p' ∨ q'
>             where p' = cnnf' p
>                   q' = cnnf' q
>           [$form| $p ⊃ $q |] -> np' ∨ q'
>             where np' = cnnf' $ (¬) p
>                   q' = cnnf' q
>           [$form| $p ⇔ $q |] -> p' ∧ q' ∨ np' ∧ nq'
>             where p' = cnnf' $ p
>                   np' = cnnf' $ (¬) p
>                   q' = cnnf' q
>                   nq' = cnnf' $ (¬) q
>           [$form| ¬ ¬ $p |] -> cnnf' p
>           [$form| ¬ ($p ∧ $q) |] -> np' ∨ nq'
>             where np' = cnnf' $ (¬) p
>                   nq' = cnnf' $ (¬) q
>           [$form| ¬ ($p ∧ $q ∨ $p' ∧ $r) |] | p' == F.opp p -> pq ∨ pr
>               where pq = cnnf' $ p ∧ (¬) q
>                     pr = cnnf' $ p' ∧ (¬) r
>           [$form| ¬ ($p ∨ $q) |] -> np' ∧ nq'
>             where np' = cnnf' $ (¬) p
>                   nq' = cnnf' $ (¬) q
>           [$form| ¬ ($p ⊃ $q) |] -> p' ∧ nq'
>             where p' = cnnf' p
>                   nq' = cnnf' $ (¬) q
>           [$form| ¬ ($p ⇔ $q) |] -> p' ∧ nq' ∨ np' ∧ q'
>             where p' = cnnf' $ p
>                   np' = cnnf' $ (¬) p
>                   q' = cnnf' q
>                   nq' = cnnf' $ (¬) q
>           _ -> lfn f
