
* Signature

> module ATP.Qelim
>   ( cnnf
>   , liftQelim
>   , qelimDLO 
>   )
> where

* Imports

> import Prelude 
> import qualified Data.List as List

> import qualified ATP.Util.Lib as Lib
> import ATP.Util.Lib((⟾))
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\))
> import ATP.FormulaSyn
> import qualified ATP.Formula as F
> import qualified ATP.FOL as FOL
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Decidable as Decidable
> import qualified ATP.Equal as Equal
> import qualified ATP.Prop as Prop

* Quantifier Elimination

> qelim :: (Formula -> Formula) -> Var -> Formula -> Formula 
> qelim bfn x p = 
>   let cjs = F.conjuncts p 
>       (ycjs, ncjs) = List.partition (List.elem x . FOL.fv) cjs in
>   if ycjs == [] then p else
>   let q = bfn (Ex x (F.listConj ycjs)) in
>   foldr And q ncjs

> liftQelim :: (Vars -> Formula -> Formula) 
>               -> (Formula -> Formula) 
>               -> (Vars -> Formula -> Formula) 
>               -> Formula -> Formula 
> liftQelim afn nfn qfn fm = Skolem.simplify (qelift (FOL.fv fm) (Decidable.miniscope fm))
>   where qelift vars f = 
>           case f of
>             Atom _ -> afn vars f
>             Not p -> Not $ qelift vars p
>             And p q -> qelift vars p ∧ qelift vars q
>             Or p q -> qelift vars p ∨ qelift vars q
>             Imp p q -> qelift vars p ⊃ qelift vars q
>             Iff p q -> qelift vars p ⇔ qelift vars q
>             All x p -> (¬) $ qelift vars $ (∃) x $ (¬) p
>             Ex x p -> let djs = F.disjuncts $ nfn $ qelift (x:vars) p in
>                           F.listDisj (map (qelim (qfn vars) x) djs)
>             _ -> f 

> cnnf :: (Formula -> Formula) -> Formula -> Formula 
> cnnf lfn = Skolem.simplify . cnnf' . Skolem.simplify
>   where cnnf' (And p q) = And (cnnf' p) (cnnf' q)
>         cnnf' (Or p q) = Or (cnnf' p) (cnnf' q)
>         cnnf' (Imp p q) = Or (cnnf' (Not p)) (cnnf' q)
>         cnnf' (Iff p q) = Or (And (cnnf' p) (cnnf' q)) (And (cnnf' (Not p)) (cnnf' (Not q))) 
>         cnnf' (Not (Not p)) = cnnf' p              
>         cnnf' (Not (And p q)) = Or (cnnf' (Not p)) (cnnf' (Not q))
>         cnnf' (Not (Or (And p q) (And p' r))) | p' == F.opp p =
>           Or (cnnf' (And p (Not q))) (cnnf' (And p' (Not r)))
>         cnnf' (Not (Or p q)) = And (cnnf' (Not p)) (cnnf' (Not q))
>         cnnf' (Not (Imp p q)) = And (cnnf' p) (cnnf' (Not q))
>         cnnf' (Not (Iff p q)) = Or (And (cnnf' p) (cnnf' (Not q))) (And (cnnf' (Not p)) (cnnf' q))  
>         cnnf' fm = lfn fm

> lfn_dlo :: Formula -> Formula 
> lfn_dlo (Not(Atom(R "<" [s,t]))) = Or (Atom(R "=" [s,t])) (Atom (R "<" [t,s]))
> lfn_dlo (Not(Atom(R "=" [s,t]))) = Or (Atom(R "<" [s,t])) (Atom (R "<" [t,s]))
> lfn_dlo fm = fm

> dloBasic :: Formula -> Formula 
> dloBasic (Ex x p) = 
>   let vx = Var x 
>       cjs = F.conjuncts p \\ [Equal.mkEq vx vx] in
>   case List.find Equal.isEq cjs of
>     Just eqn -> let (s, t) = Equal.destEq eqn
>                     y = if s == vx then t else s in
>                 F.listConj (map (FOL.apply (x ⟾ y)) (cjs \\ [eqn]))
>     Nothing -> if elem (Atom (R "<" [vx, vx])) cjs then Bot else
>                let (lefts, rights) = List.partition (\(Atom (R "<" [_, t])) -> t == vx) cjs 
>                    ls = map (\(Atom (R "<" [l, _])) -> l) lefts
>                    rs = map (\(Atom (R "<" [_, r])) -> r) rights in
>                F.listConj (Lib.allPairs (\l r -> Atom (R "<" [l, r])) ls rs)
> dloBasic _ = error "dloBasic"               

> afn_dlo :: Vars -> Formula -> Formula 
> afn_dlo _ (Atom (R "<=" [s,t])) = Not(Atom(R "<" [t,s]))
> afn_dlo _ (Atom (R ">=" [s,t])) = Not(Atom(R "<" [s,t]))
> afn_dlo _ (Atom (R ">" [s,t])) = Atom(R "<" [t,s])
> afn_dlo _ fm = fm

> qelimDLO :: Formula -> Formula 
> qelimDLO = liftQelim afn_dlo (Prop.dnf . cnnf lfn_dlo) (const dloBasic)
