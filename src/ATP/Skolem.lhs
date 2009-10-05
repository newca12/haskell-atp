
* Signature

> module ATP.Skolem
>   ( simplify
>   , nnf
>   , prenex
>   , pnf
>   , specialize
>   , skolem
>   , skolemize
>   , askolemize
>   ) 
> where

* Imports

> import Prelude 
> import qualified List 
> import ATP.Util.Lib((⟾))
> import ATP.FormulaSyn
> import qualified ATP.Prop as Prop
> import qualified ATP.FOL as FOL

* Skolem

%%%%%%%%%%%%%%%%%%%%%
%%% Simplification

> simplify :: Formula -> Formula
> simplify (Not p) = simplify1 $ Not $ simplify p
> simplify (And p q) = simplify1 (simplify p ∧ simplify q)
> simplify (Or p q) = simplify1 (simplify p ∨ simplify q)
> simplify (Imp p q) = simplify1 (simplify p ⊃ simplify q)
> simplify (Iff p q) = simplify1 (simplify p ⇔ simplify q)
> simplify (All x p) = simplify1 $ All x (simplify p)
> simplify (Ex x p) = simplify1 $ Ex x (simplify p)
> simplify fm = fm

> simplify1 :: Formula -> Formula
> simplify1 fm = case fm of
>                All x p -> if List.elem x (FOL.fv p) then fm else p
>                Ex x p -> if List.elem x (FOL.fv p) then fm else p
>                _ -> Prop.simplify1 fm

%%%%%%%%%%%%%%%%%%%%%%%%
%%% Negation Normal Form

> nnf :: Formula -> Formula
> nnf (And p q) = And (nnf p) (nnf q)
> nnf (Or p q) = Or (nnf p) (nnf q)
> nnf (Imp p q) = Or (nnf (Not p)) (nnf q)
> nnf (Iff p q) = Or (And (nnf p) (nnf q)) (And (nnf(Not p)) (nnf(Not q)))
> nnf (Not(Not p)) = nnf p
> nnf (Not(And p q)) = Or (nnf(Not p)) (nnf(Not q))
> nnf (Not(Or p q)) = And (nnf(Not p)) (nnf(Not q))
> nnf (Not(Imp p q)) = And (nnf p) (nnf(Not q))
> nnf (Not(Iff p q)) = Or (And (nnf p) (nnf(Not q))) (And (nnf(Not p)) (nnf q))
> nnf (All x p) = All x (nnf p)
> nnf (Ex x p) = Ex x (nnf p)
> nnf (Not (All x p)) = Ex x (nnf (Not p))
> nnf (Not (Ex x p)) = All x (nnf (Not p))
> nnf fm = fm

nnf $ read "(∀ x. P(x)) ⊃ ((∃ y. Q(y)) ⇔ ∃ z. P(z) & Q(z))"

%%%%%%%%%%%%%%%%%%%%%%%
%%% Prenex Normal Form

> pnf :: Formula -> Formula
> pnf = prenex . nnf . simplify

> prenex :: Formula -> Formula
> prenex (All x p) = All x (prenex p)
> prenex (Ex x p) = Ex x (prenex p)
> prenex (And p q) = pullquants (prenex p ∧ prenex q)
> prenex (Or p q) = pullquants (prenex p ∨ prenex q)
> prenex fm = fm

> pullquants :: Formula -> Formula
> pullquants fm = case fm of
>   And (All x p) (All y q) -> 
>     pullq (True,True) fm All And x y p q
>   Or (Ex x p) (Ex y q) -> 
>     pullq (True,True) fm Ex Or x y p q
>   And (All x p) q -> pullq (True,False) fm All And x x p q
>   And p (All y q) -> pullq (False,True) fm All And y y p q
>   Or (All x p) q ->  pullq (True,False) fm All Or x x p q
>   Or p (All y q) ->  pullq (False,True) fm All Or y y p q
>   And (Ex x p) q -> pullq (True,False) fm Ex And x x p q
>   And p (Ex y q) -> pullq (False,True) fm Ex And y y p q
>   Or (Ex x p) q ->  pullq (True,False) fm Ex Or x x p q
>   Or p (Ex y q) ->  pullq (False,True) fm Ex Or y y p q
>   _ -> fm

> pullq :: (Bool, Bool) -> Formula 
>       -> (Var -> Formula -> Formula) 
>       -> (Formula -> Formula -> Formula) -> Var -> Var
>       -> Formula -> Formula -> Formula
> pullq (l,r) fm quant op x y p q =
>   let z = FOL.variant x (FOL.fv fm) 
>       p' = if l then FOL.apply (x ⟾ Var z) p else p
>       q' = if r then FOL.apply (y ⟾ Var z) q else q in
>   quant z (pullquants(op p' q'))

(∀ y. Q(y)) & (∀ x. P(y))
(∀ y. Q(y)) & (∀ x. ~ P(y))

%%%%%%%%%%%%%%%%%
%%% Skolemization

> specialize :: Formula -> Formula 
> specialize (All _ p) = specialize p
> specialize fm = fm

> skolemize :: Formula -> Formula 
> skolemize = specialize . pnf . askolemize

> askolemize :: Formula -> Formula 
> askolemize fm = fst ((skolem $ nnf $ simplify fm) (map fst (FOL.functions fm)))

> skolem :: Formula -> Vars -> (Formula, [Func])
> skolem fm fns = case fm of
>     Ex y p ->
>         let xs = FOL.fv(fm) 
>             f = FOL.variant (if xs == [] then "c_" ++ y else "f_" ++ y) fns 
>             fx = Fn f (map Var xs) in
>         skolem (FOL.apply (y ⟾ fx) p) (f:fns)
>     All x p -> let (p', fns') = skolem p fns in (All x p', fns')
>     And p q -> skolem2 And (p, q) fns
>     Or p q -> skolem2 Or (p, q) fns
>     _ -> (fm, fns)

> skolem2 :: (Formula -> Formula -> Formula) -> (Formula, Formula) 
>         -> Vars -> (Formula, [Func])
> skolem2 cons (p,q) fns =
>   let (p', fns') = skolem p fns 
>       (q', fns'') = skolem q fns' in
>   (cons p' q', fns'')

skolemize $ read "∃ y. x < y ⊃ ∀ u. ∃ v. x * u < y * v"
skolemize $ read "∀ x. P(x) ⊃ (∃ y z. Q(y) | ~(∃ z. P(z) & Q(z)))"

