
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

> import Prelude hiding (print)
> import qualified ATP.FOL as FOL
> import ATP.FormulaSyn
> import qualified ATP.Prop as Prop
> import ATP.Util.Lib((⟾))
> import qualified Data.List as List

* Simplification

> simplify :: Formula -> Formula
> simplify fm = case fm of 
>   [$form| ¬ $p |] -> simplify1 $ (¬) $ simplify p
>   [$form| $p ∧ $q |] -> simplify1 $ simplify p ∧ simplify q
>   [$form| $p ∨ $q |] -> simplify1 $ simplify p ∨ simplify q
>   [$form| $p ⊃ $q |] -> simplify1 $ simplify p ⊃ simplify q
>   [$form| $p ⇔ $q |] -> simplify1 $ simplify p ⇔ simplify q
>   [$form| ∀ $x. $p |] -> simplify1 $ (¥) x (simplify p)
>   [$form| ∃ $x. $p |] -> simplify1 $ (∃) x (simplify p)
>   _ -> fm

> simplify1 :: Formula -> Formula
> simplify1 fm = case fm of
>   All x p -> if List.elem x (FOL.fv p) then fm else p
>   Ex x p -> if List.elem x (FOL.fv p) then fm else p
>   _ -> Prop.simplify1 fm

* Negation normal form

> nnf :: Formula -> Formula
> nnf fm = case fm of 
>   [$form| $p ∧ $q |] -> nnf p ∧ nnf q
>   [$form| $p ∨ $q |] -> nnf p ∨ nnf q
>   [$form| $p ⊃ $q |] -> np' ∨ nnf q
>     where np' = nnf $ (¬) p
>   [$form| $p ⇔ $q |] -> p' ∧ q' ∨ np' ∧ nq'
>     where p' = nnf $ p
>           np' = nnf $ (¬) p
>           q' = nnf q
>           nq' = nnf $ (¬) q
>   [$form| ¬ ¬ $p |] -> nnf p
>   [$form| ¬ ($p ∧ $q) |] -> np' ∨ nq'
>     where np' = nnf $ (¬) p
>           nq' = nnf $ (¬) q
>   [$form| ¬ ($p ∨ $q) |] -> np' ∧ nq'
>     where np' = nnf $ (¬) p
>           nq' = nnf $ (¬) q
>   [$form| ¬ ($p ⊃ $q) |] -> p' ∧ nq'
>     where p' = nnf p
>           nq' = nnf $ (¬) q
>   [$form| ¬ ($p ⇔ $q) |] -> p' ∧ nq' ∨ np' ∧ q'
>     where p' = nnf $ p
>           np' = nnf $ (¬) p
>           q' = nnf q
>           nq' = nnf $ (¬) q
>   [$form| ∀ $x. $p |] -> (¥) x (nnf p)
>   [$form| ∃ $x. $p |] -> (∃) x (nnf p)
>   [$form| ¬ (∀ $x. $p) |] -> (∃) x (nnf $ (¬) p)
>   [$form| ¬ (∃ $x. $p) |] -> (¥) x (nnf $ (¬) p)
>   _ -> fm

nnf $ parse "(∀ x. P(x)) ⊃ ((∃ y. Q(y)) ⇔ ∃ z. P(z) ∧ Q(z))"

* Prenex normal form

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
>   [$form| (∀ $x. $p) ∧ (∀ $y. $q) |] -> pullq (True,True) fm (¥) (∧) x y p q
>   [$form| (∃ $x. $p) ∨ (∃ $y. $q) |] -> pullq (True,True) fm (∃) (∨) x y p q
>   [$form| (∀ $x. $p) ∧ $q |] -> pullq (True,False) fm (¥) (∧) x x p q
>   [$form| $p ∧ (∀ $y. $q) |] -> pullq (False,True) fm (¥) (∧) y y p q
>   [$form| (∀ $x. $p) ∨ $q |] -> pullq (True,False) fm (¥) (∨) x x p q
>   [$form| $p ∨ (∀ $y. $q) |] -> pullq (False,True) fm (¥) (∨) y y p q
>   [$form| (∃ $x. $p) ∧ $q |] -> pullq (True,False) fm (∃) (∧) x x p q
>   [$form| $p ∧ (∃ $y. $q) |] -> pullq (False,True) fm (∃) (∧) y y p q
>   [$form| (∃ $x. $p) ∨ $q |] -> pullq (True,False) fm (∃) (∨) x x p q
>   [$form| $p ∨ (∃ $y. $q) |] -> pullq (False,True) fm (∃) (∨) y y p q
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

print $ pullquants [$form| (∀ y. Q(y)) ∧ (∀ x. P(y)) |]

* Skolemization

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

:m +ATP.Util.Parse 
print $ skolemize [$form| ∃ y. x < y ⊃ ∀ u. ∃ v. x * u < y * v |]
print $ skolemize [$form| ∀ x. P(x) ⊃ (∃ y z. Q(y) ∨ ~(∃ z. P(z) ∧ Q(z))) |]


