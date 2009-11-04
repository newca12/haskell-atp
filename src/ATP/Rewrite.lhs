
Rewriting

* Signature

> module ATP.Rewrite
>   ( rewrite )
> where

* Imports

> import Prelude 
> import qualified ATP.FOL as FOL
> import ATP.FormulaSyn
> import qualified ATP.Resolution as Resolution
> import qualified Data.Map as Map

* Rewriting

To rewrite a term t at the top level with an equation l = r we just attempt
to match l to t and apply the corresponding instantiation to r; the following
does this with the first in a list of equations to succeed:

> rewrite1 :: [Formula] -> Term -> Maybe Term
> rewrite1 eqs t = case eqs of
>   Atom(R "=" [l,r]):oeqs -> 
>     case Resolution.termMatch Map.empty [(l,t)] of
>       Nothing -> rewrite1 oeqs t
>       Just env -> Just $ FOL.apply env r
>   _ -> Nothing

Our interest is in rewriting at all subterms, and repeatedly, to normalize a
term w.r.t. a set of equations. Although for theoretical reasons, in particular
for applying Newman’s Lemma, it’s important to single out the ‘one-step’
(though at depth) rewrite relation !R, from an implementation point ofa
view we needn’t bother isolating it. The following function simply applies
rewrites at all possible subterms and repeatedly until no further rewrites are
possible. The user is responsible for ensuring that the rewrites terminate,
and if this is not the case this function may loop indefinitely. Where several
rewrites could be applied, the leftmost outermost subterm in the term being
rewritten is always preferred, and thereafter the first applicable equation in
the list of rewrites. Alternative strategies such as choosing the innermost
rewritable subterm would work equally well in our applications.

> rewrite :: [Formula] -> Term -> Term
> rewrite eqs tm = 
>   case rewrite1 eqs tm of
>     Just tm' -> rewrite eqs tm'
>     Nothing -> 
>       case tm of 
>         Var _ -> tm
>         Fn f args -> let tm' = Fn f (map (rewrite eqs) args) in
>                      if tm' == tm then tm else rewrite eqs tm'
