
* Signature

> module ATP.EqElim 
>   ( replace
>   , modifyS
>   , modifyT
>   , modifyE
>   , brand
>   , bmeson
>   ) 
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude 
> import qualified ATP.Equal as Equal
> import qualified ATP.Fol as Fol
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Meson as Meson
> import qualified ATP.Prop as Prop
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Tableaux as Tableaux
> import qualified ATP.Util.Lib as Lib
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\))
> import qualified Data.List as List
> import qualified Data.Map as Map
> import Data.Map(Map)
> import qualified Data.Maybe as Maybe

* Equality elimination

Brand's S and T modications
An earlier equality elimination method (Brand 1975) similarly eliminates
symmetry and transitivity, but keeps the re
exivity axiom 8x:R(x; x). The
advantage of doing this is that one may then perform the expansive transformation
only on positive occurrences of R(s; t), while negative occurrences
:R(u; v) can be left alone. We can adapt the proof of Theorem 4.29 as
follows. Assume the formula P[: : : ;R(s; t); : : : ;:R(u; v); : : :] whose satis-
ability is at issue is in NNF, so we can distinguish positive and negative
occurrences simply by whether they are directly covered by a negation operation.
All are treated in the way indicated for the paradigmatic examples
R(s; t) and :R(u; v). Write as before
P = P[: : : ;R[s; t]; : : : ;:R[u; v]; : : :]
but also
P0 = P[: : : ;R[s; t]; : : : ;:R(u; v); : : :]
The rst part of the proof works equally well to show that if Equiv ^ P
is satisable, so is Equiv ^ P0 and therefore (8x: R(x; x)) ^ P0. Conversely,
(8x:R(x; x)) ) R[u; v] ) R(u; v), so (8x:R(x; x)) ) :R(u; v) ) :R[u; v]
and therefore (8x:R(x; x))^P0 ) (8x:R(x; x))^P. Thus if (8x:R(x; x))^P0
is satisable, so is P and by the same proof as before, so is P.
Restricted to the special case of a formula in clausal form with R being
the equality relation, these ways of eliminating symmetry and transitivity
290 Equality
give exactly Brand's S-modication and T-modication respectively. Doing
these successively works out the same as doing equivalence-elimination
once and for all, but we'll keep them separate both to emphasize the correspondence
with Brand's work and to modularize the implementation. In
the clausal context we can also recognize positivity or negativity trivially. If
we keep the same predicate symbol, namely =, then we can just leave negative
literals untouched in each case, and only modify positive equations.
The S-transformation on a clause with n positive equations (written at the
beginning for simplicity):
s1 = t1 _    _ sn = tn _ C
leads to:
(s1 = t1 ^ t1 = s1) _    _ (sn = tn ^ tn = sn) _ C
This is no longer in clausal form, but we can redistribute and arrive at 2n
resulting clauses:
s1 = t1 _    _ sn􀀀1 = tn􀀀1 _ sn = tn _ C
s1 = t1 _    _ sn􀀀1 = tn􀀀1 _ tn = sn _ C
s1 = t1 _    _ tn􀀀1 = sn􀀀1 _ sn = tn _ C
s1 = t1 _    _ tn􀀀1 = sn􀀀1 _ tn = sn _ C
  
t1 = s1 _    _ tn􀀀1 = sn􀀀1 _ tn = sn _ C
which essentially cover all possible combinations of forward and backward
equations in the original clause. Admittedly, if n is large, this exponential
blowup in the number of clauses is not very appealing, but it can be made
manageable using a few extra tricks (cf. exercise 4). Here is the implementation
on a clause represented as a list of literals:

> modifyS :: Clause -> Clauses
> modifyS cl = case List.find Equal.isEq cl of
>                Nothing -> [cl]
>                Just eq1 -> 
>                  let (s, t) = Equal.destEq eq1 
>                      eq2 = Equal.mkEq t s
>                      sub = modifyS (cl \\ [eq1]) in
>                  map (Set.insert eq1) sub ++ map (Set.insert eq2) sub

For the T-modication, we need to replace each equation si = ti in a
clause:
s1 = t1 _    _ sn = tn _ C
4.8 Equality elimination 291
as follows:
(8w: t1 = w ) s1 = w) _    _ (8w: tn = w ) sn = w) _ C
We can pull out the universal quantiers to retain clausal form, but we
then need to use distinct variable names wi instead of a single w in each
equation. We also transform t1 = w ) s1 = w into :(ti = w) _ si = w to
return to clausal form, resulting in:
:(t1 = w1) _ s1 = w1 _    _ :(tn = wn) _ sn = wn _ C
We can implement this directly, just running through the literals successively,
recursively transforming the tail and picking a new variable w that is
neither in the transformed tail nor the unmodied literal being considered:

> modifyT :: Clause -> Clause
> modifyT [] = []
> modifyT (p:ps) = if Equal.isEq p then
>                    let (s, t) = Equal.destEq p 
>                        ps' = modifyT ps
>                        w = Var (Fol.variant "w" (Fol.fv (p:ps'))) in
>                    Not(Equal.mkEq t w) : Equal.mkEq s w : ps'
>                  else p : modifyT ps

and hence find a nested non-variable subterm where possible:

> findNestNonvar :: Term -> Maybe Term
> findNestNonvar (Var _) = Nothing 
> findNestNonvar (Num _) = Nothing 
> findNestNonvar (Fn _ args) = List.find (not . Fol.isVar) args

Now we can identify a non-variable subterm that we want to pull out in
flattening; in the case of equality this is a nested non-variable
subterm, while for the other predicate symbols it is any non-variable
subterm:

> findNvSubterm :: Formula -> Maybe Term
> findNvSubterm (Not p) = findNvSubterm p
> findNvSubterm (Atom (R "=" st)) = Lib.findApply findNestNonvar st
> findNvSubterm (Atom (R _ args)) = List.find (not . Fol.isVar) args
> findNvSubterm _ = __IMPOSSIBLE__ 

Having found such a non-variable subterm, we want to replace it with a
new variable. We don't have a general function to replace subterms (tsubst
and subst only replace variables), so we dene one, rst for terms:

> replacet :: Map Term Term -> Term -> Term
> replacet rfn tm = case Map.lookup tm rfn of
>   Just tm' -> tm'
>   Nothing -> case tm of
>     Var _ -> tm
>     Num _ -> tm
>     Fn f args -> Fn f (map (replacet rfn) args)

and then for other formulas (here we only care about literals, and can treat
quantied formulas without regard to variable capture):

> replace :: Map Term Term -> Formula -> Formula
> replace rfn = Fol.onformula (replacet rfn)

To E-modify a clause, we try to nd a nested non-variable subterm; if we
fail we are already done, and otherwise we replace that term with a fresh
variable w, add the new disjunct :(t = w) and call recursively:

> emodify :: Vars -> Clause -> Clause
> emodify fvs cls = 
>   case Lib.findApply findNvSubterm cls of
>     Nothing -> cls
>     Just t -> let w = Fol.variant "w" fvs 
>                   cls' = map (replace (Map.singleton t (Var w))) cls in
>               emodify (w : fvs) (Not(Equal.mkEq t (Var w)) : cls')

The fvs parameter tracks the free variables in the clause so far, so we
just need to set its initial value:

> modifyE :: Clause -> Clause
> modifyE cls = emodify (Fol.fv cls) cls

The overall Brand transformation now applies E-modication, then Smodi
cation and T-modication, then nally includes the re
exive clause
x = x:

> brand :: Clauses -> Clauses
> brand cls = 
>   let cls1 = map modifyE cls
>       cls2 = Set.unions (map modifyS cls1) in
>   [Equal.mkEq (Var "x") (Var "x")] : map modifyT cls2

We insert Brand's transformation into MESON's clausal framework to
give bmeson:

> bpuremeson :: Formula -> IO Int
> bpuremeson fm = 
>   let cls = brand(Prop.simpcnf (Skolem.specialize (Skolem.pnf fm)))
>       rules = List.concat (map Meson.contrapositives cls) in
>   Tableaux.deepen (\n -> do Meson.mexpand rules [] Bot Just (Map.empty, n, 0)
>                             return n) 0

> bmeson :: Formula -> IO [Int]
> bmeson fm = 
>   let fm1 = Skolem.askolemize (Not (Fol.generalize fm)) in
>   mapM (bpuremeson . F.listConj) (Prop.simpdnf fm1)
