
* Signature

> module ATP.Interpolation
>   ( interpolate
>   , einterpolate
>   ) 
> where

* Imports

#include "../undefined.h" 

> import ATP.Util.Prelude
> import qualified ATP.DefCnf as Cnf
> import qualified ATP.EqElim as EqElim
> import qualified ATP.Equal as Equal
> import qualified ATP.Fol as Fol
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Herbrand as Herbrand
> import qualified ATP.Order as Order
> import qualified ATP.Prop as Prop
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Util.ListSet as Set
> import ATP.Util.ListSet((\\), (∪))
> import qualified ATP.Util.Lib as Lib
> import ATP.Util.Lib((⟾))
> import ATP.Util.Log (Log)
> import qualified Data.List as List
> import qualified Data.Map as Map

* Interpolation

> pinterpolate :: Formula -> Formula -> Formula
> pinterpolate p q = 
>   let orify a r = Prop.apply (a ⟾ (⊥)) r ∨ Prop.apply (a ⟾ (⊤)) r in
>   Prop.simplify $ foldr orify p (Prop.atoms p \\ Prop.atoms q)

Again we can express the proof as an algorithm, for simplicity using the 
Davis-Putnam procedure from section 3.8 to ﬁnd the set of ground instances. 
(This will usually loop indeﬁnitely unless the user does indeed supply for- 
mulas p and q such that |= p ∧ q ⇒ ⊥.) 

> urinterpolate :: Log m => Formula -> Formula -> m (Formula)
> urinterpolate p q = 
>   let fm = Skolem.specialize $ Skolem.prenex $ p ∧ q
>       fvs = Fol.fv fm
>       (consts, funcs) = Herbrand.herbfuns fm
>       cntms = map (\(c, _) -> Fn c []) consts in
>   do tups <- Herbrand.dpRefineLoop (Prop.simpcnf fm) cntms funcs fvs 0 [] [] []
>      let fmis = map (\tup -> Fol.apply (Map.fromList (zip fvs tup)) fm) tups
>          (ps, qs) = List.unzip (map F.destAnd fmis) 
>      return $ pinterpolate (F.listConj(Set.setify ps)) (F.listConj(Set.setify qs))

To turn this into an algorithm we ﬁrst deﬁne a function to obtain all
the topmost terms whose head function is in the list fns, ﬁrst for
terms:

> toptermt :: [(Pred, Int)] -> Term -> [Term]
> toptermt _ (Var _) = []
> toptermt _ (Num _) = []
> toptermt fns (tm @ (Fn f args)) = if elem (f, length args) fns then [tm]
>                            else Set.unions (map (toptermt fns) args)

and then for formulas: 

> topterms :: [(Pred, Int)] -> Formula -> [Term]
> topterms fns = F.atomUnion (\(R _ args) -> Set.unions (map (toptermt fns) args))

For the main algorithm, we ﬁnd the pre-interpolant using urinterpolate, 
ﬁnd the top terms in it starting with non-shared function symbols, sort them 
in decreasing order of size (so no earlier one is a subterm of a later one), 
then iteratively replace them by quantiﬁed variables. 

> uinterpolate :: Log m => Formula -> Formula -> m Formula
> uinterpolate p q = 
>   let fp = Fol.functions p
>       fq = Fol.functions q
>       simpinter tms n c = 
>         case tms of
>           [] -> c
>           (tm @ (Fn f args) : otms) -> 
>             let v = "v_" ++ show n
>                 c' = EqElim.replace (tm ⟾ Var v) c
>                 c'' = if elem (f, length args) fp 
>                       then (∃) v c' else (¥) v c' in
>             simpinter otms (n+1::Int) c'' 
>           _ -> __IMPOSSIBLE__ in
>   do c <- urinterpolate p q 
>      let tts = topterms ((fp \\ fq) ∪ (fq \\ fp)) c
>          tms = List.sortBy (Lib.decreasing Order.termSize) tts 
>      return $ simpinter tms 1 c

Note that while an individual step of the generalization procedure is valid 
regardless of whether we choose a maximal subterm, we do need to observe 
the ordering restriction to allow repeated application, otherwise we might 
end up with a term involving an unshared function h where one of the 
subterms is non-ground, when the lemma is not applicable. If we try this 
on our current example, we now get a true interpolant as expected. It uses 
only the common language of p and q: 

--FIXME:

Now we need to lift interpolation to arbitrary formulas. Once again we use 
Skolemization. Let us suppose ﬁrst that the two formulas p and q have no 
common free variables. Since 
|= p∧q ⇒ ⊥ we also have |= (∃u1 · · · un .p∧q) ⇒ 
⊥ where the ui are the free variables. If we Skolemize ∃u1 · · · un . p ∧ q we 
get a closed universal formula of the form p∗ 
∧ q∗ , with |= p∗ ∧ q∗ ⇒ ⊥. 
Thus we can apply uinterpolate to obtain an interpolant. Recall that 
diﬀerent Skolem functions are used for the diﬀerent existential quantiﬁers 
in p and q, 
† while there are no common free variables that would make 
any of the Skolem constants for the ui common. Thus, none of the newly 
introduced Skolem functions are common to p∗ and q∗ and will not appear 
in the interpolant c. And since 
|= p∗ ⇒ c and |= q∗ ⇒ ¬c with c containing 
none of the Skolem functions, the basic conservativity result (section 3.6) 
assures us that 
|= p ⇒ c and |= q ⇒ ¬c, and it is also an interpolant for the 
original formulas. This is realized in the following algorithm:      

> cinterpolate :: Log m => Formula -> Formula -> m Formula
> cinterpolate p q = 
>   let fm = Skolem.nnf (p ∧ q)
>       efm = F.listEx (Fol.fv fm) fm
>       fns = map fst (Fol.functions fm)
>       (p', q') = F.destAnd $ fst $ Skolem.skolem efm fns 
>   in uinterpolate p' q'

To deal with shared variables we could introduce Skolem constants by 
existential quantiﬁcation before the core operation. The only diﬀerence is 
that we need to replace them by variables again in the ﬁnal result to respect 
the conditions for an interpolant. We elect to ‘manually’ replace the common 
variables by new constants c i and then restore them afterwards.

> interpolate :: Log m => Formula -> Formula -> m Formula
> interpolate p q =
>   let vs = map Var (Set.intersect (Fol.fv p) (Fol.fv q))
>       fns = Fol.functions (p ∧ q)
>       n = foldr (Cnf.maxVarIndex "c_" . fst) 0 fns + 1
>       cs = map (\i -> Fn ("c_" ++ show i) []) [n .. n + length vs - 1]
>       fn_vc = Map.fromList (zip vs cs)
>       fn_cv = Map.fromList (zip cs vs)
>       p' = EqElim.replace fn_vc p 
>       q' = EqElim.replace fn_vc q in
>   do fm <- cinterpolate p' q'
>      return $ EqElim.replace fn_cv fm

There are yet two further generalizations to be made. First, note that 
interpolation applies equally to logic with equality, where now the inter- 
polant may contain the equality symbol (even if only one of the formulas p 
and q does). We simply note that 
|= p ∧ q ⇒ ⊥ in logic with equality iﬀ 
|= (p ∧ eqaxiom(p)) ∧ (q ∧ eqaxiom(q)) ⇒ ⊥ in standard ﬁrst-order logic. 
Since the augmentations a 
∧ eqaxiom(a) have the same language as a plus 
equality, the interpolant will involve only shared symbols in the original 
formulas and possibly the equality sign. To implement this, we can extract 
the equality axioms from equalitize (which is designed for validity-proving 
and hence adjoins them as hypotheses): 

> einterpolate :: Log m => Formula -> Formula -> m Formula
> einterpolate p q =
>   let p' = Equal.equalitize p
>       q' = Equal.equalitize q
>       p'' = if p == p' then p else fst (F.destImp p') ∧ p
>       q'' = if q == q' then q else fst (F.destImp q') ∧ q in
>   interpolate p'' q''
