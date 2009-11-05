
* Signature 

> module ATP.Complex 
>   ( Sign(..)
>   , Ctx
>   , swap
>   , initSgns
>   , findSign
>   , assertSign
>   , splitZero
>   , qelim 
>   )
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude hiding (div)
> import qualified ATP.Cooper as Cooper
> import qualified ATP.Equal as Equal
> import qualified ATP.Formula as F
> import ATP.FormulaSyn
> import qualified ATP.Poly as P
> import qualified ATP.Prop as Prop
> import qualified ATP.Qelim as Qelim
> import qualified ATP.Skolem as Skolem
> import ATP.Util.ListSet ((\\))
> import qualified ATP.Util.Print as PP
> import ATP.Util.Print (Print, pPrint)
> import qualified Data.List as List
> import qualified Data.Maybe as Maybe

* Signs

> data Sign = Zero | Nonzero | Positive | Negative
>   deriving (Eq, Ord, Show)

> instance Print Sign where
>   pPrint = PP.text . show

> type Ctx = [(Term, Sign)]

> swap :: Bool -> Sign -> Sign
> swap False s = s
> swap True s = case s of
>   Positive -> Negative
>   Negative -> Positive
>   _ -> s

> findSign :: Ctx -> Term -> Maybe Sign
> findSign sgns p = 
>   let (p', swf) = P.monic p in
>   swap swf <$> lookup p' sgns

> assertSign :: Ctx -> (Term, Sign) -> Maybe Ctx
> assertSign sgns (p, s) = 
>   if p == P.zero then if s == Zero then Just sgns else Nothing else
>   let (p', swf) = P.monic p
>       s' = swap swf s
>       s0 = maybe s' id (lookup p' sgns) 
>   in if s' == s0 || s0 == Nonzero && (s' == Positive || s' == Negative)
>      then Just $ (p', s') : (sgns \\ [(p', s0)]) else Nothing
>              

> splitZero :: Ctx -> Term -> (Ctx -> Formula) -> (Ctx -> Formula) -> Formula
> splitZero sgns pol contZ contN = 
>   case findSign sgns pol of
>     Just Zero -> contZ sgns
>     Just _ -> contN sgns
>     Nothing -> 
>       let eq = Atom $ R "=" [pol, P.zero] in
>       (eq ∧ contZ (Maybe.fromJust $ assertSign sgns (pol, Zero)))
>       ∨ ((¬) eq ∧ contN (Maybe.fromJust $ assertSign sgns (pol, Nonzero)))

> polyNonzero :: Vars -> Ctx -> Term -> Formula
> polyNonzero vars sgns pol = 
>   let cs = P.coefficients vars pol
>       (dcs, ucs) = List.partition (Maybe.isJust . findSign sgns) cs
>   in if List.any (\p -> findSign sgns p /= Just Zero) dcs then (⊤)
>      else if ucs == [] then (⊥) else
>      F.listDisj $ map ((¬) . flip Equal.mkEq P.zero) ucs

> polyNondiv :: Vars -> Ctx -> Term -> Term -> Formula
> polyNondiv vars sgns p s = polyNonzero vars sgns r
>  where (_, r) = P.pdivide vars s p

> cqelim :: Vars -> ([Term], [Term]) -> Ctx -> Formula
> cqelim vars (eqs, neqs) sgns =
>   case List.find (P.isConstant vars) eqs of
>     Just c -> case assertSign sgns (c, Zero) of
>       Nothing -> (⊥)
>       Just sgns' -> 
>         let eqs' = eqs \\ [c] in
>         Equal.mkEq c P.zero ∧ cqelim vars (eqs', neqs) sgns'
>     Nothing -> 
>       let res = 
>             if null eqs then F.listConj $ map (polyNonzero vars sgns) neqs else
>             let n = minimum $ map (P.degree vars) eqs
>                 p = Maybe.fromJust $ List.find (\p' -> P.degree vars p' == n) eqs
>                 oeqs = eqs \\ [p]
>             in splitZero sgns (P.phead vars p) (cqelim vars (P.behead vars p : oeqs, neqs))
>                  $ \sgns' -> 
>                     let cfn s = snd $ P.pdivide vars s p in
>                     if null oeqs then cqelim vars (p : map cfn oeqs, neqs) sgns'
>                     else if null neqs then (⊤) else
>                     let q = foldr1 (P.mul vars) neqs in
>                     polyNondiv vars sgns' p (P.pow vars q (P.degree vars p))
>       in trace' "cqelim" (PP.vcat [ pPrint vars
>                                   , pPrint eqs
>                                   , pPrint neqs
>                                   , pPrint sgns
>                                   , pPrint res]) $ res

> initSgns :: Ctx
> initSgns = [ (Fn "1" [], Positive), (Fn "0" [], Zero) ]

> basicQelim :: Vars -> Formula -> Formula
> basicQelim vars (Ex x p) =
>   let (eqs, neqs) = List.partition (not . F.negative) (F.conjuncts p) in
>   cqelim (x : vars) (map Equal.lhs eqs, map (Equal.lhs . F.opp) neqs) initSgns
> basicQelim _ _ = __IMPOSSIBLE__ 

> qelim :: Formula -> Formula
> qelim = 
>   Skolem.simplify . Cooper.evalc . 
>     Qelim.lift P.atom (Prop.dnf . Qelim.cnnf id . Cooper.evalc) basicQelim
