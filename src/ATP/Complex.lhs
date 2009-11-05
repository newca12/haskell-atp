
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

 [x, a]
 [(1 % 1 + a * 0 % 1) + x * ((0 % 1 + a * 1 % 1) + x * 1 % 1)]
 [1 % 1 + x * (0 % 1 + x * (0 % 1 + x * (0 % 1 + x * 1 % 1)))]
 [(1 % 1, Positive), (0 % 1, Zero)]

> cqelim :: Vars -> ([Term], [Term]) -> Ctx -> Formula
> cqelim vars (eqs, neqs) sgns =
>   case List.find (P.isConstant vars) eqs of
>     Just c -> case assertSign sgns (c, Zero) of
>       Nothing -> (⊥)
>       Just sgns' -> 
>         let eqs' = eqs \\ [c] in
>         Equal.mkEq c P.zero ∧ cqelim vars (eqs', neqs) sgns'
>     Nothing -> 
>       if null eqs then F.listConj $ map (polyNonzero vars sgns) neqs else
>       let n = minimum $ map (P.degree vars) eqs
>           p = Maybe.fromJust $ List.find (\p' -> P.degree vars p' == n) eqs
>           oeqs = eqs \\ [p]
>       in splitZero sgns (P.phead vars p) 
>            (cqelim vars (P.behead vars p : oeqs, neqs))
>            $ \sgns' -> 
>               let cfn s = snd $ P.pdivide vars s p in
>               if not $ null oeqs then cqelim vars (p : map cfn oeqs, neqs) sgns'
>               else if null neqs then (⊤) else
>               let q = foldr1 (P.mul vars) neqs in
>               polyNondiv vars sgns' p (P.pow vars q (P.degree vars p))

> initSgns :: Ctx
> initSgns = [ (P.one, Positive), (P.zero, Zero) ]

> basicQelim :: Vars -> Formula -> Formula
> basicQelim vars (Ex x p) =
>   let (eqs, neqs) = List.partition (not . F.negative) (F.conjuncts p) in
>   cqelim (x : vars) (map Equal.lhs eqs, map (Equal.lhs . F.opp) neqs) initSgns
> basicQelim _ _ = __IMPOSSIBLE__ 

> qelim :: Formula -> Formula
> qelim = 
>   Skolem.simplify . Cooper.evalc . 
>     Qelim.lift P.atom (Prop.dnf . Qelim.cnnf id . Cooper.evalc) basicQelim

* Tests

let polytest tm = polynate (free tm)) tm;;

let lagrange_4 = polytest
 <<|(((x1^2) + (x2^2) + (x3^2) + (x4^2)) *
     ((y1^2) + (y2^2) + (y3^2) + (y4^2))) -
    ((((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4))^2)  +
     (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3))^2)  +
     (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2))^2)  +
     (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1))^2))|>>;;

let lagrange_8 = polytest
 <<|((p1^2 + q1^2 + r1^2 + s1^2 + t1^2 + u1^2 + v1^2 + w1^2) *
     (p2^2 + q2^2 + r2^2 + s2^2 + t2^2 + u2^2 + v2^2 + w2^2)) -
     ((p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1* w2)^2 +
      (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1* v2)^2 +
      (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1* u2)^2 +
      (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1* t2)^2 +
      (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1* s2)^2 +
      (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1* r2)^2 +
      (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1* q2)^2 +
      (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1* p2)^2)|>>;;

let liouville = polytest
 <<|6 * (x1^2 + x2^2 + x3^2 + x4^2)^2 -
    (((x1 + x2)^4 + (x1 + x3)^4 + (x1 + x4)^4 +
      (x2 + x3)^4 + (x2 + x4)^4 + (x3 + x4)^4) +
     ((x1 - x2)^4 + (x1 - x3)^4 + (x1 - x4)^4 +
      (x2 - x3)^4 + (x2 - x4)^4 + (x3 - x4)^4))|>>;;

let fleck = polytest
 <<|60 * (x1^2 + x2^2 + x3^2 + x4^2)^3 -
    (((x1 + x2 + x3)^6 + (x1 + x2 - x3)^6 +
      (x1 - x2 + x3)^6 + (x1 - x2 - x3)^6 +
      (x1 + x2 + x4)^6 + (x1 + x2 - x4)^6 +
      (x1 - x2 + x4)^6 + (x1 - x2 - x4)^6 +
      (x1 + x3 + x4)^6 + (x1 + x3 - x4)^6 +
      (x1 - x3 + x4)^6 + (x1 - x3 - x4)^6 +
      (x2 + x3 + x4)^6 + (x2 + x3 - x4)^6 +
      (x2 - x3 + x4)^6 + (x2 - x3 - x4)^6) +
     2 * ((x1 + x2)^6 + (x1 - x2)^6 +
          (x1 + x3)^6 + (x1 - x3)^6 +
          (x1 + x4)^6 + (x1 - x4)^6 +
          (x2 + x3)^6 + (x2 - x3)^6 +
          (x2 + x4)^6 + (x2 - x4)^6 +
          (x3 + x4)^6 + (x3 - x4)^6) +
     36 * (x1^6 + x2^6 + x3^6 + x4^6))|>>;;

let hurwitz = polytest
 <<|5040 * (x1^2 + x2^2 + x3^2 + x4^2)^4 -
    (6 * ((x1 + x2 + x3 + x4)^8 +
          (x1 + x2 + x3 - x4)^8 +
          (x1 + x2 - x3 + x4)^8 +
          (x1 + x2 - x3 - x4)^8 +
          (x1 - x2 + x3 + x4)^8 +
          (x1 - x2 + x3 - x4)^8 +
          (x1 - x2 - x3 + x4)^8 +
          (x1 - x2 - x3 - x4)^8) +
     ((2 * x1 + x2 + x3)^8 +
      (2 * x1 + x2 - x3)^8 +
      (2 * x1 - x2 + x3)^8 +
      (2 * x1 - x2 - x3)^8 +
      (2 * x1 + x2 + x4)^8 +
      (2 * x1 + x2 - x4)^8 +
      (2 * x1 - x2 + x4)^8 +
      (2 * x1 - x2 - x4)^8 +
      (2 * x1 + x3 + x4)^8 +
      (2 * x1 + x3 - x4)^8 +
      (2 * x1 - x3 + x4)^8 +
      (2 * x1 - x3 - x4)^8 +
      (2 * x2 + x3 + x4)^8 +
      (2 * x2 + x3 - x4)^8 +
      (2 * x2 - x3 + x4)^8 +
      (2 * x2 - x3 - x4)^8 +
      (x1 + 2 * x2 + x3)^8 +
      (x1 + 2 * x2 - x3)^8 +
      (x1 - 2 * x2 + x3)^8 +
      (x1 - 2 * x2 - x3)^8 +
      (x1 + 2 * x2 + x4)^8 +
      (x1 + 2 * x2 - x4)^8 +
      (x1 - 2 * x2 + x4)^8 +
      (x1 - 2 * x2 - x4)^8 +
      (x1 + 2 * x3 + x4)^8 +
      (x1 + 2 * x3 - x4)^8 +
      (x1 - 2 * x3 + x4)^8 +
      (x1 - 2 * x3 - x4)^8 +
      (x2 + 2 * x3 + x4)^8 +
      (x2 + 2 * x3 - x4)^8 +
      (x2 - 2 * x3 + x4)^8 +
      (x2 - 2 * x3 - x4)^8 +
      (x1 + x2 + 2 * x3)^8 +
      (x1 + x2 - 2 * x3)^8 +
      (x1 - x2 + 2 * x3)^8 +
      (x1 - x2 - 2 * x3)^8 +
      (x1 + x2 + 2 * x4)^8 +
      (x1 + x2 - 2 * x4)^8 +
      (x1 - x2 + 2 * x4)^8 +
      (x1 - x2 - 2 * x4)^8 +
      (x1 + x3 + 2 * x4)^8 +
      (x1 + x3 - 2 * x4)^8 +
      (x1 - x3 + 2 * x4)^8 +
      (x1 - x3 - 2 * x4)^8 +
      (x2 + x3 + 2 * x4)^8 +
      (x2 + x3 - 2 * x4)^8 +
      (x2 - x3 + 2 * x4)^8 +
      (x2 - x3 - 2 * x4)^8) +
     60 * ((x1 + x2)^8 + (x1 - x2)^8 +
           (x1 + x3)^8 + (x1 - x3)^8 +
           (x1 + x4)^8 + (x1 - x4)^8 +
           (x2 + x3)^8 + (x2 - x3)^8 +
           (x2 + x4)^8 + (x2 - x4)^8 +
           (x3 + x4)^8 + (x3 - x4)^8) +
     6 * ((2 * x1)^8 + (2 * x2)^8 + (2 * x3)^8 + (2 * x4)^8))|>>;;

let schur = polytest
 <<|22680 * (x1^2 + x2^2 + x3^2 + x4^2)^5 -
    (9 * ((2 * x1)^10 +
          (2 * x2)^10 +
          (2 * x3)^10 +
          (2 * x4)^10) +
     180 * ((x1 + x2)^10 + (x1 - x2)^10 +
            (x1 + x3)^10 + (x1 - x3)^10 +
            (x1 + x4)^10 + (x1 - x4)^10 +
            (x2 + x3)^10 + (x2 - x3)^10 +
            (x2 + x4)^10 + (x2 - x4)^10 +
            (x3 + x4)^10 + (x3 - x4)^10) +
     ((2 * x1 + x2 + x3)^10 +
      (2 * x1 + x2 - x3)^10 +
      (2 * x1 - x2 + x3)^10 +
      (2 * x1 - x2 - x3)^10 +
      (2 * x1 + x2 + x4)^10 +
      (2 * x1 + x2 - x4)^10 +
      (2 * x1 - x2 + x4)^10 +
      (2 * x1 - x2 - x4)^10 +
      (2 * x1 + x3 + x4)^10 +
      (2 * x1 + x3 - x4)^10 +
      (2 * x1 - x3 + x4)^10 +
      (2 * x1 - x3 - x4)^10 +
      (2 * x2 + x3 + x4)^10 +
      (2 * x2 + x3 - x4)^10 +
      (2 * x2 - x3 + x4)^10 +
      (2 * x2 - x3 - x4)^10 +
      (x1 + 2 * x2 + x3)^10 +
      (x1 + 2 * x2 - x3)^10 +
      (x1 - 2 * x2 + x3)^10 +
      (x1 - 2 * x2 - x3)^10 +
      (x1 + 2 * x2 + x4)^10 +
      (x1 + 2 * x2 - x4)^10 +
      (x1 - 2 * x2 + x4)^10 +
      (x1 - 2 * x2 - x4)^10 +
      (x1 + 2 * x3 + x4)^10 +
      (x1 + 2 * x3 - x4)^10 +
      (x1 - 2 * x3 + x4)^10 +
      (x1 - 2 * x3 - x4)^10 +
      (x2 + 2 * x3 + x4)^10 +
      (x2 + 2 * x3 - x4)^10 +
      (x2 - 2 * x3 + x4)^10 +
      (x2 - 2 * x3 - x4)^10 +
      (x1 + x2 + 2 * x3)^10 +
      (x1 + x2 - 2 * x3)^10 +
      (x1 - x2 + 2 * x3)^10 +
      (x1 - x2 - 2 * x3)^10 +
      (x1 + x2 + 2 * x4)^10 +
      (x1 + x2 - 2 * x4)^10 +
      (x1 - x2 + 2 * x4)^10 +
      (x1 - x2 - 2 * x4)^10 +
      (x1 + x3 + 2 * x4)^10 +
      (x1 + x3 - 2 * x4)^10 +
      (x1 - x3 + 2 * x4)^10 +
      (x1 - x3 - 2 * x4)^10 +
      (x2 + x3 + 2 * x4)^10 +
      (x2 + x3 - 2 * x4)^10 +
      (x2 - x3 + 2 * x4)^10 +
      (x2 - x3 - 2 * x4)^10) +
     9 * ((x1 + x2 + x3 + x4)^10 +
          (x1 + x2 + x3 - x4)^10 +
          (x1 + x2 - x3 + x4)^10 +
          (x1 + x2 - x3 - x4)^10 +
          (x1 - x2 + x3 + x4)^10 +
          (x1 - x2 + x3 - x4)^10 +
          (x1 - x2 - x3 + x4)^10 +
          (x1 - x2 - x3 - x4)^10))|>>;;
