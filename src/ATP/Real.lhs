
* Signature 

> module ATP.Real 
>   ( qelim )
> where

* Imports

#include "undefined.h" 

> import ATP.Util.Prelude
> import qualified ATP.Complex as C
> import ATP.Complex (Sign(..), Ctx, swap)
> import qualified ATP.Cooper as Cooper
> import ATP.FormulaSyn
> import qualified ATP.Formula as F
> import qualified ATP.Poly as P
> import qualified ATP.Prop as Prop
> import qualified ATP.Qelim as Qelim
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Util.Lib as Lib
> import qualified ATP.Util.List as List

* Real

> relSigns :: [(String, [Sign])]
> relSigns = [ ("=", [Zero]), ("<=", [Zero, Negative]), (">=", [Zero, Positive])
>            , ("<", [Negative]), (">", [Positive]) ]

> testform :: Ctx -> Formula -> Bool
> testform pmat fm = Prop.eval fm evalfn
>  where 
>   evalfn (R a [p, _z]) =
>     elem (fromJust $ lookup p pmat) (fromJust $ lookup a relSigns)
>   evalfn _ = __IMPOSSIBLE__ 

> inferpsign :: ([Sign], [Sign]) -> [Sign]
> inferpsign (pd, qd) = 
>   case List.elemIndex Zero pd of
>     Nothing -> Nonzero : pd
>     Just i -> qd !! i : pd

> condense :: [[Sign]] -> [[Sign]]
> condense ps = case ps of
>   int:pt:other -> let rest = condense other in
>                  if elem Zero pt then int:pt:rest else rest
>   _ -> ps

> inferisign :: [[Sign]] -> [[Sign]]
> inferisign ps = case ps of
>   x@(l:_ls) : (_:ints) : pts@((r:_rs) : _xs) -> 
>     case (l, r) of
>       (Zero, Zero) -> error "inferisign: inconsistent"
>       (Nonzero, _) -> error "inferisign: indeterminate"
>       (_, Nonzero) -> error "inferisign: indeterminate"
>       (Zero, _) -> x:(r:ints):inferisign pts
>       (_, Zero) -> x:(l:ints):inferisign pts
>       (Negative, Negative) -> x:(l:ints):inferisign pts
>       (Positive, Positive) -> x:(l:ints):inferisign pts
>       _ -> x:(l:ints):(Zero:ints):(r:ints):inferisign pts
>   _ -> ps

> dedmatrix :: ([[Sign]] -> a) -> [[Sign]] -> a
> dedmatrix cont mat = 
>   let n = length (head mat) `div` 2 
>       mat1 = condense $ map (inferpsign . splitAt n) mat
>       mat2 = [swap True (head mat1 !! 1)] : mat1 ++ [[last mat1 !! 1]]
>       mat3 = init $ tail $ inferisign mat2
>   in cont $ condense $ map (\l -> head l : tail (tail l)) mat3

> pdividePos :: Vars -> Ctx -> Term -> Term -> Term
> pdividePos vars sgns s p = 
>   let a = P.phead vars p 
>       (k, r) = P.pdivide vars s p
>       sgn = fromJust $ C.findSign sgns a 
>   in if sgn == Zero then error "pdividePos: zero head coefficient"
>      else if sgn == Positive || k `mod` 2 == 0 then r
>      else if sgn == Negative then P.neg r else P.mul vars a r

> splitSign :: Ctx -> Term -> (Ctx -> Formula) -> Formula
> splitSign sgns pol cont = case fromJust $ C.findSign sgns pol of
>   Nonzero -> let fm = Atom $ R ">" [pol, P.zero] in
>             (fm ∧ cont (fromJust $ C.assertSign sgns (pol, Positive)))
>           ∨ ((¬) fm ∧ cont (fromJust $ C.assertSign sgns (pol, Negative)))
>   _ -> cont sgns

> splitTrichotomy :: Ctx -> Term -> (Ctx -> Formula) -> (Ctx -> Formula) -> Formula
> splitTrichotomy sgns pol contZ contP = 
>   C.splitZero sgns pol contZ (\s' -> splitSign s' pol contP)

> caseSplit :: Vars -> [Term] -> [Term] -> ([[Sign]] -> Maybe Formula) -> Ctx -> Formula
> caseSplit vars dun pols cont sgns = case pols of
>   [] -> matrix vars dun cont sgns
>   p:ops -> splitTrichotomy sgns (P.phead vars p)
>             (if P.isConstant vars p then delConst vars dun p ops cont
>              else caseSplit vars dun (P.behead vars p : ops) cont)
>             (if P.isConstant vars p then delConst vars dun p ops cont
>              else caseSplit vars (dun ++ [p]) ops cont)

> delConst :: Vars -> [Term] -> Term -> [Term] -> ([[Sign]] -> Maybe Formula) -> Ctx -> Formula
> delConst vars dun p ops cont sgns =
>   let cont' m = cont $ map (List.insertAt (length dun) (fromJust $ C.findSign sgns p)) m in
>   caseSplit vars dun ops cont' sgns

> matrix :: Vars -> [Term] -> ([[Sign]] -> Maybe Formula) -> Ctx -> Formula
> matrix vars pols cont sgns =
>   if null pols then maybe (⊥) id (cont [[]]) else
>   let p = head $ List.sortBy (Lib.decreasing (P.degree vars)) pols
>       p' = P.diff vars p 
>       i = fromJust $ List.elemIndex p pols
>       (p1, p2) = splitAt i pols
>       qs = p' : p1 ++ tail p2
>       gs = map (pdividePos vars sgns p) qs
>       cont' m = cont $ map (\l -> List.insertAt i (head l) (tail l)) m
>   in caseSplit vars [] (qs ++ gs) (dedmatrix cont') sgns

> basicQelim :: Vars -> Formula -> Formula
> basicQelim vars (Ex x p) =
>   let union (R _a [t, Fn "0" []]) = [t]
>       union _ = []
>       pols = F.atomUnion union p
>       cont mat = if List.any (\m -> testform (zip pols m) p) mat
>                  then Just (⊤) else Just (⊥)
>   in caseSplit (x:vars) [] pols cont C.initSgns
> basicQelim _ _ = __IMPOSSIBLE__ 

> qelim :: Formula -> Formula
> qelim = 
>   Skolem.simplify . Cooper.evalc . 
>     Qelim.lift P.atom (Skolem.simplify . Cooper.evalc) basicQelim
