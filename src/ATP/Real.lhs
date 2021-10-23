
* Signature 

> module ATP.Real 
>   ( qelim )
> where

* Imports

> import ATP.Util.Prelude
> import qualified ATP.Complex as C
> import ATP.Complex (Sign(..), Ctx, swap, Err, failwith)
> import qualified ATP.Cooper as Cooper
> import ATP.FormulaSyn
> import qualified ATP.Formula as F
> import qualified ATP.Poly as P
> import qualified ATP.Prop as Prop
> import qualified ATP.Qelim as Qelim
> import qualified ATP.Skolem as Skolem
> import qualified ATP.Util.Lib as Lib
> import qualified ATP.Util.List as List
> import qualified ATP.Util.Print as PP
> import Control.Monad.Error (catchError)

* Real

A Row gives the signs for a single polynomial.

> type Row = [Sign]

A Matrix gives the signs for a list of polynomials.

> type Matrix = [Row]

> relSigns :: [(String, [Sign])]
> relSigns = [ ("=", [Zero]), ("≤", [Zero, Negative]), ("≥", [Zero, Positive])
>            , ("<", [Negative]), (">", [Positive]) ]

> testform :: Ctx -> Formula -> Bool
> testform pmat fm = Prop.eval fm evalfn
>  where 
>   evalfn (R a [p, _z]) = 
>     case (lookup p pmat, lookup a relSigns) of
>       (Nothing, _) -> error' $ PP.text "testform1:" <+> pPrint (pmat, fm)
>       (_, Nothing) -> error "testform2"
>       (Just sgn, Just sgns) -> 
>         elem sgn sgns
>   evalfn _ = (throwImpossible (Impossible __FILE__ __LINE__))

> inferpsign :: (Row, Row) -> Row
> inferpsign (pd, qd) = case List.elemIndex Zero pd of
>   Nothing -> Nonzero : pd
>   Just i -> qd !! i : pd

> condense :: Matrix -> Matrix
> condense ps = case ps of
>   int:pt:other -> 
>     let rest = condense other in
>     if elem Zero pt then int:pt:rest else rest
>   _ -> ps

In OCaml, inferisign can raise the "inferisign: inconsisitent" exception.

> inferisign :: Matrix -> Err Matrix
> inferisign ps = case ps of
>   x@(l:_ls) : (_:ints) : pts@((r:_rs) : _xs) -> 
>     do sgns <- inferisign pts 
>        case (l, r) of
>          (Zero, Zero) -> failwith "inferisign: inconsistent"
>          (_, Nonzero) -> failwith "inferisign: indeterminate"
>          (Nonzero, _) -> failwith "inferisign: indeterminate"
>          (Zero, _) -> return $ x : (r : ints) : sgns
>          (_, Zero) -> return $ x : (l : ints) : sgns
>          (Negative, Negative) -> return $ x : (l : ints) : sgns
>          (Positive, Positive) -> return $ x : (l : ints) : sgns
>          _ -> return $ x : (l : ints) : (Zero : ints) : (r : ints) : sgns
>   _ -> return ps

> dedmatrix' :: Matrix -> Err Matrix
> dedmatrix' mat = 
>   let -- Split the matrix in half and infer the sign for p'
>       n = length (head mat) `div` 2 
>       mat1 = condense $ map (inferpsign . splitAt n) mat
>       -- Fill in the intervals at the points at infinity
>       mat2 = [swap True (head mat1 !! 1)] : mat1 ++ [[last mat1 !! 1]]
>       -- Infer the interval signs and drop the points at infinity
>   in do
>     mat3 <- inferisign mat2 
>     let mat3' = init $ tail mat3
>     return $ condense $ map (\l -> head l : tail (tail l)) mat3'

> dedmatrix :: (Matrix -> Err a) -> (Matrix -> Err a)
> dedmatrix cont mat = dedmatrix' mat >>= cont

> pdividePos, pdividePos' :: Vars -> Ctx -> Term -> Term -> Err Term
> pdividePos = tracef4 "pdividePos" pdividePos'
> pdividePos' vars sgns s p = 
>   let a = P.phead vars p 
>       (k, r) = P.pdivide vars s p
>   in do 
>     sgn <- C.findSign sgns a 
>     return $ 
>      if sgn == Zero then error "pdividePos: zero head coefficient"
>      else if sgn == Positive || k `mod` 2 == 0 then r
>      else if sgn == Negative then P.neg r 
>      else P.mul vars a r

> splitSign, splitSign' :: Ctx -> Term -> (Ctx -> Err Formula) -> Err Formula
> splitSign = tracef3 "splitSign" splitSign'
> splitSign' sgns pol cont = do
>   mat <- C.findSign sgns pol
>   case mat of 
>     Nonzero -> do
>       m1 <- C.assertSign sgns (pol, Positive)
>       m2 <- C.assertSign sgns (pol, Negative)
>       f1 <- cont m1
>       f2 <- cont m2
>       let fm = Atom $ R ">" [pol, P.zero] 
>       return $ (fm ∧ f1) ∨ (((¬) fm) ∧ f2)
>     _ -> cont sgns

> splitTrichotomy, splitTrichotomy' :: Ctx -> Term -> (Ctx -> Err Formula) -> (Ctx -> Err Formula) -> Err Formula
> splitTrichotomy = tracef4 "splitTrichotomy" splitTrichotomy'
> splitTrichotomy' sgns pol contZ contP = 
>   C.splitZero sgns pol contZ (\s' -> splitSign s' pol contP)

> caseSplit, caseSplit' :: Vars -> [Term] -> [Term] -> (Matrix -> Err Formula) -> Ctx -> Err Formula
> caseSplit = tracef5 "caseSplit" caseSplit'
> caseSplit' vars dun pols cont sgns = case pols of
>   [] -> matrix vars dun cont sgns
>   p:ops -> 
>     splitTrichotomy sgns (P.phead vars p)
>       (if P.isConstant vars p then delConst vars dun p ops cont
>        else caseSplit vars dun (P.behead vars p : ops) cont)
>       (if P.isConstant vars p then delConst vars dun p ops cont
>        else caseSplit vars (dun ++ [p]) ops cont)

> delConst, delConst' :: Vars -> [Term] -> Term -> [Term] -> (Matrix -> Err Formula) -> Ctx -> Err Formula
> delConst = tracef6 "delConst" delConst'
> delConst' vars dun p ops cont sgns = do
>   sgns' <- C.findSign sgns p
>   let cont' m = cont $ map (List.insertAt (length dun) sgns') m
>   caseSplit vars dun ops cont' sgns

> matrix, matrix' :: Vars -> [Term] -> (Matrix -> Err Formula) -> Ctx -> Err Formula
> matrix = tracef4 "matrix" matrix'
> matrix' vars pols cont sgns = 
>   if null pols then (cont [[]]) `catchError` handle else
>   let p = head $ List.sortBy (Lib.decreasing (P.degree vars)) pols
>       p' = P.diff vars p 
>       -- Nonfailing fromJust.  p is in the list.
>       i = fromJust $ List.elemIndex p pols 
>       (p1, p2) = splitAt i pols
>       qs = p' : p1 ++ tail p2
>   in do
>     gs <- mapM (pdividePos vars sgns p) qs
>     let cont' m = cont $ map (\l -> List.insertAt i (head l) (tail l)) m
>     caseSplit vars [] (qs ++ gs) (dedmatrix cont') sgns
>  where
>   handle "inferisign: inconsistent" = return (⊥)
>   handle s = failwith s

> basicQelim :: Vars -> Formula -> Formula
> basicQelim vars (Ex x p) =
>   let union (R _a [t, Num n]) | n == 0 = [t]
>       union _ = []
>       pols = F.atomUnion union p
>       cont mat = 
>         if any (\m -> testform (zip pols m) p) mat 
>         then return (⊤) else return (⊥)
>   in case caseSplit (x:vars) [] pols cont C.initSgns of
>        Left s -> error s
>        Right res -> res
> basicQelim _ _ = (throwImpossible (Impossible __FILE__ __LINE__))

> qelim :: Formula -> Formula
> qelim = 
>   Skolem.simplify . Cooper.evalc . 
>     Qelim.lift P.atom (Skolem.simplify . Cooper.evalc) (tracef2 "basicQelim" basicQelim)
