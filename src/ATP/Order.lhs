
> module Order ( earlier
>              , termSize
>              , lpoGt
>              , lpoGe
>              , weight
>              ) where
                        
> import Prelude 
> import FormulaSyn
> import qualified Fol

> termSize :: Term -> Int
> termSize (Var _) = 1
> termSize (Fn _ ts) = 1 + sum (map termSize ts)

> lexord :: Eq a => (a -> a -> Bool) -> [a] -> [a] -> Bool
> lexord ord (h1:t1) (h2:t2) = if ord h1 h2 
>                              then length t1 == length t2
>                              else h1 == h2 && lexord ord t1 t2
> lexord _ _ _ = False

> lpoGt :: ((String, Int) -> (String, Int) -> Bool) -> Term -> Term -> Bool
> lpoGt w s t = 
>   case (s, t) of 
>     (_, Var x) -> not(s == t) && elem x (Fol.fv s)
>     (Fn f fargs, Fn g gargs) -> 
>       any (\si -> lpoGe w si t) fargs ||
>       all (lpoGt w s) gargs &&
>       (f == g && lexord (lpoGt w) fargs gargs ||
>        w (f, length fargs) (g, length gargs))
>     _ -> False

> lpoGe :: ((Var, Int) -> (Var, Int) -> Bool) -> Term -> Term -> Bool
> lpoGe w s t = s == t || lpoGt w s t

> weight :: Vars -> (Var, Int) -> (Var, Int) -> Bool
> weight lis (f, n) (g, m) = if f == g then n > m else earlier lis g f

> earlier :: Ord a => [a] -> a -> a -> Bool
> earlier (h:t) x y = not(h == y) && (h == x || earlier t x y)
> earlier [] _ _ = False
