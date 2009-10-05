
Union-Find 

* Signature

> module ATP.Util.UnionFind
>   ( Partition
>   , canonize,
>   , equivalent
>   , unequal
>   , equate
>   , equated
>   ) 
> where
  
* Imports

> import Prelude 
> import qualified Data.Map as Map
> import Data.Map(Map)

* Union-Find

> data Pnode a = Nonterminal a
>              | Terminal a Int

> data Partition a = Partition (Map a (Pnode a))

> terminus :: Ord a => Partition a -> a -> Maybe (a, Int)
> terminus (ptn @ (Partition m)) a = 
>   case Map.lookup a m of
>     Nothing -> Nothing
>     Just (Nonterminal b) -> terminus ptn b
>     Just (Terminal p q) -> Just (p, q)

> tryterminus :: Ord a => Partition a -> a -> (a, Int)
> tryterminus ptn a = 
>     case terminus ptn a of
>       Just p -> p
>       Nothing -> (a, 1)

> canonize :: Ord a => Partition a -> a -> a
> canonize env = fst . tryterminus env

> equivalent :: Ord a => Partition a -> a -> a -> Bool
> equivalent eqv a b = canonize eqv a == canonize eqv b

> equate :: Ord a => (a, a) -> Partition a -> Partition a
> equate (a, b) (ptn @ (Partition f)) =
>   let (a', na) = tryterminus ptn a
>       (b', nb) = tryterminus ptn b 
>       map = if a' == b' then f 
>             else if na <= nb then
>               Map.insert a' (Nonterminal b') (Map.insert b' (Terminal b' (na + nb)) f)
>             else
>               Map.insert b' (Nonterminal a') (Map.insert a' (Terminal a' (na + nb)) f) in
>   Partition map

> unequal :: Partition a
> unequal = Partition Map.empty

> equated :: Partition a -> [a]
> equated (Partition f) = Map.keys f
