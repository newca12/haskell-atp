
Set operations on lists.

* Signature

> module ATP.Util.ListSet 
>   ( ListSet
>   , setify
>   , uniq
>   , union
>   , intersect
>   , (\\), (∪), (∩)
>   , image
>   , insert
>   , unions
>   , subset
>   , psubset
>   , allSubsets
>   , allNonemptySubsets
>   , allSets
>   ) 
> where

* Imports

> import Prelude hiding (subtract)
> import qualified Data.List

* Sets as lists

> type ListSet a = [a]

> setify :: Ord a => [a] -> [a]
> setify = uniq . Data.List.sortBy compare

Remove duplicates in a sorted list

> uniq :: Ord a => [a] -> [a]
> uniq (x : t@(y:_)) = case compare x y of
>                EQ -> uniq t
>                _ -> x:uniq t
> uniq l = l

> union :: Ord a => [a] -> [a] -> [a]
> union s1 s2 = union' (setify s1) (setify s2)
>     where union' [] l2 = l2
>           union' l1 [] = l1
>           union' l1@(h1:t1) l2@(h2:t2) = 
>             case compare h1 h2 of
>               EQ -> h1 : union' t1 t2
>               LT -> h1 : union' t1 l2
>               GT -> h2 : union' l1 t2

> (∪) :: Ord a => [a] -> [a] -> [a]
> (∪) = union

> intersect :: Ord a => [a] -> [a] -> [a]
> intersect s1 s2 = intersect' (setify s1) (setify s2)
>     where intersect' [] _l2 = []
>           intersect' _l1 [] = []
>           intersect' l1@(h1:t1) l2@(h2:t2) = 
>             case compare h1 h2 of
>               EQ -> h1 : intersect' t1 t2
>               LT -> intersect' t1 l2
>               GT -> intersect' l1 t2

> (∩) :: Ord a => [a] -> [a] -> [a]
> (∩) = intersect

Difference

> (\\) :: Ord a => [a] -> [a] -> [a]
> s1 \\ s2 = subtract (setify s1) (setify s2)
>     where subtract [] _l2 = []
>           subtract l1 [] = l1
>           subtract l1@(h1:t1) l2@(h2:t2) = 
>             case compare h1 h2 of
>               EQ -> subtract t1 t2
>               LT -> h1 : subtract t1 l2
>               GT -> subtract l1 t2

Image of a function 

> image :: Ord b => (a -> b) -> [a] -> [b]
> image f = setify . map f

> insert :: Ord a => a -> [a] -> [a]
> insert x xs = union [x] xs

> subset :: Ord a => [a] -> [a] -> Bool
> subset l1 l2 = subset' (setify l1) (setify l2)
>     where
>       subset' [] _ = True
>       subset' _ [] = False
>       subset' (l1'@(h1:t1)) (h2:t2) | h1 == h2 = subset' t1 t2
>                                       | h1 < h2 = False
>                                       | otherwise = subset' l1' t2

> psubset :: Ord a => [a] -> [a] -> Bool
> psubset l1 l2 = psubset' (setify l1) (setify l2)
>     where
>       psubset' _l1 [] = False
>       psubset' [] _l2 = True
>       psubset' (l1'@(h1:t1)) (h2:t2) | h1 == h2 = psubset' t1 t2
>                                        | h1 < h2 = False
>                                        | otherwise = subset l1' t2

> unions :: Ord a => [[a]] -> [a]
> unions = setify . Data.List.concat

Power set

> allSubsets :: [a] -> [[a]]
> allSubsets [] = [[]]
> allSubsets (a:t) = let res = allSubsets t in
>                    map (a:) res ++ res

> allNonemptySubsets :: Ord a => [a] -> [[a]]
> allNonemptySubsets s = allSubsets s \\ [[]]

All subsets of a certain size.

> allSets :: Int -> [a] -> [[a]]
> allSets 0 _ = [[]]
> allSets _ [] = []
> allSets m (h:t) = map (h:) (allSets (m - 1) t) ++ allSets m t

