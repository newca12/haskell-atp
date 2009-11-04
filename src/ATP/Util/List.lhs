
| List utilities.

* Signature

> module ATP.Util.List 
>   ( allInjectiveMaps
>   , findFirst
>   , findRemFirst
>   , partitions
>   , select
>   , sublists
>   , splits
>   , classify
>   , partition
>   , uncons
>   , foldr2
>   )
> where

* Imports

> import Prelude 

* Utils

| Given two lists l1 l2 where |l1| >= |l2|, return all
injective maps between the two lists.  For example
allInjectiveMaps [1,2,3] [4,5,6] = [[(1,4), (2,5), (3,6)], [(1,5),(2,4),(3,6)], ...]

> allInjectiveMaps :: [a] -> [b] -> [[(a,b)]]
> allInjectiveMaps [] _ = [[]]
> allInjectiveMaps (_:_) [] = []
> allInjectiveMaps (x:xs) ys = 
>   let sels = map (flip select ys) [0..length ys-1] 
>       f (y, ys') = map ((x, y):) (allInjectiveMaps xs ys')
>   in concat $ map f sels

Grab the nth element out of a list and return the element with
the modified list.

> select :: Int -> [a] -> (a, [a])
> select _ [] = error "select: empty" 
> select 0 (x:xs) = (x, xs)
> select n (x:xs) = (y, x:xs')
>   where (y, xs') = select (n-1) xs

| Return the first element satisfying the function.

> findFirst :: (a -> Maybe b) -> [a] -> Maybe b
> findFirst _ [] = Nothing
> findFirst f (x:xs) = case f x of
>                        Nothing -> findFirst f xs
>                        Just y -> Just y

| Return the first element satisfying the function, and removing
  it from the list.

> findRemFirst :: (a -> Maybe b) -> [a] -> Maybe (b, [a])
> findRemFirst _ [] = Nothing
> findRemFirst f (x:xs) = case f x of
>   Nothing -> case findRemFirst f xs of
>                Nothing -> Nothing
>                Just (v, xs') -> Just (v, x:xs')
>   Just y -> Just (y, xs)

| Return all partitions of a list

> partitions :: [a] -> [[[a]]]
> partitions [] = [[]]
> partitions (x:xs) = concat $ map f parts
>   where parts = partitions xs
>         f p = ([x]:p) : insertAll x p

| insertAll x [l1, ..., ln] --> [[(x:l1), l2, ..., ln], 
                                 [l1, (x:l2), ..., ln], 
                                 ...
                                 [l1, l2, ..., (x:ln)]]

> insertAll :: a -> [[a]] -> [[[a]]]
> insertAll _ [] = []
> insertAll x (l:ls) = ((x:l) : ls) : map (l:) ls'
>   where ls' = insertAll x ls

| Return all sublists of a list

> sublists :: [a] -> [[a]]
> sublists [] = [[]]
> sublists (x:xs) = xs' ++ map (x:) xs'
>   where xs' = sublists xs

| Return all sublists of a list with the corresponding list difference

> splits :: [a] -> [([a], [a])]
> splits [] = [([], [])]
> splits (x:xs) = map (use x) xs' ++ map (leave x) xs'
>   where xs' = splits xs
>         use a (as, bs) = (a:as, bs)
>         leave a (as, bs) = (as, a:bs)

> classify :: (a -> Either b c) -> [a] -> ([b], [c])
> classify _ [] = ([], [])
> classify f (x:xs) = 
>   case f x of 
>     Left a -> (a:as, bs)
>     Right b -> (as, b:bs)
>   where (as, bs) = classify f xs

> partition :: (a -> Maybe (Either b c)) -> [a] -> ([b], [c])
> partition _ [] = ([], [])
> partition f (x:xs) =
>   let yzs@(ys, zs) = partition f xs in
>   case f x of 
>     Nothing -> yzs
>     Just (Left y) -> (y:ys, zs)
>     Just (Right z) -> (ys, z:zs)

> uncons :: [a] -> (a, [a])
> uncons [] = error "Impossible" 
> uncons (h:t) = (h, t)

> foldr2 :: (a -> b -> c -> c) -> c -> [a] -> [b] -> c
> foldr2 _ b [] [] = b
> foldr2 f b (x:xs) (y:ys) = foldr2 f (f x y b) xs ys
> foldr2 _ _ _ _ = error "foldr2: length mismatch"
