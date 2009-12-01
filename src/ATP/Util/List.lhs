
| List utilities.

* Signature

> module ATP.Util.List 
>   ( module Data.List
>   , allInjectiveMaps
>   , allPairs
>   , distinctPairs
>   , findFirst
>   , findRemFirst
>   , partitions
>   , select
>   , sublists
>   , splits
>   , classify
>   , partition'
>   , uncons
>   , foldr2
>   , insertAt
>   , all2
>   , mapi
>    -- * Tests
>   , tests
>   )
> where

* Imports

> import Prelude 
> import ATP.Util.Lib (pow)
> import qualified Control.Monad as M
> import Data.List
> import qualified Test.QuickCheck as Q
> import Test.QuickCheck (Gen, Property, (==>))

* Util

Generate small ints

> ints :: Int -> Gen Int
> ints n = Q.choose (0, n)

Lists with a maximum length.

> list :: Int -> Gen [Int]
> list 0 = return []
> list n 
>  | n > 0 = Q.oneof [ return [], M.liftM2 (:) Q.arbitrary (list $ n-1) ]
>  | otherwise = error "Impossible" 

Lists with very few possibilities for values.

> list' :: Int -> Int -> Gen [Int]
> list' 0 _ = return []
> list' n m
>  | n > 0 = Q.oneof [ return [], M.liftM2 (:) (ints m) (list' (n-1) m) ]
>  | otherwise = error "Impossible" 

* List operations absent from Data.List

** all2

all2 f xs ys 

returns true iff the lengths of xs and ys are the same and 
f xi yi --> True for all i < length xs

> all2 :: (a -> b -> Bool) -> [a] -> [b] -> Bool
> all2 _ [] [] = True
> all2 f (x:xs) (y:ys) = f x y && all2 f xs ys
> all2 _ _ _ = False

** allPairs

allPairs f xs ys

returns f applied to all pairs of an element of xs with an element of ys

> allPairs :: (a -> b -> c) -> [a] -> [b] -> [c]
> allPairs f xs ys = [f x y | x <- xs, y <- ys]

** allInjectiveMaps

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

> prop_allInjectiveMaps_length :: Property
> prop_allInjectiveMaps_length = Q.label "allInjectiveMaps_length" $
>   Q.forAll (list 8) $ \xs -> 
>   Q.forAll (list 8) $ \ys -> 
>   length (allInjectiveMaps xs ys) ==
>     product (take (length xs) [length ys, length ys - 1 .. ])

** classify

| Partition based on Either

> classify :: (a -> Either b c) -> [a] -> ([b], [c])
> classify _ [] = ([], [])
> classify f (x:xs) = 
>   case f x of 
>     Left a -> (a:as, bs)
>     Right b -> (as, b:bs)
>   where (as, bs) = classify f xs

** distinctPairs 

> distinctPairs :: [a] -> [(a,a)]
> distinctPairs (x:xs) = 
>   foldr (\y l -> (x,y) : l) (distinctPairs xs) xs
> distinctPairs [] = []

** findFirst

| Return the first element satisfying the function.

> findFirst :: (a -> Maybe b) -> [a] -> Maybe b
> findFirst _ [] = Nothing
> findFirst f (x:xs) = case f x of
>   Nothing -> findFirst f xs
>   Just y -> Just y

> prop_findFirst_correct :: Property
> prop_findFirst_correct = Q.label "findFirst_correct" $
>   Q.forAll (list' 20 10) $ \xs -> 
>   Q.forAll (ints 10) $ \n -> 
>     case findFirst (\x -> if x == n then Just x else Nothing) xs of
>       Nothing -> not $ elem n xs
>       Just k -> k == n

** findRemFirst 

| Return the first element satisfying the function, and removing
  it from the list.

> findRemFirst :: (a -> Maybe b) -> [a] -> Maybe (b, [a])
> findRemFirst _ [] = Nothing
> findRemFirst f (x:xs) = case f x of
>   Nothing -> case findRemFirst f xs of
>                Nothing -> Nothing
>                Just (v, xs') -> Just (v, x:xs')
>   Just y -> Just (y, xs)

** insertAll

| insertAll x [l1, ..., ln] --> [[(x:l1), l2, ..., ln], 
                                 [l1, (x:l2), ..., ln], 
                                 ...
                                 [l1, l2, ..., (x:ln)]]

> insertAll :: a -> [[a]] -> [[[a]]]
> insertAll _ [] = []
> insertAll x (l:ls) = ((x:l) : ls) : map (l:) ls'
>   where ls' = insertAll x ls

** insertAt 

| Insert an element at a given position in a list.  
insertAt n x l is a list where x is the nth element.

> insertAt :: Int -> a -> [a] -> [a]
> insertAt 0 x xs = x:xs
> insertAt _ _ [] = error "insertAt: empty"
> insertAt n x (y:ys) = y:insertAt (n-1) x ys

> prop_insertAt_length :: Property
> prop_insertAt_length = Q.label "insertAt_length" $
>   Q.forAll (list 10) $ \xs -> 
>   Q.forAll (ints $ length xs) $ \n -> 
>    n <= length xs ==> 
>    0 <= n ==> 
>     length (insertAt n 7 xs) == length xs + 1

> prop_insertAt_correct :: Property
> prop_insertAt_correct = Q.label "insertAt_correct" $
>   Q.forAll (list 10) $ \xs -> 
>   Q.forAll (ints $ length xs) $ \n -> 
>    n <= length xs ==> 
>    0 <= n ==> 
>     insertAt n 7 xs == take n xs ++ 7 : drop n xs

** foldr2 

| Double fold

> foldr2 :: (a -> b -> c -> c) -> c -> [a] -> [b] -> c
> foldr2 _ b [] [] = b
> foldr2 f b (x:xs) (y:ys) = foldr2 f (f x y b) xs ys
> foldr2 _ _ _ _ = error "foldr2: length mismatch"

** mapi

Map with element index as argument

> mapi :: (Int -> a -> b) -> [a] -> [b]
> mapi f = mapi' 0
>   where mapi' _ [] = []
>         mapi' n (h:t) = f n h : mapi' (n+1) t

** partition' 

| Partition based on Maybe Either

> partition' :: (a -> Maybe (Either b c)) -> [a] -> ([b], [c])
> partition' _ [] = ([], [])
> partition' f (x:xs) =
>   let yzs@(ys, zs) = partition' f xs in
>   case f x of 
>     Nothing -> yzs
>     Just (Left y) -> (y:ys, zs)
>     Just (Right z) -> (ys, z:zs)

** partitions

| Return all partitions of a list

> partitions :: [a] -> [[[a]]]
> partitions [] = [[]]
> partitions (x:xs) = concat $ map f parts
>   where parts = partitions xs
>         f p = ([x]:p) : insertAll x p

** uncons

| List destructor

> uncons :: [a] -> (a, [a])
> uncons [] = error "Impossible" 
> uncons (h:t) = (h, t)

** select

| Grab the nth element out of a list and return the element with
the modified list.

> select :: Int -> [a] -> (a, [a])
> select _ [] = error "select: empty" 
> select 0 (x:xs) = (x, xs)
> select n (x:xs) = (y, x:xs')
>   where (y, xs') = select (n-1) xs

** splits 

| Return all sublists of a list with the corresponding list difference

> splits :: [a] -> [([a], [a])]
> splits [] = [([], [])]
> splits (x:xs) = map (use x) xs' ++ map (leave x) xs'
>   where xs' = splits xs
>         use a (as, bs) = (a:as, bs)
>         leave a (as, bs) = (as, a:bs)

** sublists

| Return all sublists of a list

> sublists :: [a] -> [[a]]
> sublists [] = [[]]
> sublists (x:xs) = xs' ++ map (x:) xs'
>   where xs' = sublists xs

> prop_sublists_length :: Property
> prop_sublists_length = Q.label "sublists_length" $
>   Q.forAll (list 8) $ \xs -> 
>     length (sublists xs) == 2 `pow` length xs

* Tests

> tests :: IO ()
> tests = do 
>   Q.quickCheck prop_allInjectiveMaps_length
>   Q.quickCheck prop_findFirst_correct
>   Q.quickCheck prop_insertAt_correct
>   Q.quickCheck prop_insertAt_length
>   Q.quickCheck prop_sublists_length

