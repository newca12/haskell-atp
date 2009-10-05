
This file contains utility functions not provided by the Haskell
standard library.  Most mirror functions in Harrison's lib.ml

* Signature

> module ATP.Util.Lib 
>   ( time
>   , pow
>   , funpow
>   , decreasing
>     -- Lists
>   , findApply
>   , mapi
>   , allPairs
>   , distinctPairs
>   , all2
>     -- Strings
>   , substringIndex
>     -- Map
>   , (↦)
>   , (⟾)
>   ) 
> where

* Imports

> import Prelude
> import qualified List 
> import qualified System.CPUTime as Time
> import qualified Text.Printf as Printf
> import qualified Char 
> import qualified Data.Map as Map
> import Data.Map(Map)

* Misc

> time :: IO a -> IO a
> time a = do start <- Time.getCPUTime
>             v <- a
>             end <- Time.getCPUTime
>             let diff = (fromIntegral (end - start)) / (10E12) :: Double
>             Printf.printf "Computation time: %0.3f sec\n" (diff :: Double)
>             return v

> pow' :: Int -> Int -> Int -> Int
> pow' _ 0 acc = acc
> pow' x n acc = pow' x (n-1) (x*acc)

> pow :: Int -> Int -> Int
> pow x y = if y >= 0 then pow' x y 1 else error "negative power"

> funpow :: Int -> (a -> a) -> a -> a
> funpow n f x = iterate f x !! n

For use with sort

> decreasing :: Ord b => (a -> b) -> a -> a -> Ordering
> decreasing f x y = compare (f x) (f y)

* Lists

Return the first element of a list that returns Just.
Equivalent to 

mapM f (List.find (isJust . f) l)

> findApply :: (a -> Maybe b) -> [a] -> Maybe b
> findApply _ [] = Nothing
> findApply f (h:t) = case f h of
>                       Nothing -> findApply f t
>                       Just x -> Just x

Map with element index as argument

> mapi :: (Int -> a -> b) -> [a] -> [b]
> mapi f = mapi' 0
>   where mapi' _ [] = []
>         mapi' n (h:t) = f n h : mapi' (n+1) t

allPairs f xs ys

returns f applied to all pairs of an element of xs with an element of ys

> allPairs :: (a -> b -> c) -> [a] -> [b] -> [c]
> allPairs f xs ys = [f x y | x <- xs, y <- ys]

> distinctPairs :: [a] -> [(a,a)]
> distinctPairs (x:xs) = 
>   foldr (\y acc -> (x,y) : acc) (distinctPairs xs) xs
> distinctPairs [] = []

all2 f xs ys 

returns true iff the lengths of xs and ys are the same and 
f xi yi --> True for all i < length xs

> all2 :: (a -> b -> Bool) -> [a] -> [b] -> Bool
> all2 _ [] [] = True
> all2 f (x:xs) (y:ys) = f x y && all2 f xs ys
> all2 _ _ _ = False

* Strings

> substringIndex :: String -> String -> Maybe Int 
> substringIndex s1 s2 = 
>   let ind _ [] = Nothing
>       ind n s = if take n s == s1 then Just n else ind (n+1) (tail s) in
>   ind 0 s2

* Substitutions
 
> (↦) :: Ord a => a -> b -> Map a b -> Map a b
> (↦) = Map.insert

> (⟾) :: Ord a => a -> b -> Map a b
> (⟾) = Map.singleton 

