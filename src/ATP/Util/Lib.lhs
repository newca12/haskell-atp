
This file contains utility functions not provided by the Haskell
standard library.  Most mirror functions in Harrison's lib.ml

* Signature

> module ATP.Util.Lib 
>   ( time
>   , pow
>   , funpow
>   , decreasing
>     -- Strings
>   , substringIndex
>     -- Map
>   , (↦)
>   , (⟾)
>   ) 
> where

* Imports

> import Prelude
> import qualified Data.Char as Char
> import qualified Data.List as List
> import qualified Data.Map as Map
> import Data.Map(Map)
> import qualified System.CPUTime as Time
> import qualified Text.Printf as Printf

* Misc

> time :: Show a => IO a -> IO a
> time a = do start <- Time.getCPUTime
>             v <- a
>             end <- Time.getCPUTime
>             let diff :: Double = (fromIntegral (end - start)) / (10E12) 
>             Printf.printf "Computation time: %0.3f sec\n" diff
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
> decreasing f x y = compare (f y) (f x)

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

