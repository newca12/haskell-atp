
This file contains utility functions not provided by the Haskell
standard library.  Most mirror functions in Harrison's lib.ml

* Signature

> module ATP.Util.Lib 
>   ( time
>   , timeIO
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
> import qualified Control.Exception as Exn
> import qualified Data.Map as Map
> import Data.Map(Map)
> import qualified System.CPUTime as Time
> import qualified Text.Printf as Printf

* Misc

> timeIO :: Show a => IO a -> IO a
> timeIO a = do 
>   start <- Time.getCPUTime
>   v <- a
>   end <- Time.getCPUTime
>   let diff :: Double = (fromIntegral (end - start)) / (1E12) 
>   _ <- Printf.printf "Computation time: %0.4f sec\n" diff
>   return v

> time :: (a -> b) -> a -> IO b
> time f x = do
>   start <- Time.getCPUTime
>   y <- Exn.evaluate $ f x
>   end <- Time.getCPUTime
>   let diff :: Double = (fromIntegral (end - start)) / (1E12)
>   _ <- Printf.printf "Computation time: %0.4f sec\n" diff
>   return y

-- > fib 0 = 0
-- > fib 1 = 1
-- > fib n = fib (n-1) + fib (n-2

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

