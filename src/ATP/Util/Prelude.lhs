
> module ATP.Util.Prelude 
>   ( module Prelude
>   , Impossible(..)
>   , throwImpossible
>   )
> where

Use System.IO.UTF8 for printing

> import Prelude hiding (print, putStr, putStrLn)
> import ATP.Util.Impossible
