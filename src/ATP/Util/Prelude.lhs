
* Signature

> module ATP.Util.Prelude 
>   ( module Prelude
>   , Impossible(..)
>   , throwImpossible
>   , (<$>)
>   , error'
>   , (<>), (<+>)
>   , trace
>   , trace'
>   , fromJust
>   )
> where

* Imports

Use System.IO.UTF8 for printing

> import Prelude hiding (print, putStr, putStrLn)
> import ATP.Util.Impossible
> import Control.Applicative ((<$>))
> import qualified ATP.Util.Debug as Debug
> import ATP.Util.Print as PP
> import Data.Maybe (fromJust)
> import Debug.Trace (trace)

* Util

> error' :: PP.Doc -> a
> error' = Debug.error

> trace' :: String -> PP.Doc -> a -> a
> trace' = Debug.trace'

