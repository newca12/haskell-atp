
* Pragmas

> {-# OPTIONS_GHC -fno-warn-orphans #-} 

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
>   , pPrint
>   )
> where

* Imports

Use System.IO.UTF8 for printing

> import Prelude hiding (print, putStr, putStrLn)
> import ATP.Util.Impossible
> import Control.Applicative ((<$>))
> import qualified ATP.Util.Debug as Debug
> import ATP.Util.Print
> import Data.Maybe (fromJust)
> import Debug.Trace (trace)

* Util

> error' :: Doc -> a
> error' = Debug.error

> trace' :: String -> Doc -> a -> a
> trace' = Debug.trace'

> instance Monad m => Functor m where
>   fmap f x = x >>= return . f
