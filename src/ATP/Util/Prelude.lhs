
* Pragmas

> {-# OPTIONS_GHC -fno-warn-orphans #-} 

* Signature

> module ATP.Util.Prelude 
>   ( module Prelude
>   , Impossible(..)
>   , throwImpossible
>   , (<$>)
>   , error'
>   , first, second
>   , (<>), (<+>)
>   , trace
>   , trace'
>   , tracef, tracef'
>   , tracef2, tracef2'
>   , tracef3, tracef3'
>   , tracef4, tracef4'
>   , tracef5, tracef5'
>   , tracef6, tracef6'
>   , fromJust
>   , pPrint
>   , print
>   , putStr
>   , putStrLn
>   , pp
>   )
> where

* Imports

> import Prelude hiding (print, putStr, putStrLn)
> import ATP.Util.Impossible
> import Control.Applicative ((<$>))
> import Control.Arrow (first, second)
> import qualified ATP.Util.Debug as Debug
> import ATP.Util.Debug ( trace'
>                       , tracef, tracef'
>                       , tracef2, tracef2'
>                       , tracef3, tracef3'
>                       , tracef4, tracef4'
>                       , tracef5, tracef5'
>                       , tracef6, tracef6'
>                       )
> import qualified ATP.Util.Print as Print
> import ATP.Util.Print ((<>), (<+>), Doc, pPrint, Print)
> import Data.Maybe (fromJust)
> import Debug.Trace (trace)
> import System.IO.UTF8 (print, putStr, putStrLn)

* Util

> error' :: Doc -> a
> error' = Debug.error

> pp :: Print a => a -> IO ()
> pp = Print.putStrLn . pPrint

> instance Monad m => Functor m where
>   fmap f x = x >>= return . f
