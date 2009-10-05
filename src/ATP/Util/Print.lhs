
> {-# OPTIONS_GHC -fno-warn-orphans  #-} 

PP.Doc is an orphan instance of Monoid.  Don't warn about it.

> module ATP.Util.Print 
>   ( module Text.PrettyPrint.HughesPJ
>   , module ATP.Util.Print.Print
>   ) 
> where

> import Prelude hiding (print, putStr, putStrLn) 
> import Text.PrettyPrint.HughesPJ
> import ATP.Util.Print.Print hiding (render)
> import Data.Monoid 

> instance Monoid Doc where
>   mempty = empty
>   mappend = ($$)
