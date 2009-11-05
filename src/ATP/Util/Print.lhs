
* Pragmas

> {-# OPTIONS_GHC -fno-warn-orphans  #-} 

PP.Doc is an orphan instance of Monoid.  Don't warn about it.

* Signature

> module ATP.Util.Print 
>   ( module Text.PrettyPrint.HughesPJ
>   , module ATP.Util.Print.Print
>   ) 
> where

* Imports

> import Prelude hiding (print, putStr, putStrLn) 
> import Text.PrettyPrint.HughesPJ hiding (render)
> import ATP.Util.Print.Print 
> --import Data.Monoid 

* Util

-- > instance Monoid Doc where
-- >   mempty = empty
-- >   mappend = ($$)
