
* Signature 

> module ATP.Test.Grobner
>   ( tests )
> where 

* Imports

> import Prelude 
> import qualified ATP.Grobner as Grobner
> import qualified ATP.TestFormulas as Forms
> import qualified Data.Maybe as Maybe
> import Test.HUnit(Test(..), (~:), (@=?))

* Tests

> tests :: Test
> tests = "Grobner" ~: map mkTest formulas
>  where 
>   mkTest (name, f) = name ~: 
>     Grobner.decide (Maybe.fromJust $ Forms.lookup name) >>= (f @=?)

> formulas :: [(String, Bool)]
> formulas = 
>   [ ("grob0", True)
>   , ("grob1", False)
>   , ("grob2", True)
>   , ("grob3", True)
>   , ("grob4", False)
>   , ("grob5", True)
>   , ("grob6", True)
>   , ("grob7", True)
>   , ("grob8", True)
>   , ("grob9", True)
>   , ("grob10", True)
>   , ("grob11", True)
>   , ("grob16", True)
>   , ("grob17", True)
>   , ("grob18", True)
>   , ("grob19", True)
>   , ("grob20", True)
>   , ("grob21", True)
>   , ("grob22", True)
>   , ("grob23", True)
>   , ("grob24", True)
>   , ("grob25", True)
>   , ("grob26", False)
>   ]



