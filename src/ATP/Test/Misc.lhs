
* Signature 

> module ATP.Test.Misc 
>   ( tests )
> where 

* Imports

> import Prelude 
> import qualified Test.HUnit as Test
> import Test.HUnit(Test(..), (~:))

* Gilmore

> gilmore :: Test
> gilmore = "Gilmore" ~: map mkTest formulas
>   where mkTest (name, f) = name ~: do
>           Herbrand.gilmore (Maybe.fromJust (Forms.lookup name))



* Top

> tests :: Test
> tests = "Misc" ~: TestList 
>   [ gilmore
>   ]
