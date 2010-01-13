
* Signature 

> module ATP.Test.Combining
>   ( tests )
> where 

* Imports

> import Prelude 
> import qualified ATP.Combining as C
> import qualified ATP.TestFormulas as Forms
> import qualified Data.Maybe as Maybe
> import Test.HUnit(Test(..), (~:), assert)

* Tests

> mkTest :: String -> Test
> mkTest s = s ~: assert $ C.nelopInt (Maybe.fromJust $ Forms.lookup s)

> tests :: Test
> tests = "Combining" ~: TestList $ map mkTest
>   [ "nelop0" 
>   , "nelop1" 
>   , "nelop2"
>   , "nelop3"
>   , "nelop4"
>   , "nelop5"
>   , "nelop6"
>   , "nelop8"
>   , "nelop10"
>   , "nelop12"
>   , "nelop13"
>   , "nelop15"
>   , "nelop17"
>   ]



