
* Signature 

> module ATP.Test.DLO 
>   ( tests )
> where 

* Imports

> import Prelude 
> import qualified Data.Maybe as Maybe
> import qualified Test.HUnit as Test
> import Test.HUnit(Test(..), (~:), assert)

> import ATP.FormulaSyn
> import qualified ATP.DLO as DLO
> import qualified ATP.TestFormulas as Forms

* Tests

> mkTest :: String -> Test
> mkTest s = s ~: assert $ DLO.qelim (Maybe.fromJust (Forms.lookup s)) == (⊤)

> tests :: Test
> tests = "DLO" ~: TestList $ map mkTest
>   [ "dlo" ++ show n | n :: Int <- [1, 2, 5] ]



