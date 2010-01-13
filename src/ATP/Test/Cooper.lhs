
* Signature 

> module ATP.Test.Cooper
>   ( tests )
> where 

* Imports

> import Prelude 
> import qualified ATP.Cooper as Cooper
> import ATP.FormulaSyn
> import qualified ATP.TestFormulas as Forms
> import qualified Data.Maybe as Maybe
> import Test.HUnit(Test(..), (~:), (@=?))

* Tests

> tests :: Test
> tests = "Cooper" ~: map mkTest formulas
>   where mkTest (name, f) = name ~: 
>           f @=? Cooper.integerQelim (Maybe.fromJust (Forms.lookup name)) 

> formulas :: [(String, Formula)]
> formulas = 
>   [ ("pres0", [$form| ⊤ |])
>   , ("pres1", [$form| ⊤ |])
>   , ("pres2", [$form| ⊥ |])
>   , ("pres3", [$form| ⊤ |])
>   , ("pres5", [$form| ⊤ |])
>   , ("pres6", [$form| ⊥ |])
>   , ("pres8", [$form| ⊥ |])
>   , ("pres10", [$form| ⊤ |])
>   , ("pres11", [$form| ⊤ |])
>   , ("pres12", [$form| ⊤ |])
>   , ("pres15", [$form| ⊥ |])
>   , ("pres17", [$form| ⊥ |])
>   , ("pres18", [$form| ⊤ |])
>   , ("pres19", [$form| ⊥ |])
>   , ("pres20", [$form| ⊥ |])
>   , ("pres21", [$form| ⊤ |])
>   , ("pres22", [$form| ⊥ |])
>   , ("pres23", [$form| ⊤ |])
>   , ("pres24", [$form| ⊤ |])
>   , ("pres25", [$form| ⊤ |])
>   , ("pres26", [$form| ⊤ |])
>   , ("pres27", [$form| ⊥ |])
>   , ("pres28", [$form| ⊥ |])
>   , ("pres29", [$form| ⊤ |])
>   , ("pres30", [$form| ⊤ |])
>   , ("pres31", [$form| ⊥ |])
>   , ("pres32", [$form| ⊤ |])
>   , ("pres34", [$form| ⊤ |])
>   , ("pres35", [$form| ⊥ |])
>   , ("pres36", [$form| ⊤ |])
>   , ("pres37", [$form| ⊤ |])
>   , ("pres38", [$form| ⊤ |])
>   , ("pres39", [$form| ⊥ |])
>   , ("pres41", [$form| ⊤ |])
>   , ("pres42", [$form| ⊥ |])
>   , ("pres43", [$form| ⊥ |])
>   , ("pres45", [$form| ⊤ |])
>   , ("pres46", [$form| ⊤ |])
>   , ("pres51", [$form| ⊤ |])
>   , ("pres53", [$form| ⊤ |])
>   , ("pres54", [$form| ⊤ |])
>   , ("pres55", [$form| ⊤ |])
>   , ("pres56", [$form| ⊤ |])
>   ]



