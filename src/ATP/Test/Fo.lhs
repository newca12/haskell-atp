
* Signature 

> module ATP.Test.Fo
>   ( tests )
> where

* Imports

> import ATP.Util.Prelude
> import ATP.FormulaSyn
> import qualified ATP.Herbrand as Herbrand
> import qualified ATP.Meson as Meson
> import qualified ATP.Resolution as Resolution
> import qualified ATP.Tableaux as Tableaux
> import Test.HUnit(Test(..), (~:))

* HUnit

> forms :: [(String, Formula)]
> forms = 
>   [ ("f1", [$form| p ⊃ p |])
>   , ("f2", [$form| p ∧ q ⊃ q ∧ p |])
>   , ("f4", [$form| ⊤ |])
>   , ("f5", [$form| p ⇔ p |])
>   , ("f7", [$form| ((⊤ ∨ (⊤ ⇔ ⊥)) ∧ (p5 ∨ ⊤ ⊃ ⊥ ⊃ p0)) ∧ ((⊤ ⇔ ⊥) ∧ (p10 ⇔ ⊥) ⊃ ¬(p10 ∨ ⊤)) |])
>   , ("f8", [$form| (⊤ ⊃ ⊥) ⊃ ⊥ |])
>   , ("f9", [$form| (⊤ ⇔ ⊥) ⊃ ⊥ |])
>   , ("f10", [$form| (((⊤ ⇔ ⊤) ⊃ ¬⊥) ⊃ ¬(⊤ ∨ ⊥ ∧ ⊤)) ∨ ((⊥ ⊃ p5 ⇔ ¬(p7)) ⊃ ((⊥ ⇔ ⊤) ⇔ ⊥ ⇔ ⊤)) ∨ (⊤ ∨ ⊥ ⊃ (⊥ ⊃ ⊥ ⇔ p5 ∨ ⊥)) |])
>   ]

> mkTest :: String -> (Formula -> IO ()) -> Test
> mkTest name p = name ~: TestList $ map fn forms
>  where
>   fn (s, f) = s ~: p f >> return ()

> ignore :: a -> () 
> ignore = const ()

> tests :: Test
> tests = "Fo" ~: [ mkTest "gilmore" (fmap ignore . Herbrand.gilmore)
>                 , mkTest "davisputnam" (fmap ignore . Herbrand.davisputnam)
>                 , mkTest "davisputnam'" (fmap ignore . Herbrand.davisputnam')
>                 , mkTest "prawitz" (return . ignore . Tableaux.prawitz)
>                 , mkTest "tab" (fmap ignore . Tableaux.tab)
>                 , mkTest "splittab" (fmap ignore . Tableaux.splittab)
>                 , mkTest "basicResolution" (fmap ignore . Resolution.basicResolution)
>                 , mkTest "resolution" (fmap ignore . Resolution.resolution)
>                 , mkTest "positiveResolution" (fmap ignore . Resolution.positiveResolution)
>                 , mkTest "sosResolution" (fmap ignore . Resolution.sosResolution)
>                 , mkTest "basicMeson" (fmap ignore . Meson.basicMeson)
>                 , mkTest "meson" (fmap ignore . Meson.meson)
>                 ]
>                   
