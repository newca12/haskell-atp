
The front end for the automated theorem proving Haskell port.

* Pragmas 

> {-# OPTIONS_GHC -fno-warn-unused-imports #-}

* Signature

> module Main ( main ) where 

* Imports

> import Prelude 

-- > import qualified List
-- > import qualified System.IO as IO
-- > import Text.Printf(printf)
-- > import qualified Text.PrettyPrint.HughesPJ as PP
-- > import Text.PrettyPrint.HughesPJ( ($+$) ) 
-- > import qualified Control.Exception as Exn

Basics

> import qualified ATP.Util.Lib
> import qualified ATP.Util.ListSet 
> import qualified ATP.Util.Lex
> import qualified ATP.Util.Parse
> import qualified ATP.Util.Print

Intro

> import qualified ATP.IntroSyn
> import qualified ATP.Intro

Formulas 

> import qualified ATP.FormulaSyn
> import qualified ATP.Formula

Propositional logic

> import qualified ATP.Prop 
> import qualified ATP.PropExamples
> import qualified ATP.DefCNF
> import qualified ATP.FOL
> import qualified ATP.DP

First order logic

> import qualified ATP.Skolem
> import qualified ATP.Herbrand
> import qualified ATP.Unif
> import qualified ATP.Tableaux
> import qualified ATP.Resolution
> import qualified ATP.Prolog
> import qualified ATP.Meson
> import qualified ATP.Equal
> import qualified ATP.Cong
> import qualified ATP.Rewrite
> import qualified ATP.Order
> import qualified ATP.Completion
> import qualified ATP.EqElim
> import qualified ATP.Paramodulation
> import qualified ATP.Decidable
> import qualified ATP.Qelim
> import qualified ATP.Cooper

-- > import qualified ATP.Complex
-- > import qualified ATP.Real
-- > import qualified ATP.Grobner
-- > import qualified ATP.Geom

> import qualified ATP.Interpolation
> import qualified ATP.Combining

Tests

> import qualified ATP.TestFormulas

* Main

> main :: IO ()
> main = do putStrLn "Hello World!"
