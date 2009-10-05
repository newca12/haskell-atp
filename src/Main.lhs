
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

-- > import qualified FormulaSyn
-- > import qualified Formula

Propositional logic

-- > import qualified Prop 
-- > import qualified PropExamples
-- > import qualified DefCnf
-- > import qualified Fol
-- > import qualified TestFormulas
-- > import qualified Dp
-- > import qualified Herbrand
-- > import qualified Unif
-- > import qualified Skolem
-- > import qualified Tableaux
-- > import qualified Resolution

-- > import qualified Prolog
-- > import qualified Meson
-- > import qualified Equal
-- > import qualified Cong
-- > import qualified Rewrite
-- > import qualified EqElim
-- > import qualified Order()
-- > import qualified Completion()
-- > import qualified Paramodulation
-- > import qualified Decidable
-- > import qualified Qelim
-- > import qualified Cooper
-- > import qualified Complex()
-- > import qualified Interpolation()
-- > import qualified Combining

* Main

> main :: IO ()
> main = do putStrLn "Hello World!"
