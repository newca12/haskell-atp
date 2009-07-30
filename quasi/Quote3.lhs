
> module Quote3 (p, f) where
 
> import qualified Data.Generics as G
> import qualified Language.Haskell.TH as TH
> import qualified Language.Haskell.TH.Quote as Q
> import Language.Haskell.TH.Quote (QuasiQuoter(..))
  
> import qualified Formula3 as F
> import Formula3 (Formula(..), Prop, Fol)

Prop

> quoteFormExpP :: String -> TH.ExpQ
> quoteFormPatP :: String -> TH.PatQ

> prop, p :: QuasiQuoter
> prop = QuasiQuoter quoteFormExpP quoteFormPatP
> p = prop

> quoteFormExpP s = do form <- F.parsePropFormula s
>                      Q.dataToExpQ (const Nothing `G.extQ` antiFormExpP) form

> antiFormExpP :: Formula Prop -> Maybe (TH.Q TH.Exp)

> antiFormExpP (AntiQuote v) = Just $ TH.varE (TH.mkName v)
> antiFormExpP _             = Nothing


> quoteFormPatP s =  do form <- F.parsePropFormula s
>                       Q.dataToPatQ (const Nothing `G.extQ` antiFormPatP) form

> antiFormPatP :: Formula Prop -> Maybe (TH.Q TH.Pat)
> antiFormPatP (AntiQuote v) = Just $ TH.varP  (TH.mkName v)
> antiFormPatP _             = Nothing

Fol

> fol, f :: QuasiQuoter
> fol = QuasiQuoter quoteFormExpF quoteFormPatF
> f = fol

> quoteFormExpF s = do form <- F.parseFolFormula s
>                      Q.dataToExpQ (const Nothing `G.extQ` antiFormExpF) form

> antiFormExpF :: Formula Fol -> Maybe (TH.Q TH.Exp)

> antiFormExpF (AntiQuote v) = Just $ TH.varE (TH.mkName v)
> antiFormExpF _             = Nothing


> quoteFormPatF s =  do form <- F.parseFolFormula s
>                       Q.dataToPatQ (const Nothing `G.extQ` antiFormPatF) form

> antiFormPatF :: Formula Fol -> Maybe (TH.Q TH.Pat)
> antiFormPatF (AntiQuote v) = Just $ TH.varP  (TH.mkName v)
> antiFormPatF _             = Nothing


