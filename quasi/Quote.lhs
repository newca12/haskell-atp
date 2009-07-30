
> module Quote (formula, f) where
 
> import qualified Data.Generics as G
> import qualified Language.Haskell.TH as TH
> import qualified Language.Haskell.TH.Quote as Q
> import Language.Haskell.TH.Quote (QuasiQuoter(..))
  
> import qualified Formula as F
> import Formula (Formula(..))

> quoteFormExp :: String -> TH.ExpQ
> quoteFormPat :: String -> TH.PatQ

> formula :: QuasiQuoter
> formula = QuasiQuoter quoteFormExp quoteFormPat

> f = formula

> quoteFormExp s = do form <- F.parse s
>                     Q.dataToExpQ (const Nothing `G.extQ` antiFormExp) form

> antiFormExp :: Formula -> Maybe (TH.Q TH.Exp)
> antiFormExp (AntiQuote v) = Just $ TH.varE (TH.mkName v)
> antiFormExp _             = Nothing

> quoteFormPat s =  do form <- F.parse s
>                      Q.dataToPatQ (const Nothing `G.extQ` antiFormPat) form

> antiFormPat :: Formula -> Maybe (TH.Q TH.Pat)
> antiFormPat (AntiQuote v) = Just $ TH.varP  (TH.mkName v)
> antiFormPat _             = Nothing


