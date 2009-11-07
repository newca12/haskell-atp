
* Signature

> module ATP.Util.Misc 
>   ( version 
>   , getInteger
>   , getInt
>   , getRational
>   )
> where

* Imports

> import Prelude 
> import qualified ATP.Util.Lex as Lex
> import qualified ATP.Util.Parse as P
> import ATP.Util.Parse (parser)
> import qualified Data.Char as Char
> import qualified Ratio

* Util

> version :: String
> version = "1.0"

> getRational :: String -> Maybe Rational
> getRational = Lex.makeParser' parser

> getInteger :: String -> Maybe Integer
> getInteger i = case getRational i of
>   Nothing -> Nothing
>   Just r -> 
>     if Ratio.denominator r == 1 
>     then Just $ Ratio.numerator r 
>     else Nothing

> getInt :: String -> Maybe Int
> getInt i = case getRational i of
>   Nothing -> Nothing
>   Just r -> 
>     if Ratio.denominator r == 1 
>     then Just $ fromInteger $ Ratio.numerator r 
>     else Nothing
