
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
> import ATP.Util.Parse (parser)
> import qualified Data.Ratio

* Util

> version :: String
> version = "1.0"

> getRational :: String -> Maybe Rational
> getRational = Lex.makeParser' parser

> getInteger :: String -> Maybe Integer
> getInteger i = case getRational i of
>   Nothing -> Nothing
>   Just r -> 
>     if Data.Ratio.denominator r == 1
>     then Just $ Data.Ratio.numerator r
>     else Nothing

> getInt :: String -> Maybe Int
> getInt i = case getRational i of
>   Nothing -> Nothing
>   Just r -> 
>     if Data.Ratio.denominator r == 1
>     then Just $ fromInteger $ Data.Ratio.numerator r
>     else Nothing
