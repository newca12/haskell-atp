
* Signature

> module ATP.Util.Parse.Parse
>   ( Parse(..)
>   , tuple
>   , list
>   , commas
>   , braces
>   )
> where

* Imports

> import Prelude 
> import qualified ATP.Util.Lex as Lex
> import Data.Ratio ((%))
> import qualified Data.Set as Set
> import Data.Set (Set)
> import qualified Text.ParserCombinators.Parsec as P
> import Text.ParserCombinators.Parsec (Parser, (<|>))

* Utils

> class Parse a where
>   parser :: Parser a
>   parse :: String -> a
>   parse = Lex.makeParser parser
>   parseFile :: String -> IO a
>   parseFile = Lex.makeFileParser parser

> commas :: Parser a -> Parser [a]
> commas p = P.sepBy p Lex.comma

> tuple :: Parser a -> Parser [a]
> tuple = Lex.parens . commas

> list :: Parser a -> Parser [a]
> list = Lex.brackets . commas

> braces :: Parser a -> Parser [a]
> braces = Lex.braces . commas 

> brackets :: Parser a -> Parser [a]
> brackets = Lex.brackets . commas 

> instance Parse Bool where
>   parser = (Lex.reserved "True" >> return True)
>        <|> (Lex.reserved "False" >> return False)

> instance Parse Int where
>   parser = Lex.int

> instance Parse Integer where
>   parser = Lex.integer

> instance Parse Rational where
>   parser = rational

> rational :: Parser Rational
> rational = do x :: Integer <- integ
>               y <- P.option 1 $ do 
>                     Lex.reserved "%"
>                     integ
>               return $ x % y
>   where integ = Lex.integer <|> Lex.parens Lex.integer

> instance (Ord a, Parse a) => Parse (Set a) where
>   parser = braces parser >>= return . Set.fromList

> instance Parse a => Parse [a] where
>   parser = brackets parser

> instance (Parse a, Parse b) => Parse (a, b) where
>   parser = Lex.parens parser'
>     where parser' :: Parser (a, b)
>           parser' = do a <- parser
>                        Lex.comma
>                        b <- parser
>                        return (a, b)

> instance (Parse a, Parse b, Parse c) => Parse (a, b, c) where
>   parser = Lex.parens parser'
>     where parser' :: Parser (a, b, c)
>           parser' = do a <- parser
>                        Lex.comma
>                        b <- parser
>                        Lex.comma
>                        c <- parser
>                        return (a, b, c)

> instance (Parse a, Parse b, Parse c, Parse d) => Parse (a, b, c, d) where
>   parser = Lex.parens parser'
>     where parser' :: Parser (a, b, c, d)
>           parser' = do a <- parser
>                        Lex.comma
>                        b <- parser
>                        Lex.comma
>                        c <- parser
>                        Lex.comma
>                        d <- parser
>                        return (a, b, c, d)

> instance (Parse a, Parse b, Parse c, Parse d, Parse e) => Parse (a, b, c, d, e) where
>   parser = Lex.parens parser'
>     where parser' :: Parser (a, b, c, d, e)
>           parser' = do a <- parser
>                        Lex.comma
>                        b <- parser
>                        Lex.comma
>                        c <- parser
>                        Lex.comma
>                        d <- parser
>                        Lex.comma
>                        e <- parser
>                        return (a, b, c, d, e)

> instance (Parse a, Parse b, Parse c, Parse d, Parse e, Parse f) => Parse (a, b, c, d, e, f) where
>   parser = Lex.parens parser'
>     where parser' :: Parser (a, b, c, d, e, f)
>           parser' = do a <- parser
>                        Lex.comma
>                        b <- parser
>                        Lex.comma
>                        c <- parser
>                        Lex.comma
>                        d <- parser
>                        Lex.comma
>                        e <- parser
>                        Lex.comma
>                        f <- parser
>                        return (a, b, c, d, e, f)
