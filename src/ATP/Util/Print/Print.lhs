
* Signature

> module ATP.Util.Print.Print
>   ( Print(..)
>   , GenPrint(..)
>   , prettyShow
>   , paren
>   , commas
>   , list
>   , listVert
>   , listHoriz
>   , tuple
>   , tupleVert
>   , tupleHoriz
>   , set
>   , setVert
>   , setHoriz
>   , putStrLn
>   , dot
>   )
> where

* Imports

> import Prelude hiding (putStrLn)
> import qualified System.IO.UTF8 as S
> import qualified Data.List as List
> import qualified Data.Set as Set
> import Data.Set (Set)
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Text.PrettyPrint.HughesPJ (Doc, (<+>))
> import qualified Data.Ratio as Ratio

* Printing

> dot :: PP.Doc
> dot = PP.text "."

> paren :: Bool -> PP.Doc -> PP.Doc
> paren False = id
> paren True = PP.parens

> commas :: [PP.Doc] -> [PP.Doc]
> commas = PP.punctuate (PP.text ", ")

> list :: [PP.Doc] -> PP.Doc
> list = PP.brackets . PP.fcat . commas

> listVert :: [PP.Doc] -> PP.Doc
> listVert = PP.brackets . PP.vcat . commas

> listHoriz :: [PP.Doc] -> PP.Doc
> listHoriz = PP.brackets . PP.hcat . commas

> tuple :: [PP.Doc] -> PP.Doc
> tuple = PP.parens . PP.fcat . commas

> tupleVert :: [PP.Doc] -> PP.Doc
> tupleVert = PP.parens . PP.vcat . commas

> tupleHoriz :: [PP.Doc] -> PP.Doc
> tupleHoriz = PP.parens . PP.hcat . commas

> set :: [PP.Doc] -> PP.Doc
> set = PP.braces . PP.fcat . commas

> setVert :: [PP.Doc] -> PP.Doc
> setVert = PP.braces . PP.vcat . commas

> setHoriz :: [PP.Doc] -> PP.Doc
> setHoriz = PP.braces . PP.hcat . commas

* Type class

> class Print a where
>   pPrintPrec :: PrettyLevel -> Rational -> a -> Doc
>   pPrint :: a -> Doc
>   pPrintList :: PrettyLevel -> [a] -> Doc
> 
>   pPrintPrec _ _ = pPrint
>   pPrint = pPrintPrec prettyNormal 0
>   pPrintList l = PP.brackets . PP.fsep . PP.punctuate PP.comma
>                    . map (pPrintPrec l 0)

> newtype PrettyLevel = PrettyLevel Int
>     deriving (Eq, Ord, Show)

> prettyNormal :: PrettyLevel
> prettyNormal = PrettyLevel 0

> prettyShow :: Print a => a -> String
> prettyShow = PP.render . pPrint

> pPrint0 :: Print a => PrettyLevel -> a -> Doc
> pPrint0 l = pPrintPrec l 0

> appPrec :: Rational
> appPrec = 10

> putStrLn :: PP.Doc -> IO ()
> putStrLn = S.putStrLn . PP.render

** Instances

> instance Print Int where 
>   pPrint = PP.int

> instance Print Integer where 
>   pPrint = PP.integer

> instance Print Float where 
>   pPrint = PP.float

> instance Print Double where 
>   pPrint = PP.double

> instance Print (a -> b) where 
>   pPrint _ = PP.text "<fun>"

> instance Print () where 
>   pPrint _ = PP.text "()"

> instance Print Bool where 
>   pPrint = PP.text . show

> instance Print Ordering where 
>   pPrint = PP.text . show

> instance Print Char where
>     pPrint = PP.char
>     pPrintList _ = PP.text . show

> instance Print Rational where
>     pPrint n = if Ratio.denominator n == 1 then pPrint $ Ratio.numerator n
>                else PP.text $ show n

> instance (Print a) => Print (Maybe a) where
>     pPrintPrec _ _ Nothing = PP.text "Nothing"
>     pPrintPrec l p (Just x) = paren (p > appPrec) $ PP.text "Just" <+> pPrintPrec l (appPrec+1) x

> instance (Print a, Print b) => Print (Either a b) where
>     pPrintPrec l p (Left x) = paren (p > appPrec) $ PP.text "Left" <+> pPrintPrec l (appPrec+1) x
>     pPrintPrec l p (Right x) = paren (p > appPrec) $ PP.text "Right" <+> pPrintPrec l (appPrec+1) x
> 
> instance (Print a) => Print [a] where
>     pPrintPrec l _ xs = pPrintList l xs
> 
> instance (Print a, Print b) => Print (a, b) where
>     pPrintPrec l _ (a, b) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b]
> 
> instance (Print a, Print b, Print c) => Print (a, b, c) where
>     pPrintPrec l _ (a, b, c) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c]
> 
> instance (Print a, Print b, Print c, Print d) => Print (a, b, c, d) where
>     pPrintPrec l _ (a, b, c, d) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c, pPrint0 l d]
> 
> instance (Print a, Print b, Print c, Print d, Print e) => Print (a, b, c, d, e) where
>     pPrintPrec l _ (a, b, c, d, e) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c, pPrint0 l d, pPrint0 l e]
> 
> instance (Print a, Print b, Print c, Print d, Print e, Print f) => Print (a, b, c, d, e, f) where
>     pPrintPrec l _ (a, b, c, d, e, f) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c, pPrint0 l d, pPrint0 l e, pPrint0 l f]
> 
> instance (Print a, Print b, Print c, Print d, Print e, Print f, Print g) =>
>          Print (a, b, c, d, e, f, g) where
>     pPrintPrec l _ (a, b, c, d, e, f, g) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c, pPrint0 l d, pPrint0 l e, pPrint0 l f, pPrint0 l g]
> 
> instance (Print a, Print b, Print c, Print d, Print e, Print f, Print g, Print h) =>
>          Print (a, b, c, d, e, f, g, h) where
>     pPrintPrec l _ (a, b, c, d, e, f, g, h) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c, pPrint0 l d, pPrint0 l e, pPrint0 l f, pPrint0 l g, pPrint0 l h]

> instance Print a => Print (Set a) where
>   pPrint x = setHoriz $ map pPrint $ Set.toList x

This is needed for proper unicode printing.

> instance Print [String] where
>   pPrint = listHoriz . map PP.text 

> class GenPrint s a where
>   pPrintEnv :: s -> a -> Doc

> instance Print a => GenPrint () a where
>   pPrintEnv _ = pPrint
