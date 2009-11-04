
* Signature

> module ATP.Util.Print.Print
>   ( Pretty(..)
>   , GenPretty(..)
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
>   , render
>   , putStrLn
>   )
>   where

* Imports

> import Prelude hiding (putStrLn)
> import qualified Data.List as List
> import qualified Data.Ratio as Ratio
> import qualified Data.Set as Set
> import Data.Set (Set)
> import qualified System.IO.UTF8 as S
> import qualified Text.PrettyPrint.HughesPJ as PP
> import Text.PrettyPrint.HughesPJ (Doc, (<+>))

* Printing

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

* Modified rendering

FIXME: Trying to make the lines longer doesn't seem to be working at all.

> render :: PP.Doc -> String
> --render = PP.renderStyle (PP.Style PP.LeftMode 1000 1.5)
> render = PP.render

* Type class

> class Pretty a where
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

> prettyShow :: (Pretty a) => a -> String
> prettyShow = PP.render . pPrint

> pPrint0 :: (Pretty a) => PrettyLevel -> a -> Doc
> pPrint0 l = pPrintPrec l 0

> appPrec :: Rational
> appPrec = 10

> putStrLn :: PP.Doc -> IO ()
> putStrLn = S.putStrLn . render

** Instances

> instance Pretty Int where pPrint = PP.int

> instance Pretty Integer where pPrint = PP.integer

> instance Pretty Float where pPrint = PP.float

> instance Pretty Double where pPrint = PP.double

> instance Pretty () where pPrint _ = PP.text "()"

> instance Pretty Bool where pPrint = PP.text . show

> instance Pretty Ordering where pPrint = PP.text . show

> instance Pretty Char where
>     pPrint = PP.char
>     pPrintList _ = PP.text . show

> instance (Pretty a) => Pretty (Maybe a) where
>     pPrintPrec _ _ Nothing = PP.text "Nothing"
>     pPrintPrec l p (Just x) = paren (p > appPrec) $ PP.text "Just" <+> pPrintPrec l (appPrec+1) x

> instance (Pretty a, Pretty b) => Pretty (Either a b) where
>     pPrintPrec l p (Left x) = paren (p > appPrec) $ PP.text "Left" <+> pPrintPrec l (appPrec+1) x
>     pPrintPrec l p (Right x) = paren (p > appPrec) $ PP.text "Right" <+> pPrintPrec l (appPrec+1) x
> 
> instance (Pretty a) => Pretty [a] where
>     pPrintPrec l _ xs = pPrintList l xs
> 
> instance (Pretty a, Pretty b) => Pretty (a, b) where
>     pPrintPrec l _ (a, b) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b]
> 
> instance (Pretty a, Pretty b, Pretty c) => Pretty (a, b, c) where
>     pPrintPrec l _ (a, b, c) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c]
> 
> instance (Pretty a, Pretty b, Pretty c, Pretty d) => Pretty (a, b, c, d) where
>     pPrintPrec l _ (a, b, c, d) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c, pPrint0 l d]
> 
> instance (Pretty a, Pretty b, Pretty c, Pretty d, Pretty e) => Pretty (a, b, c, d, e) where
>     pPrintPrec l _ (a, b, c, d, e) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c, pPrint0 l d, pPrint0 l e]
> 
> instance (Pretty a, Pretty b, Pretty c, Pretty d, Pretty e, Pretty f) => Pretty (a, b, c, d, e, f) where
>     pPrintPrec l _ (a, b, c, d, e, f) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c, pPrint0 l d, pPrint0 l e, pPrint0 l f]
> 
> instance (Pretty a, Pretty b, Pretty c, Pretty d, Pretty e, Pretty f, Pretty g) =>
>          Pretty (a, b, c, d, e, f, g) where
>     pPrintPrec l _ (a, b, c, d, e, f, g) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c, pPrint0 l d, pPrint0 l e, pPrint0 l f, pPrint0 l g]
> 
> instance (Pretty a, Pretty b, Pretty c, Pretty d, Pretty e, Pretty f, Pretty g, Pretty h) =>
>          Pretty (a, b, c, d, e, f, g, h) where
>     pPrintPrec l _ (a, b, c, d, e, f, g, h) =
>         PP.parens $ PP.fsep $ PP.punctuate PP.comma [pPrint0 l a, pPrint0 l b, pPrint0 l c, pPrint0 l d, pPrint0 l e, pPrint0 l f, pPrint0 l g, pPrint0 l h]

> instance Pretty a => Pretty (Set a) where
>   pPrint x = setHoriz $ map pPrint $ Set.toList x

This is needed for proper unicode printing.

> instance Pretty [String] where
>   pPrint = listHoriz . map PP.text 

> class GenPretty s a where
>   pPrintEnv :: s -> a -> Doc

> instance Pretty a => GenPretty () a where
>   pPrintEnv _ = pPrint
