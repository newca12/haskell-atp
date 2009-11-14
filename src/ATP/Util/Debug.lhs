
* Signature 

> module ATP.Util.Debug 
>   ( err
>   , assert
>   , impossible
>   , error
>   , trace
>   , trace'
>   , traceIn
>   , traceOut
>   , tracef, tracef'
>   , tracef2, tracef2'
>   , tracef3, tracef3'
>   , tracef4, tracef4'
>   , tracef5, tracef5'
>   , tracef6, tracef6'
>   )
> where

* Imports

> import Prelude hiding (error)
> import qualified ATP.Util.Print as PP
> import ATP.Util.Print (Print, pPrint, (<+>))
> import qualified Codec.Binary.UTF8.String as UString
> import qualified Control.Exception as Exn
> import qualified Debug.Trace as Trace
> import qualified GHC.Err

* Debug

> traceP :: Bool
> traceP = False

> error :: PP.Doc -> a
> error = GHC.Err.error . UString.encodeString . PP.render

> assert :: Bool -> a -> a
> assert = Exn.assert

> trace :: String -> a -> a
> trace s x = if traceP then Trace.trace (UString.encodeString s) x else x

> impossible :: a
> impossible = Exn.assert False undefined

> trace' :: String -> PP.Doc -> a -> a
> trace' name doc x = 
>   let msg = UString.encodeString $ PP.render (PP.text name <+> doc) in
>   if traceP then Trace.trace msg x else x

> traceIn :: String -> PP.Doc -> a -> a
> traceIn name doc x = 
>   let msg = UString.encodeString $ PP.render (PP.text (name ++ "<--") <+> doc) in
>   Trace.trace msg x

> traceOut :: String -> PP.Doc -> a -> a
> traceOut name doc x = 
>   let msg = UString.encodeString $ PP.render (PP.text (name ++ "-->") <+> doc) in
>   Trace.trace msg x

> err :: a
> err = GHC.Err.error "Impossible"

> tracef :: (Print a1, Print a2) => String -> (a1 -> a2) -> (a1 -> a2)
> tracef name f x = 
>   trace' (name ++ " <--") (pPrint x) $
>   let res = f x in
>   trace' (name ++" -->") (pPrint res) res

> tracef' :: (Print a1) => String -> (a1 -> a2) -> (a1 -> a2)
> tracef' name f x = 
>   trace' (name ++ " <--") (pPrint x) $
>   f x

> tracef2 :: (Print a1, Print a2, Print a3) => String -> (a1 -> a2 -> a3) -> (a1 -> a2 -> a3)
> tracef2 name f x y = 
>   trace' (name ++ " <--") (pPrint (x, y)) $
>   let res = f x y in
>   trace' (name ++" -->") (pPrint res) res

> tracef2' :: (Print a1, Print a2) => String -> (a1 -> a2 -> a3) -> (a1 -> a2 -> a3)
> tracef2' name f x y = 
>   trace' (name ++ " <--") (pPrint (x, y)) $
>   f x y

> tracef3 :: (Print a1, Print a2, Print a3, Print a4) => String -> (a1 -> a2 -> a3 -> a4) -> (a1 -> a2 -> a3 -> a4)
> tracef3 name f x y = 
>   trace' (name ++ " <--") (pPrint (x, y)) $
>   let res = f x y in
>   trace' (name ++" -->") (pPrint res) res

> tracef3' :: (Print a1, Print a2, Print a3) => String -> (a1 -> a2 -> a3 -> a4) -> (a1 -> a2 -> a3 -> a4)
> tracef3' name f x y = 
>   trace' (name ++ " <--") (pPrint (x, y)) $
>   f x y 

> tracef4 :: (Print a1, Print a2, Print a3, Print a4, Print a5) => String -> (a1 -> a2 -> a3 -> a4 -> a5) -> (a1 -> a2 -> a3 -> a4 -> a5)
> tracef4 name f x1 x2 x3 x4 = 
>   trace' (name ++ " <--") (pPrint (x1, x2, x3, x4)) $
>   let res = f x1 x2 x3 x4 in
>   trace' (name ++" -->") (pPrint res) res

> tracef4' :: (Print a1, Print a2, Print a3, Print a4) => String -> (a1 -> a2 -> a3 -> a4 -> a5) -> (a1 -> a2 -> a3 -> a4 -> a5)
> tracef4' name f x1 x2 x3 x4 = 
>   trace' (name ++ " <--") (pPrint (x1, x2, x3, x4)) $
>   f x1 x2 x3 x4

> tracef5 :: (Print a1, Print a2, Print a3, Print a4, Print a5, Print a6) => String -> (a1 -> a2 -> a3 -> a4 -> a5 -> a6) -> (a1 -> a2 -> a3 -> a4 -> a5 -> a6)
> tracef5 name f x1 x2 x3 x4 x5 = 
>   trace' (name ++ " <--") (pPrint (x1, x2, x3, x4, x5)) $
>   let res = f x1 x2 x3 x4 x5 in
>   trace' (name ++" -->") (pPrint res) res

> tracef5' :: (Print a1, Print a2, Print a3, Print a4, Print a5) => String -> (a1 -> a2 -> a3 -> a4 -> a5 -> a6) -> (a1 -> a2 -> a3 -> a4 -> a5 -> a6)
> tracef5' name f x1 x2 x3 x4 x5 = 
>   trace' (name ++ " <--") (pPrint (x1, x2, x3, x4, x5)) $
>   f x1 x2 x3 x4 x5

> tracef6 :: (Print a1, Print a2, Print a3, Print a4, Print a5, Print a6, Print a7) => String -> (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7) -> (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7)
> tracef6 name f x1 x2 x3 x4 x5 x6 = 
>   trace' (name ++ " <--") (pPrint (x1, x2, x3, x4, x5, x6)) $
>   let res = f x1 x2 x3 x4 x5 x6 in
>   trace' (name ++" -->") (pPrint res) res

> tracef6' :: (Print a1, Print a2, Print a3, Print a4, Print a5, Print a6) => String -> (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7) -> (a1 -> a2 -> a3 -> a4 -> a5 -> a6 -> a7)
> tracef6' name f x1 x2 x3 x4 x5 x6 = 
>   trace' (name ++ " <--") (pPrint (x1, x2, x3, x4, x5, x6)) $
>   f x1 x2 x3 x4 x5 x6
