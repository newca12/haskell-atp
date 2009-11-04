
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
>   )
> where

* Imports

> import Prelude hiding (error)
> import qualified ATP.Util.Print as PP
> import ATP.Util.Print ((<+>))
> import qualified Codec.Binary.UTF8.String as UString
> import qualified Control.Exception as Exn
> import qualified Debug.Trace as Trace
> import qualified GHC.Err

* Debug

> error :: PP.Doc -> a
> error = GHC.Err.error . UString.encodeString . PP.render

> assert :: Bool -> a -> a
> assert = Exn.assert

> trace :: String -> a -> a
> trace s x = Trace.trace (UString.encodeString s) x

> impossible :: a
> impossible = Exn.assert False undefined

> trace' :: String -> PP.Doc -> a -> a
> trace' name doc x = 
>   let msg = UString.encodeString $ PP.render (PP.text (name ++ ">") <+> doc) in
>   Trace.trace msg x

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

