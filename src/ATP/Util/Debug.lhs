
> module ATP.Util.Debug 
>   ( err
>   , error
>   , trace
>   , trace'
>   , traceIn
>   , traceOut
>   )
> where

> import Prelude hiding (error)
> import qualified Codec.Binary.UTF8.String as UString
> import qualified Debug.Trace as Trace
> import qualified GHC.Err

> import qualified ATP.Util.Print as PP
> import ATP.Util.Print ((<+>))

> error :: PP.Doc -> a
> error = GHC.Err.error . UString.encodeString . PP.render

> trace :: String -> a -> a
> trace s x = Trace.trace (UString.encodeString s) x

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

