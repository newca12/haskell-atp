
* Signature 

> module ATP.Util.Monad 
>   ( puts
>   , any
>   , all
>   , findM
>   , ignore
>   ) 
> where

* Imports

> import Prelude hiding (any, all)
> import qualified Control.Monad.State as State
> import Control.Monad.State(MonadState)

* Utils

> puts :: (MonadState s m) => (s -> a -> s) -> a -> m ()
> puts f x = do s <- State.get
>               State.put (f s x)
>               return ()

> any :: Monad m => (a -> m Bool) -> [a] -> m Bool
> any p xs = do bs <- mapM p xs
>               return $ elem True bs

> all :: Monad m => (a -> m Bool) -> [a] -> m Bool
> all p xs = do bs <- mapM p xs
>               return $ not $ elem False bs

> findM :: Monad m => (a -> m Bool) -> [a] -> m (Maybe a)
> findM _p [] = return Nothing
> findM p (x:xs) = do
>   res <- p x
>   if res then return (Just x) else findM p xs

> ignore :: Monad m => m a -> m ()
> ignore x = x >> return ()
