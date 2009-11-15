
Gracenotes:
e.g. you can easily define 
newtype MyReader a = MyReader (ReaderT MyEnv IO a) 
  deriving (MonadIO), 
with GeneralizedNewtypeDeriving

* Signature 

> module ATP.Util.Monad 
>   ( module Control.Monad
>   , module Control.Monad.Trans
>   , puts
>   , any
>   , all
>   , partition
>   , zipWith
>   , findM
>   , ignore
>   , ifM
>   , ifM'
>   , maybeM
>   , mapMaybeM
>   , Has(..)
>   , lift2
>   , foldrM
>   ) 
> where

* Imports 

> import ATP.Util.Prelude hiding (any, all, zipWith)
> import qualified Control.Monad.State as State
> import Control.Monad.State
> import Control.Monad
> import Control.Monad.Trans
> import qualified Data.Maybe as Maybe
> import qualified Data.Foldable as Fold

* Classes

> class Has a b where
>   grab :: b -> a
>   stuff :: b -> a -> b

> instance Has a a where
>   grab = id
>   stuff _ x = x

* Monad utils

> partition :: Monad m => (a -> m Bool) -> [a] -> m ([a], [a])
> partition _ [] = return ([], [])
> partition f (x:xs) = do
>   (ys, ns) <- partition f xs
>   b <- f x
>   return $ if b then (x:ys, ns) else (ys, x:ns)

> zipWith :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
> zipWith f xs ys = mapM (uncurry f) (zip xs ys)

> foldrM :: Monad m => (a -> b -> m b) -> b -> [a] -> m b
> foldrM = Fold.foldrM

> maybeM :: Monad m => b -> (a -> b) -> m (Maybe a) -> m b
> maybeM b f x = x >>= return . maybe b f

> mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
> mapMaybeM f xs = mapM f xs >>= return . Maybe.catMaybes

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

> ifM :: Monad m => m Bool -> m a -> m a -> m a
> ifM g x y = do b <- g
>                if b then x else y

> ifM' :: Monad m => m Bool -> a -> a -> m a
> ifM' g x y = do b <- g
>                 if b then return x else return y

> lift2 :: (MonadTrans t1, MonadTrans t2, Monad m, Monad (t2 m)) => m a -> t1 (t2 m) a
> lift2 = lift . lift 
