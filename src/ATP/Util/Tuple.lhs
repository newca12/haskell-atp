
* Signature 

> module ATP.Util.Tuple
>   ( map2
>   , map3
>   , map4
>   , map9 
>   , map10
>   )
> where

* Tuples

> map2 :: (a -> b) -> (a, a) -> (b, b)
> map2 f (a1, a2) = (f a1, f a2) 

> map3 :: (a -> b) -> (a, a, a) -> (b, b, b)
> map3 f (a1, a2, a3) = (f a1, f a2, f a3) 

> map4 :: (a -> b) -> (a, a, a, a) -> (b, b, b, b)
> map4 f (a1, a2, a3, a4) = (f a1, f a2, f a3, f a4) 

> map9 :: (a -> b) -> (a, a, a, a, a, a, a, a, a) -> (b, b, b, b, b, b, b, b, b)
> map9 f (a1, a2, a3, a4, a5, a6, a7, a8, a9) = (f a1, f a2, f a3, f a4, f a5, f a6, f a7, f a8, f a9) 

> map10 :: (a -> b) -> (a, a, a, a, a, a, a, a, a, a) -> (b, b, b, b, b, b, b, b, b, b)
> map10 f (a1, a2, a3, a4, a5, a6, a7, a8, a9, a10) = (f a1, f a2, f a3, f a4, f a5, f a6, f a7, f a8, f a9, f a10) 
