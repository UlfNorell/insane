
module Utils.Monad where

import Control.Monad

type Cont r a = (a -> r) -> r

thread :: (a -> Cont r b) -> [a] -> Cont r [b]
thread f [] ret = ret []
thread f (x:xs) ret =
    f x		$ \x ->
    thread f xs $ \xs -> ret (x:xs)

