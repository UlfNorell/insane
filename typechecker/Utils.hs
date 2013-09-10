
module Utils 
    ( module Utils.Monad
    , on
    ) where

import Utils.Monad

on f g x y = f (g x) (g y)

