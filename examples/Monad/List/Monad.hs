module Monad where

import Prelude hiding (Monad, return, (>>=))


class Monad m where
    (>>=)       :: m a -> (a -> m b) -> m b
    return      :: a -> m a

instance Monad [] where
    return a       = [a]
    m >>= xs = concatMap xs m
