module Monad where

import Prelude hiding (Either(..), Monad(..))

data Either a b = Left a | Right b

class Monad m where
    (>>=)       :: m a -> (a -> m b) -> m b
    return      :: a -> m a

instance Monad (Either e) where
    return = Right
    Left l >>= _ = Left l
    Right r >>= k = k r
