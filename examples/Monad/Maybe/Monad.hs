{-# LANGUAGE ExplicitForAll #-}
module Monad where

import Prelude hiding (Maybe(..), Monad, return, (>>=))

data Maybe a = Nothing | Just a

class Monad m where
    (>>=)       :: forall a b. m a -> (a -> m b) -> m b
    return      :: a -> m a

instance Monad Maybe where
    return a       = Just a
    Nothing  >>= k = Nothing
    (Just x) >>= k = k x
