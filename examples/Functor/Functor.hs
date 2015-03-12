module Functor where

import Prelude hiding (Functor, fmap)

data Identity a = Identity a

runIdentity :: Identity a -> a
runIdentity (Identity a) = a

class Functor f where
    fmap :: (a -> b) -> f a -> f b

instance Functor Identity where
    fmap f id = Identity (f (runIdentity id))
