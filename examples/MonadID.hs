{-# LANGUAGE ExplicitForAll #-}
module MonadID where

import Prelude hiding (Monad, return, (>>=))

data Identity a = Identity a

runIdentity :: Identity a -> a
runIdentity (Identity a) = a

class Monad m where
    (>>=)       :: forall a b. m a -> (a -> m b) -> m b
    return      :: a -> m a

instance Monad Identity where
    return a = Identity a
    m >>= k  = k (runIdentity m)
