{-# LANGUAGE ConstraintKinds, TemplateHaskell #-}
module List where

import Test.QuickCheck

import HaskHOL.Core
import HaskHOL.Deductive
import HaskHOL.Math

-- Plumbing
myrev :: [a] -> [a]
myrev [] = []
myrev (x:xs) = myrev xs `myapp` [x]

myapp :: [a] -> [a] -> [a]
myapp [] ys = ys
myapp (x:xs) ys = x : myapp xs ys

class MyEq a where
  myeq :: a -> a -> Bool

instance MyEq a => MyEq [a] where
  myeq [] [] = True
  myeq (x:xs) (y:ys)
      | x `myeq` y = myeq xs ys
      | otherwise = False
  myeq _ _ = False

instance MyEq Bool where
  myeq True True = True
  myeq False False = True
  myeq _ _ = False

-- Property, proof, and test
prop :: MyEq a => [a] -> [a] -> Bool
prop xs ys = (myrev (xs `myapp` ys)) `myeq` (myrev ys `myapp` myrev xs)

proof :: ListsCtxt thry => Tactic Proof thry
proof = tacMATCH_ACCEPT thmREVERSE_APPEND

return []
main = $quickCheckAll
