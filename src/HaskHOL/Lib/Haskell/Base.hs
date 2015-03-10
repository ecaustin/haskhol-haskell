{-|
  Module:    HaskHOL.Lib.Haskell.Base
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Haskell.Base where

import HaskHOL.Core
import HaskHOL.Math

import HaskHOL.Lib.Haskell.A

tyDefIdentity :: HaskellACtxt thry => HOL cls thry (HOLThm, HOLThm)
tyDefIdentity = getType "Identity"

inductionIdentity :: HaskellACtxt thry => HOL cls thry HOLThm
inductionIdentity = cacheProof "inductionIdentity" ctxtHaskellA $ 
    liftM fst tyDefIdentity

recursionIdentity :: HaskellACtxt thry => HOL cls thry HOLThm
recursionIdentity = cacheProof "recursionIdentity" ctxtHaskellA $ 
    liftM snd tyDefIdentity

tyDefMaybe :: HaskellACtxt thry => HOL cls thry (HOLThm, HOLThm)
tyDefMaybe = getType "Maybe"

inductionMaybe :: HaskellACtxt thry => HOL cls thry HOLThm
inductionMaybe = cacheProof "inductionMaybe" ctxtHaskellA $ 
    liftM fst tyDefMaybe

recursionMaybe :: HaskellACtxt thry => HOL cls thry HOLThm
recursionMaybe = cacheProof "recursionMaybe" ctxtHaskellA $ 
    liftM snd tyDefMaybe

defMonad' :: HaskellACtxt thry => HOL Theory thry HOLThm
defMonad' = newDefinition "Monad"
    [str| Monad (bind : % 'A 'B. 'A _M -> ('A -> 'B _M) -> 'B _M)
                (return : % 'A. 'A -> 'A _M)
          = ((!! 'A 'B. ! (a: 'A) (f:'A -> 'B _M). 
                 bind [: 'A] [: 'B] (return [: 'A] a) f = f a) /\
             (!! 'A. ! (m: 'A _M). 
                 bind m return = m) /\
             (!! 'A 'B 'C. ! (m: 'A _M) (f: 'A -> 'B _M) (g: 'B -> 'C _M).
                 bind (bind m f) g = bind m (\ x. bind (f x) g))) |]

defIdentity :: HaskellACtxt thry => HOL cls thry HOLThm
defIdentity = getDefinition "Identity"

defJust :: HaskellACtxt thry => HOL cls thry HOLThm
defJust = getDefinition "Just"

defRunIdentity' :: HaskellACtxt thry => HOL Theory thry HOLThm
defRunIdentity' = newRecursiveDefinition "runIdentity" recursionIdentity
    [str| runIdentity (IdentityIn x) = x |]
