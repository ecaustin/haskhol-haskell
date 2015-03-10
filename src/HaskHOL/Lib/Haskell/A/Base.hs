{-|
  Module:    HaskHOL.Lib.Haskell.A.Base
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Haskell.A.Base where

import HaskHOL.Core
import HaskHOL.Math

tyDefIdentity' :: MathCtxt thry => HOL Theory thry (HOLThm, HOLThm)
tyDefIdentity' = defineType [str| Identity = IdentityIn A |]

defIdentity' :: MathCtxt thry => HOL Theory thry HOLThm
defIdentity' = newDefinition "Identity"
    [str| Identity = \\ 'a. \ x:'a. IdentityIn x |]

tyDefMaybe' :: MathCtxt thry => HOL Theory thry (HOLThm, HOLThm)
tyDefMaybe' = defineType [str| Maybe = Nothing | JustIn A |]

defJust' :: MathCtxt thry => HOL Theory thry HOLThm
defJust' = newDefinition "Just"
    [str| Just = \\ 'a. \ x:'a. JustIn x |]
