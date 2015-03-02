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
import HaskHOL.Deductive hiding (newDefinition)
import HaskHOL.Math

tyDefIdentity' :: (BasicConvs thry, MathCtxt thry) 
            => HOL Theory thry (HOLThm, HOLThm)
tyDefIdentity' = defineType [str| Identity = ID A |]

defIdentity' :: (BasicConvs thry, MathCtxt thry) => HOL Theory thry HOLThm
defIdentity' = newDefinition "Identity"
    [str| Identity = \\ 'a. \ x:'a. ID x |]
