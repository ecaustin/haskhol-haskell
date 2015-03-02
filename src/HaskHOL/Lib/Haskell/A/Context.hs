{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TypeFamilies, 
             TypeSynonymInstances, UndecidableInstances #-}
{-|
  Module:    HaskHOL.Lib.Haskell.A.Context
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Haskell.A.Context
    ( HaskellAType
    , HaskellACtxt
    , ctxtHaskellA
    , haskellA
    ) where

import HaskHOL.Core
import HaskHOL.Deductive
import HaskHOL.Math

import HaskHOL.Lib.Haskell.A.Base

extendTheory ctxtMath "HaskellA" $
    do void tyDefIdentity'
       void defIdentity'

templateProvers 'ctxtHaskellA

-- have to manually write this, for now
type family HaskellACtxt a where
    HaskellACtxt a = (MathCtxt a, HaskellAContext a ~ True)

type instance PolyTheory HaskellAType b = HaskellACtxt b

instance BasicConvs HaskellAType where
    basicConvs _ = basicConvs (undefined :: MathType)
