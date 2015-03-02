{-# LANGUAGE DataKinds, EmptyDataDecls, FlexibleInstances, TypeFamilies, 
             TypeSynonymInstances, UndecidableInstances #-}
{-|
  Module:    HaskHOL.Lib.Haskell.Context
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Haskell.Context
    ( HaskellType
    , HaskellCtxt
    , ctxtHaskell
    , haskell
    ) where

import HaskHOL.Core
import HaskHOL.Deductive

import HaskHOL.Lib.Haskell.A.Context
import HaskHOL.Lib.Haskell.Base

extendTheory ctxtHaskellA "Haskell" $
    sequence_ [defMONAD', defRunIdentity']

templateProvers 'ctxtHaskell

-- have to manually write this, for now
type family HaskellCtxt a where
    HaskellCtxt a = (HaskellACtxt a, HaskellContext a ~ True)

type instance PolyTheory HaskellType b = HaskellCtxt b

instance BasicConvs HaskellType where
    basicConvs _ = basicConvs (undefined :: HaskellAType)
