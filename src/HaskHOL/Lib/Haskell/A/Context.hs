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
    , HaskellAThry
    , HaskellACtxt
    , ctxtHaskellA
    , haskellA
    ) where

import HaskHOL.Core
import HaskHOL.Math

import HaskHOL.Lib.Haskell.A.Base

templateTypes ctxtMath "HaskellA"

ctxtHaskellA :: TheoryPath HaskellAType
ctxtHaskellA = extendTheory ctxtMath $(thisModule') $
    do sequence_ [tyDefIdentity', tyDefMaybe', tyDefEither']
       sequence_ [defEQ', defIdentity', defJust']
       sequence_ [defLeft', defRight']

templateProvers 'ctxtHaskellA

-- have to manually write this, for now
type family HaskellACtxt a where
    HaskellACtxt a = (MathCtxt a, HaskellAContext a ~ True)

type instance PolyTheory HaskellAType b = HaskellACtxt b
