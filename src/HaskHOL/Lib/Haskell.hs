{-|
  Module:    HaskHOL.Lib.Haskell
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Lib.Haskell
    ( HaskellType
    , HaskellAThry
    , HaskellThry
    , HaskellCtxt
    , tyDefIdentity
    , inductionIdentity
    , recursionIdentity
    , tyDefMaybe
    , inductionMaybe
    , recursionMaybe
    , defIdentity
    , defJust
    , defMonad
    , defRunIdentity
    , thmIdentityMonad
    , proveConsClass
    ) where

import HaskHOL.Core
import HaskHOL.Deductive hiding (getDefinition)
import HaskHOL.Math

import HaskHOL.Lib.Haskell.A
import HaskHOL.Lib.Haskell.Base
import HaskHOL.Lib.Haskell.Context

defMonad :: HaskellCtxt thry => HOL cls thry HOLThm
defMonad = getDefinition "Monad"

defRunIdentity :: HaskellCtxt thry => HOL cls thry HOLThm
defRunIdentity = getRecursiveDefinition "runIdentity"

thmIdentityMonad :: HaskellCtxt thry => HOL cls thry HOLThm
thmIdentityMonad = cacheProof "thmIdentityMonad" ctxtHaskell .
    prove [str| Monad (\\ 'A 'B. \ m k. k (RunIdentity m)) Identity |] $
      tacREWRITE [defMonad] `_THEN` tacCONJ `_THENL`
      [ _REPEAT tacGEN_TY `_THEN` tacREWRITE [defIdentity, defRunIdentity]
      , tacCONJ `_THENL`
        [ tacGEN_TY `_THEN` tacMATCH_MP inductionIdentity `_THEN` 
          tacREWRITE [defIdentity, defRunIdentity]
        , _REPEAT tacGEN_TY `_THEN` tacACCEPT thmTRUTH
        ]
      ]

proveConsClass :: (HOLThmRep thm cls thry, MathCtxt thry) 
               => thm -> thm -> [thm] -> Tactic cls thry
proveConsClass consDef indThm thms =
    tacREWRITE [consDef] `_THEN` 
    _REPEAT (_TRY (tacCONJ `_THEN` _REPEAT tacGEN_TY) `_THEN` 
             _TRY (tacMATCH_MP indThm) `_THEN` 
             tacREWRITE thms)

{-
[str| Monad (\\'a 'b. (\ ds k . match ds with Nothing -> Nothing | JustIn x -> k x)) Just |]

tacREWRITE [defMonad]
(tacCONJ `_THEN` _REPEAT tacGEN_TY)
induction failed `orelse` _REPEAT tacGEN `_THEN`
ty_beta redex goes here
-}
