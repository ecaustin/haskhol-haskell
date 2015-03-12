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
    , defEQ
    , defMonad
    , defFunctor
    , defRunIdentity
    , thmMonadIdentity
    , thmMonadMaybe
    , thmFunctorIdentity
    , tacMonadIdentity
    , tacMonadMaybe
    , tacFunctorIdentity
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

defFunctor :: HaskellCtxt thry => HOL cls thry HOLThm
defFunctor = getDefinition "Functor"

defRunIdentity :: HaskellCtxt thry => HOL cls thry HOLThm
defRunIdentity = getRecursiveDefinition "runIdentity"

thmMonadIdentity :: HaskellCtxt thry => HOL cls thry HOLThm
thmMonadIdentity = cacheProof "thmMonadIdentity" ctxtHaskell .
    prove [str| Monad (\\ 'A 'B. \ m k. k (runIdentity m)) Identity |] $
      tacREWRITE [defMonad] `_THEN` tacCONJ `_THENL`
      [ _REPEAT tacGEN_TY `_THEN` tacREWRITE [defIdentity, defRunIdentity]
      , tacCONJ `_THENL`
        [ tacGEN_TY `_THEN` tacMATCH_MP inductionIdentity `_THEN` 
          tacREWRITE [defIdentity, defRunIdentity]
        , _REPEAT tacGEN_TY `_THEN` tacACCEPT thmTRUTH
        ]
      ]

thmMonadMaybe :: HaskellCtxt thry => HOL cls thry HOLThm
thmMonadMaybe = cacheProof "thmMonadMaybe" ctxtHaskell $
    prove [str| Monad 
                  (\\'a 'b. (\ ds k .
                     match ds with Nothing -> Nothing | JustIn x -> k x)) 
                  Just |] tacMonadMaybe

thmFunctorIdentity :: HaskellCtxt thry => HOL cls thry HOLThm
thmFunctorIdentity = cacheProof "thmFunctorIdentity" ctxtHaskell $
    prove [str| Functor (\\ 'a 'b. \ (f:'a -> 'b) id. 
                            Identity [: 'b] (f (runIdentity id))) |]
      tacFunctorIdentity
           

proveConsClass :: (HOLThmRep thm cls thry, MathCtxt thry) 
               => thm -> thm -> [thm] -> Tactic cls thry
proveConsClass consDef indThm thms =
    tacREWRITE [consDef] `_THEN` 
    _REPEAT (_TRY (tacCONJ `_THEN` _REPEAT tacGEN_TY) `_THEN` 
             _TRY (tacMATCH_MP indThm `_ORELSE` 
                   (tacABS_TO_ALL `_THEN` tacMATCH_MP indThm) `_ORELSE`
                   _REPEAT tacGEN) `_THEN` 
             tacREWRITE thms)
  where tacABS_TO_ALL :: BoolCtxt thry => Tactic cls thry
        tacABS_TO_ALL =
            tacABS `_THEN` 
            (\ gl@(Goal _ w) -> let a = head $ frees w in 
                                  tacSPEC (a, a) gl)

tacMonadIdentity :: HaskellCtxt thry => Tactic cls thry
tacMonadIdentity = 
    proveConsClass defMonad inductionIdentity [defIdentity, defRunIdentity]

tacMonadMaybe :: HaskellCtxt thry => Tactic cls thry
tacMonadMaybe = proveConsClass defMonad inductionMaybe [defJust]

tacFunctorIdentity :: HaskellCtxt thry => Tactic cls thry
tacFunctorIdentity =
    proveConsClass defFunctor inductionIdentity 
      [defIdentity, defRunIdentity, defI, defO]
