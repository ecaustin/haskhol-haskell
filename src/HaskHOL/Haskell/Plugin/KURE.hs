{-|
  Module:    HaskHOL.Haskell.Plugin.KURE
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Haskell.Plugin.KURE where

import HaskHOL.Core

import HERMIT.Kure
import HERMIT.Plugin.Types

import Control.Monad.Trans


type TransHOL thry a b = Transform (TheoryPath thry) PluginM a b

liftHOL' :: TheoryPath thry -> HOL Proof thry a -> PluginM a
liftHOL' ctxt x = lift (runHOLProof True x ctxt)

htyvarT :: TransHOL thry Bool a -> TransHOL thry Text b
        -> (a -> b -> HOL Proof thry c) -> TransHOL thry HOLType c
htyvarT fl i f = transform $ \ c e ->
    case e of
      TyVar b t -> do b' <- applyT fl c b
                      t' <- applyT i c t
                      liftHOL' c $! f b' t'
      _ -> fail "not a type variable."

htyappT :: TransHOL thry TypeOp a -> TransHOL thry HOLType b
        -> (a -> [b] -> HOL Proof thry c) -> TransHOL thry HOLType c
htyappT op ty f = transform $ \ c e ->
    case e of
      TyApp o tys -> do o' <- applyT op c o
                        tys' <- mapM (applyT ty c) tys
                        liftHOL' c $! f o' tys'
      _ -> fail "not a type level application."

hutypeT :: TransHOL thry HOLType a -> TransHOL thry HOLType b
        -> (a -> b -> HOL Proof thry c) -> TransHOL thry HOLType c
hutypeT t1 t2 f = transform $ \ c e ->
    case e of
      UType bv bod -> do bv' <- applyT t1 c bv
                         bod' <- applyT t2 c bod
                         liftHOL' c $! f bv' bod'
      _ -> fail "not a type quantification."

hvarT :: TransHOL thry Text a -> TransHOL thry HOLType b
      -> (a -> b -> HOL Proof thry c) -> TransHOL thry HOLTerm c
hvarT i ty f = transform $ \ c e ->
    case e of
      Var v t -> do v' <- applyT i c v 
                    t' <- applyT ty c t
                    liftHOL' c $! f v' t'
      _ -> fail "not a variable."

hconstT :: TransHOL thry Text a -> TransHOL thry HOLType b
        -> (a -> b -> HOL Proof thry c) -> TransHOL thry HOLTerm c
hconstT i ty f = transform $ \ c e ->
    case e of
      Const v t -> do v' <- applyT i c v 
                      t' <- applyT ty c t
                      liftHOL' c $! f v' t'
      _ -> fail "not a constant."

hcombT :: TransHOL thry HOLTerm a -> TransHOL thry HOLTerm b
       -> (a -> b -> HOL Proof thry c) -> TransHOL thry HOLTerm c
hcombT t1 t2 f = transform $ \ c e ->
    case e of
      Comb e1 e2 -> do e1' <- applyT t1 c e1
                       e2' <- applyT t2 c e2
                       liftHOL' c $! f e1' e2'
      _ -> fail "not an application."

habsT :: TransHOL thry HOLTerm a -> TransHOL thry HOLTerm b
      -> (a -> b -> HOL Proof thry c) -> TransHOL thry HOLTerm c
habsT t1 t2 f = transform $ \ c e ->
    case e of
      Abs bv bod -> do bv' <- applyT t1 c bv 
                       bod' <- applyT t2 c bod
                       liftHOL' c $! f bv' bod'
      _ -> fail "not an abstraction."

htycombT :: TransHOL thry HOLTerm a -> TransHOL thry HOLType b
         -> (a -> b -> HOL Proof thry c) -> TransHOL thry HOLTerm c
htycombT t1 t2 f = transform $ \ c e ->
    case e of
      TyComb tm ty -> do tm' <- applyT t1 c tm 
                         ty' <- applyT t2 c ty
                         liftHOL' c $! f tm' ty'
      _ -> fail "not a type abstraction."

htyabsT :: TransHOL thry HOLType a -> TransHOL thry HOLTerm b
        -> (a -> b -> HOL Proof thry c) -> TransHOL thry HOLTerm c
htyabsT t1 t2 f = transform $ \ c e ->
    case e of
      TyAbs ty tm -> do ty' <- applyT t1 c ty 
                        tm' <- applyT t2 c tm
                        liftHOL' c $! f ty' tm'
      _ -> fail "not an type abstraction."
