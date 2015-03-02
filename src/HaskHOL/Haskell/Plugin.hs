{-|
  Module:    HaskHOL.Haskell.Plugin
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Haskell.Plugin
    ( plugin
    ) where

import Control.Monad.State

import HERMIT.Context (LocalPathH)
import HERMIT.GHC (Plugin, cmpString2Var)
import HERMIT.Kure
import HERMIT.Plugin
import HERMIT.Dictionary.Navigation

import HaskHOL.Haskell.Plugin.KURE
import HaskHOL.Haskell.Plugin.Parser
import HaskHOL.Haskell.Plugin.Transform

import HaskHOL.Core
import HaskHOL.Deductive
import HaskHOL.Math
import HaskHOL.Lib.Haskell

import HERMIT.PrettyPrinter.Common	
import HERMIT.PrettyPrinter.AST
import HERMIT.Dictionary.Navigation

plugin :: Plugin
plugin = hermitPlugin $ \ opts -> firstPass $
    do liftIO $ putStrLn "Parsing constant mappings..."
       liftIO $ print opts
       let ctxt = ctxtHaskell
           liftHOL = liftHOL' ctxt
       tyMap <- prepConsts "types.h2h" $ liftHOL types
       tmMap <- prepConsts "terms.h2h" $ liftHOL constants
--
       liftIO $ putStrLn "Translating from Core to HOL..."
       tm <- at (lookupBind "$fMonadIdentity") $ query trans
       let (_, [bnd, ret]) = stripComb tm
--
       let pass :: HOLTerm -> HPM HOLTerm
           pass tm = liftIO $
               do tm' <- applyT (replaceType tyMap) ctxt tm
                  applyT (replaceTerm tmMap) ctxt tm'
           
           trans' :: Bool -> HOLTerm -> HPM HOLTerm
           trans' True (Var name _) =
               pass =<< (at (lookupBind $ unpack name) $ 
                            query trans)
           trans' _ tm = pass tm
--
       liftIO $ putStrLn "Translating Bind..."
       bnd' <- trans' True bnd
--
       liftIO $ putStrLn "Translating Return..."
       ret' <- trans' False ret
--
       liftIO $ putStrLn "Building Monad Instance..."
       monad <- liftHOL $ mkConstFull "MONAD" ([],[],[])
       let tm' = fromJust $ 
                   liftM1 mkIComb (mkIComb monad bnd') ret'
--
       liftIO $ putStrLn "Proving..."
       liftHOL $ printHOL =<< 
         prove tm' 
           (proveConsClass defMONAD inductionIdentity 
            [defIdentity, defRunIdentity])

lookupBind :: String -> TransformH CoreTC LocalPathH
lookupBind = bindingOfT . cmpString2Var

proof :: Tactic Proof MathType
proof = tacMATCH_ACCEPT thmREVERSE_APPEND

prepConsts :: String -> HPM (Map Text b) -> HPM (Map Text b)
prepConsts file mcnsts =
    do cmap <- liftIO $ parse file
       cnsts <- mcnsts
       return . mapFromList . catMaybes $ 
         map (\ (x, y) -> do y' <- mapLookup y cnsts
                             return (x, y')) cmap

replaceTerm :: Map Text HOLTerm -> TransHOL thry HOLTerm HOLTerm
replaceTerm tmmap = repTerm
  where repTerm :: TransHOL thry HOLTerm HOLTerm
        repTerm =
               contextfreeT (\ tm@Const{} -> return tm)
            <+ hcombT repTerm repTerm (\ x -> liftO . mkComb x)
            <+ habsT (contextfreeT return) repTerm (\ x -> liftO . mkAbs x)
            <+ htycombT repTerm (contextfreeT return) (\ x -> liftO . mkTyComb x)
            <+ htyabsT (contextfreeT return) repTerm (\ x -> liftO . mkTyAbs x)
            <+ hvarT (contextfreeT return) (contextfreeT return) repVar
               -- EvNote: has the potential to cause issues if a bound var has
               --         a name shared with a mapped constant

        repVar :: Text -> HOLType -> HOL Proof thry HOLTerm
        repVar i ty =
            do cs <- constants
               case mapLookup i $ cs `mapUnion` tmmap of
                 Just (Const i' _) ->
                     mkMConst i' ty <?> "type mismatch for term constant."
                 _ -> return $! mkVar i ty

replaceType :: Map Text TypeOp -> TransHOL thry HOLTerm HOLTerm
replaceType tymap = repTerm
  where repTerm :: TransHOL thry HOLTerm HOLTerm
        repTerm =
               hvarT (contextfreeT return) repType (\ x -> return . mkVar x)
            <+ contextfreeT (\ tm@Const{} -> return tm)
            <+ hcombT repTerm repTerm (\ x -> liftO . mkComb x)
            <+ habsT repTerm repTerm (\ x -> liftO . mkAbs x)
            <+ htycombT repTerm repType (\ x -> liftO . mkTyComb x)
            <+ htyabsT repType repTerm (\ x -> liftO . mkTyAbs x)

        repType :: TransHOL thry HOLType HOLType
        repType =
               contextfreeT (\ ty@TyVar{} -> return ty)
            <+ htyappT repTyCon repType (\ x -> liftO . tyApp x)
            <+ hutypeT (contextfreeT return) repType 
                 (\ x -> liftO . mkUType x)
  
        repTyCon :: TransHOL thry TypeOp TypeOp
        repTyCon = contextfreeT $ \ e ->
            case e of
              TyPrimitive i arity
                  | i == "fun" -> return e
                  | otherwise ->
                    case mapLookup i tymap of
                      Nothing -> return $! mkTypeOpVar i
                      Just op -> 
                          let (_, arity') = destTypeOp op in
                            if arity == arity' then return op
                            else fail "arity mismatch for type operators."
              _ -> return e

generalize :: TransHOL thry HOLTerm HOLTerm
generalize = genTerm
  where genTerm :: TransHOL thry HOLTerm HOLTerm
        genTerm =
               contextfreeT (\ tm@Var{} -> return tm)
            <+ contextfreeT (\ tm@Const{} -> return tm)
            <+ hcombT genTerm genTerm (\ x -> liftO . mkComb x)
            <+ habsT genTerm genTerm (\ x -> liftO . mkAbs x)
            <+ htycombT genTerm (contextfreeT return)
                 (\ (Var x (UType bv bod)) ty -> return .
                        mkVar x $! typeSubst [(bv, ty)] bod)
            <+ htyabsT (contextfreeT return) genTerm (\ _ x -> return x)
                   
