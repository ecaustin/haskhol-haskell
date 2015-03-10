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
import HERMIT.Plugin hiding (pass)

import HaskHOL.Haskell.Plugin.KURE
import HaskHOL.Haskell.Plugin.Parser
import HaskHOL.Haskell.Plugin.Transform

import HaskHOL.Core
import HaskHOL.Deductive
import HaskHOL.Lib.Haskell
import HaskHOL.Lib.Haskell.Context

import HERMIT.Dictionary.Navigation

import Debug.Trace

plugin :: Plugin
plugin = hermitPlugin $ \ opts -> firstPass $
    do liftIO $ putStrLn "Parsing constant mappings..."
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
           pass x = liftIO $
               do x' <- applyT (replaceType tyMap) ctxt x
                  applyT (replaceTerm tmMap) ctxt x'
           
           trans' :: Bool -> HOLTerm -> HPM HOLTerm
           trans' True (Var name _) =
               pass =<< (at (lookupBind $ unpack name) $ 
                            query trans)
           trans' _ x = pass x
--
       liftIO $ putStrLn "Translating Bind..."
       bnd' <- trans' True bnd
       liftHOL $ printHOL (bnd', typeOf bnd')
--
       liftIO $ putStrLn "Translating Return..."
       ret' <- trans' False ret
       liftHOL $ printHOL ret'
--
       liftIO $ putStrLn "Building Monad Instance..."
       monad <- liftHOL $ mkConstFull "Monad" ([],[],[])
       let tm' = fromJust $ liftM1 mkIComb (mkIComb monad bnd') ret'
       liftHOL $ printHOL (tm', typeOf tm')
       let tm' = fromJust $ 
                   liftM1 mkIComb (mkIComb monad bnd') ret'
--
       liftIO $ putStrLn "Proving..."
       liftHOL $ printHOL =<< 
         prove tm' 
           (proveConsClass defMonad inductionIdentity 
            [defIdentity, defRunIdentity])

lookupBind :: String -> TransformH CoreTC LocalPathH
lookupBind = bindingOfT . cmpString2Var

prepConsts :: String -> HPM (Map Text b) -> HPM [(Text, b)]
prepConsts file mcnsts =
    do cmap <- liftIO $ parse file
       cnsts <- mcnsts
       let cnsts' = catMaybes $ 
                      map (\ (x, y) -> do y' <- mapLookup y cnsts
                                          return (x, y')) cmap
       return (cnsts' ++ mapToList cnsts)

replaceTerm :: [(Text, HOLTerm)] -> TransHOL thry HOLTerm HOLTerm
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
            (tryFind (\ (key, Const name ty') ->
                      if key == i && isJust (typeMatch ty ty' ([], [], []))
                      then mkMConst name ty
                      else fail "") tmmap) 
              <|> (return $! mkVar i ty)

replaceType :: [(Text, TypeOp)] -> TransHOL thry HOLTerm HOLTerm
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
            <+ htyappT (contextfreeT return) repType repTyApp
            <+ hutypeT (contextfreeT return) repType 
                 (\ x -> liftO . mkUType x)
  
        repTyApp :: TypeOp -> [HOLType] -> HOL Proof thry HOLType
        repTyApp op tys = 
            do op' <- repOp
               liftO $! tyApp op' tys
           where repOp :: HOL Proof thry TypeOp
                 repOp =
                     case op of
                       (TyPrimitive i arity)
                           | i == "fun" -> return op
                           | otherwise ->
                               (tryFind (\ (key, op') ->
                                         let (_, arity') = destTypeOp op' in
                                           if key == i && arity' == arity
                                           then return op'
                                           else fail "") tymap)
                                 <|> (return $! mkTypeOpVar i)
                       _ -> return op
                   
-- crude generalization for constructors
mkGenComb :: HOLTerm -> HOLTerm -> HOL cls thry HOLTerm
mkGenComb f arg = (liftO $ mkIComb f arg) <|>
    let (bvs, _) = fromJust . destUTypes $ typeOf f in
      do bvs' <- mapM genVar bvs
         let arg' = fromRight $
                      listMkTyAbs bvs =<< listMkAbs bvs' =<< listMkComb arg bvs'
         liftO $ mkIComb f arg'
