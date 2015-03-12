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
import HERMIT.Dictionary.Navigation
import HERMIT.GHC (Plugin, cmpString2Var)
import HERMIT.Kure
import HERMIT.Plugin hiding (pass)

import HaskHOL.Haskell.Plugin.KURE
import HaskHOL.Haskell.Plugin.Parser
import HaskHOL.Haskell.Plugin.Transform

import HaskHOL.Core
import HaskHOL.Deductive
import HaskHOL.Lib.Haskell.Context

ctxt :: TheoryPath HaskellType
ctxt = ctxtHaskell

liftHOL :: HOL Proof HaskellType a -> HPM a
liftHOL = liftHOL' ctxt

plugin :: Plugin
plugin = hermitPlugin $ \ _ -> firstPass $
    do liftIO $ putStrLn "Parsing configuration files..."
       tyMap <- prepConsts "types.h2h" $ liftHOL types
       tmMap <- prepConsts "terms.h2h" $ liftHOL constants
       opts <- liftIO $ optParse "config.h2h"
       let getOpt :: String -> String -> HPM String
           getOpt lbl err =
             maybe (fail err) return $ lookup lbl opts
--
       liftIO $ putStrLn "Translating from Core to HOL..."
       target <- getOpt "binding" "<binding> not set in config.h2h."
       tm <- at (bindingOfT $ cmpString2Var target) $ query trans
--
       let pass :: HOLTerm -> HPM HOLTerm
           pass x = liftIO $
               do x' <- applyT (replaceType tyMap) ctxt x
                  applyT (replaceTerm tmMap) ctxt x'
       cls <- getOpt "bindingType" "<bindingType> not set in config.h2h."
       tm' <- if cls == "ConsClass" 
              then do cls' <- getOpt "class" "<class> not set in config.h2h."
                      consClassPass cls' tm pass
              else let (bvs, bod) = stripTyAbs tm
                       (bvs', bod') = stripAbs bod in
                     do x <- pass bod'
                        bvs'' <- mapM pass bvs'
                        liftHOL $ flip (foldrM mkTyAll) bvs =<< 
                          listMkForall bvs'' x
--
       liftIO $ putStrLn "Proving..."
       prfType <- getOpt "proofType" "<proofType> not set in config.h2h."
       prfMod <- getOpt "proofModule" "<proofModule> not set in config.h2h."
       prfName <- getOpt "proofName" "<proofName> not set in config.h2h."
       tac <- liftHOL $ if prfType == "HOLThm"
                        then do thm <- runHOLHint prfName [prfMod]
                                return (tacACCEPT (thm::HOLThm))
                        else runHOLHint ("return " ++ prfName) 
                               [prfMod, "HaskHOL.Deductive"]
       liftHOL $ printHOL =<< prove tm' tac

consClassPass :: String -> HOLTerm -> (HOLTerm -> HPM HOLTerm) -> HPM HOLTerm
consClassPass cls tm pass =
    do liftIO $ putStrLn "Translating Arguments..."
       let (_, args) = stripComb tm
       args' <- mapM trans' args
--
       liftIO $ putStrLn "Building Class Instance..."
       monad <- liftHOL $ mkConstFull (pack cls) ([],[],[])
       maybe (fail "Reconstruction of class instance failed.") return $
         foldlM mkIComb monad args'
  where trans' :: HOLTerm -> HPM HOLTerm
        trans' x@(Var name _) = pass =<< query
            (do lp <- lookupBind $ unpack name
                case lp of
                  Nothing -> return x
                  Just res -> localPathT res trans)
        trans' x = pass x

        lookupBind :: String -> TransformH CoreTC (Maybe LocalPathH)
        lookupBind x = catchesT [ liftM Just . bindingOfT $ cmpString2Var x
                                , return Nothing
                                ]

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
                      if key == i && isJust (typeMatch ty' ty ([], [], []))
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
