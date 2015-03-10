{-# LANGUAGE OverloadedStrings #-}
{-|
  Module:    HaskHOL.Haskell.Plugin.Transform
  Copyright: (c) The University of Kansas 2013
  LICENSE:   BSD3

  Maintainer:  ecaustin@ittc.ku.edu
  Stability:   unstable
  Portability: unknown
-}
module HaskHOL.Haskell.Plugin.Transform where

import HERMIT.GHC
import HERMIT.Kure

import HaskHOL.Core hiding (put, get)
import qualified HaskHOL.Core as HC

import Control.Monad.State
import qualified Data.Text.Lazy as T

import System.IO.Unsafe
import Debug.Trace
import HaskHOL.Haskell

data HOLSum = Tm HOLTerm | Ty HOLType | TyOp TypeOp

dummy :: TransformH a HOLSum
dummy = return . Tm $ mkVar "a" tyBool

-- Top-level'ish transformations
trans :: TransformH CoreTC HOLTerm
trans = promoteBindT (transform $ \ c -> liftM snd . applyT transBind c)

transBind :: TransformH CoreBind (HOLTerm, HOLTerm)
transBind = nonRecT transVar transExpr (\ (Tm bv) (Tm e) -> (bv, e))

transVar :: TransformH Var HOLSum
transVar = transform $ \ c v ->
    let name = pack . unqualifiedName $ varName v in
      if isTKVar v then return . Ty . fromRight . mkSmall $ mkVarType name
      else do (Ty ty) <- applyT transType c (varType v)
              return . Tm $! mkVar name ty

transExpr :: TransformH CoreExpr HOLSum
transExpr = 
       varT transVar
--    <+ litT undefined
      <+ appT transExpr transExpr transApp
      <+ lamT transVar transExpr transLam
      <+ letT transBind transExpr transLet
      <+ caseT transExpr transVar transType (const transAlt) transCase
--    <+ castT undefined undefined undefined
--    <+ tickT undefined undefined undefined
      <+ typeT transType
--    <+ coercionT undefined

transApp :: HOLSum -> HOLSum -> HOLSum
-- force type applications if we can
transApp (Tm x@(HC.Var name (UType xty@(TyVar _ bname) ty))) y =
    case y of
      TyOp op -> Tm . mkVar name $ typeSubst [(mkTypeOpVar bname, op)] ty
      Ty ty' -> Tm . mkVar name $ typeSubst [(xty, ty')] ty
      Tm y' -> Tm $ mkComb' x y'
transApp (Tm x) (Ty y) = Tm $ mkTyComb' x y
-- erase type class arguments rather crudely
transApp (Tm x@(HC.Var name ty)) (Tm y@(HC.Var cls _))
    | T.take 2 cls == "$d" = 
        let (_, ty') = fromJust $ destFunTy ty in
          Tm $ mkVar name ty'
    | otherwise = Tm $ mkComb' x y
transApp (Tm x) (Tm y) = Tm $ mkComb' x y
transApp _ _ = error "transApp: type-level application at term level."

transLam :: HOLSum -> HOLSum -> HOLSum
transLam (Ty bv) (Tm bod) = Tm . fromRight $ mkTyAbs bv bod
-- erase type class arguments
transLam (Tm bv@(HC.Var name _)) (Tm bod)
    | T.take 2 name == "$d" = Tm bod
    | otherwise = Tm $ mkAbs' bv bod
transLam _ _ = error "transLam: type-level abstraction at term level."

transLet :: (HOLTerm, HOLTerm) -> HOLSum -> HOLSum
transLet (bv@(HC.Var name _), be) (Tm bod)
    -- erase type class arguments
    | T.take 2 name == "$d" = Tm bod
    | otherwise = Tm mkLet'
  where mkLet' :: HOLTerm
        mkLet' =
            let tyLend = mkFunTy' [ty, ty]
                lend = mkComb' (mkVar "LET_END" tyLend) bod
                lbod = mkGabs' bv lend
                tyAbs = typeOf lbod
                (ty1, ty2) = fromJust $ destFunTy tyAbs
                tyLet = mkFunTy' [tyAbs, ty1, ty2] in
              foldl mkComb' (mkVar "LET" tyLet) [lbod, be]
          where ty = typeOf bod

        mkGabs' :: HOLTerm -> HOLTerm -> HOLTerm
        mkGabs' tm1@HC.Var{} tm2 = mkAbs' tm1 tm2
        mkGabs' tm1 tm2 =
            let fTy = mkFunTy' [ty1, ty2]
                fvs = frees tm1
                f = variant (frees tm1 ++ frees tm2) $ mkVar "f" fTy
                bodIn = foldr (mkBinder' "!") (mkGeq' (mkComb' f tm1) tm2) fvs
                tyGabs = mkFunTy' [mkFunTy' [fTy, tyBool], fTy] in
              mkComb' (mkVar "GABS" tyGabs) $ mkAbs' f bodIn
          where ty1 = typeOf tm1
                ty2 = typeOf tm2
transLet _ Ty{} = error "transLet: types not allowed as bodies of let terms."
transLet _ _ = error "transLet: binding must be a variable."

transAlt :: TransformH CoreAlt (Text, [HOLTerm], HOLTerm)
transAlt = altT transAlt' (const transVar) transExpr
             (\ x y z -> (x, map fromTm y, fromTm z))
  where transAlt' :: TransformH AltCon Text
        transAlt' = contextfreeT $ \ ac ->
            case ac of
              DEFAULT -> return "DEFAULT"
              DataAlt dc -> return . pack . unqualifiedName $ dataConName dc
              LitAlt _ -> fail "transAlt: literals are not handled currently."

        fromTm :: HOLSum -> HOLTerm
        fromTm (Tm x) = x
        fromTm _ = error "fromTm"
              
-- The State monad should be at the top level to be correct.
-- Maybe ask drew if the context is extendable with user data, would make it eaasier.
-- Or just change the translation to use a custom context and write a wrapper in the plugin?

instance Show HOLTerm where
    show x = unsafePerformIO $ runHOLProof (showHOL x) ctxtHaskell

instance Show HOLType where
    show x = unsafePerformIO $ runHOLProof (showHOL x) ctxtHaskell

transCase :: HOLSum -> HOLSum -> HOLSum -> [(Text, [HOLTerm], HOLTerm)] 
          -> HOLSum
transCase (Tm match) (Tm asVar) (Ty resTy) alts = flip evalState 0 $
    do alts' <- mapM mkPat alts
       let ty' = mkFunTy' [asTy, resTy, tyBool]
           tmSeq = mkVar "_SEQPATTERN" $ mkFunTy' [ty', ty', ty']
           clauses = foldr1 (\ s t -> mkComb' (mkComb' tmSeq s) t) alts'
           tmMatch = mkVar "_MATCH" $ mkFunTy' [asTy, ty', resTy]
           res = mkComb' (mkComb' tmMatch match) clauses
       return $! Tm res
  where asTy = typeOf asVar

        mkPat :: (Text, [HOLTerm], HOLTerm) -> State Int HOLTerm
        mkPat (con, bvs, res) =        
            do x <- pgenVar asTy
               y <- pgenVar $ typeOf res
               let patTm = mkVar "_UNGUARDED_PATTERN" $ 
                             mkFunTy' [tyBool, tyBool, tyBool]
                   tys = map typeOf bvs
                   conTm = foldr (flip mkComb') 
                             (mkVar con $ mkFunTy' (tys ++ [asTy])) bvs
                   bod = mkComb' (mkComb' patTm (mkGeq' conTm x)) (mkGeq' res y)
               return $! mkAbs' x (mkAbs' y (foldr (mkBinder' "?") bod bvs))

        pgenVar :: HOLType -> State Int HOLTerm
        pgenVar ty =
            do n <- get
               put $ succ n
               return $! mkVar (pack $ "_GENPVAR" ++ show n) ty
transCase _ _ _ _ = error "transCase: expecting terms, got types."

transType :: TransformH Type HOLSum
transType =
         tyVarT transVar
--    <+ litTyT undefined
      <+ appTyT transType transType transOp
      <+ funTyT transType transType 
           (\ (Ty x) (Ty y) -> Ty $ mkFunTy' [x, y])
      <+ forAllTyT transVar transType 
           (\ (Ty x) (Ty y) -> Ty . fromRight $ mkUType x y)
      <+ tyConAppT transTyCon (const transType)
           (\ x ys -> 
              if null ys
              then let (_, n) = destTypeOp x in
                     if n == 0 then Ty $ tyApp' x []
                     else TyOp x
              else Ty . tyApp' x $ map (\ (Ty y) -> y) ys)

transOp :: HOLSum -> HOLSum -> HOLSum
transOp (Ty (TyVar _ x)) (Ty ty) = 
    Ty $ tyApp' (mkTypeOpVar x) [ty]
transOp (Ty (TyApp op tys)) (Ty ty) = 
    Ty . tyApp' op $ tys ++ [ty]
transOp _ _ = error "transOp"

transTyCon :: TransformH TyCon TypeOp
transTyCon = contextfreeT $ \ op ->
    if isFunTyCon op then return tyOpFun
    else let name = pack . unqualifiedName $ tyConName op
             arity = tyConArity op in
           return $! newPrimitiveTypeOp name arity    

-- Utils
tyApp' :: TypeOp -> [HOLType] -> HOLType
tyApp' op = leftToErr . tyApp op

mkFunTy' :: [HOLType] -> HOLType
mkFunTy' = leftToErr . foldr1M (\ ty acc -> tyApp tyOpFun [ty, acc])

mkComb' :: HOLTerm -> HOLTerm -> HOLTerm
mkComb' x = leftToErr . mkComb x

mkTyComb' :: HOLTerm -> HOLType -> HOLTerm
mkTyComb' x = leftToErr . mkTyComb x

mkAbs' :: HOLTerm -> HOLTerm -> HOLTerm
mkAbs' x = leftToErr . mkAbs x

mkGeq' :: HOLTerm -> HOLTerm -> HOLTerm
mkGeq' tm1 tm2 =
    let tmGeq = mkVar "GEQ" $ mkFunTy' [ty, ty, tyBool] in
      mkComb' (mkComb' tmGeq tm1) tm2
  where ty = typeOf tm1

mkBinder' :: Text -> HOLTerm -> HOLTerm -> HOLTerm
mkBinder' op v b =
    let ty = mkFunTy' [mkFunTy' [typeOf v, tyBool], tyBool] in
      mkComb' (mkVar op ty) $ mkAbs' v b

leftToErr :: Either String a -> a
leftToErr (Left s) = error s
leftToErr (Right x) = x
