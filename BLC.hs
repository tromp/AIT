-- Purpose: compile Haskell to BLC using ghc.
--
-- This code works as a ghc plugin:
-- # ghc --make -dynamic -c BLC.hs -package ghc
-- # ghc -dynamic -c -fplugin=BLC Sample.hs
--
-- The main function is called `mainLC`, and all types and definitions
-- used by it must be defined in the same file.
--
-- Author: Bertram Felgenhauer <int-e@gmx.de>

{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ViewPatterns #-}

module BLC (plugin) where

import GhcPlugins hiding (mkLet)
import TyCon
import DataCon
import FastString (fsLit)
import Name (mkSystemVarName)
import Unique
import UniqDSet
import Data.List
import Control.Monad
import qualified AIT
import Lambda (DB (..))
import qualified Data.Map as M
import qualified Data.Set as S

mainLCName :: String
mainLCName = "mainLC"

plugin :: Plugin
plugin = defaultPlugin{ installCoreToDos = install }

install :: [CommandLineOption] -> [CoreToDo] -> CoreM [CoreToDo]
install _ todo = do
    return (todo ++ [CoreDoPluginPass "generate BLC" pass])

type FlatCoreProgram = [(CoreBndr, CoreExpr)]

pass :: ModGuts -> CoreM ModGuts
pass mg = do
    let !types = summarize (mg_tcs mg)
        !binds = mg_binds mg
        !flatBinds = do
            b <- binds
            case b of
                NonRec b e -> [(b,e)]
                Rec bs     -> bs
        !main = filter ((mainLCName ==) . getOccString) $ map fst flatBinds
    case main of
        [getName -> nm] -> do
            let binds' = prune nm binds flatBinds
                code = AIT.optimize $ codeGen types nm binds'
            liftIO $ putStrLn (show code)
            liftIO $ putStrLn (AIT.encode code)
            liftIO $ putStrLn "Ok."
        _ -> liftIO $ putStrLn "Oops, not exactly one mainLC function."
    return mg

data MyCon = MyCon{ conI :: !Int, conW :: !Int, conA :: !Int, conNs :: [String] }
type MyTypes = M.Map String MyCon

summarize :: [TyCon] -> MyTypes
summarize = M.fromList . (>>= go) where
    go tc
        | isAlgTyCon tc = do
            let cs = reverse (visibleDataCons (algTyConRhs tc))
                ns = map getOccString cs
            (c, i) <- zip cs [0..]
            return (getOccString c, MyCon{ conI = i, conW = length cs, conA = dataConSourceArity c, conNs = ns })
        | otherwise = []

prune :: Name -> CoreProgram -> FlatCoreProgram -> CoreProgram
prune nm bs bs' = filter check bs
  where
    check (NonRec b _) = getName b `S.member` nms
    check (Rec bs)     = getName (fst (head bs)) `S.member` nms
    nms = go S.empty nm
    go s nm
        | nm `S.member` s = s
        | otherwise       = foldl go (S.insert nm s) (next nm)
    next nm = do
        (getName -> nm', e) <- bs'
        guard $ nm' == nm
        fmap getName . uniqDSetToList . freeVarsOf . freeVars $ e

type MyExpr = DB

infixl <^>

(<^>) = DBApp

noName = mkSystemVarName (mkUnique 'x' 0) (fsLit "<noName>")

codeGen :: MyTypes -> Name -> CoreProgram -> MyExpr
codeGen types main bs = go bs [] where
    go [] vs = case findIndex ((main ==) . getName) vs of
        Just n -> DBVar n
        Nothing -> error "BLC: no main function"
    go (b : bs) vs = mkLet' types b (go bs) vs

expr :: MyTypes -> Expr CoreBndr -> [Name] -> MyExpr
expr types (Var n) vs
    | isValName (varName n) = case findIndex (== getName n) vs of
        Just n -> DBVar n
        _ -> case M.lookup (getOccString n) types of
            Just ci ->
                iterate DBLam (
                    foldr (\i e -> e <^> DBVar i) (DBVar (conI ci))
                    [conW ci..conW ci + conA ci - 1]
                ) !! (conW ci + conA ci)
            _ -> error $ "BLC: free variable <" ++ getOccString n ++ "> " ++ show (map getOccString vs)
    | otherwise = error "BLC: non-value variable"
expr types (Lit _) vs = error "BLC: literals not supported"
expr types (App a b) vs = case b of
    Type{} -> expr types a vs
    Coercion{} -> expr types a vs
    _ -> expr types a vs <^> expr types b vs
expr types (Lam v e) vs
    | isId v = DBLam (expr types e (getName v : vs))
    | otherwise = expr types e vs
expr types (Let b e) vs = mkLet' types b (expr types e) vs
expr types (Case e b _ alts) vs = mkCase types e b alts vs
expr types (Cast e _) vs = expr types e vs
expr types (Tick _ e) vs = expr types e vs
expr types (Type _) vs = error "BLC: unexpected 'Type' expression"
expr types (Coercion _) vs = error "BLC: unexpected 'Coercion' expression"

mkLet' types (NonRec v e) e' vs = DBLam (e' (getName v : vs)) <^> expr types e vs
-- mkLet' types (Rec [(b,e)]) e' vs = error "TODO: implement special case"
mkLet' types (Rec g) e' vs =
    DBLam (DBVar 0 <^> DBVar 0) <^>
    DBLam (
        foldr (\x y -> y <^> (DBVar 0 <^> DBVar 0 <^> (foldr (const DBLam) (DBVar x) g)))
            (foldr (const DBLam) (DBLam (
                foldr (\b i -> i <^> expr types (snd b) ([noName] ++ map (getName . fst) g ++ [noName] ++ vs)) (DBVar 0) g)) g) [0..length g-1]) <^>
    (foldr (const DBLam) (e' (map (getName . fst) g ++ vs)) g)

mkCase types e b alts vs = mkLet' types (NonRec b e) (mkCase' types alts) vs

mkCase' types ((DEFAULT, _, e) : []) vs = expr types e vs
mkCase' types ((DEFAULT, _, e) : alts) vs = undefined
mkCase' types [] vs = DBVar 0
mkCase' types alts@((DataAlt n,_,_):_) vs =
    foldr (\n i -> i <^> mkAlt n) (DBVar 0) ns
  where
    ns = conNs (types M.! getOccString n)
    mkAlt n = foldr (const DBLam) (expr types e (map getName (reverse bs) ++ vs)) bs where
       [(bs,e)] = [(bs,e) | (DataAlt n',bs,e) <- alts, n == getOccString n']
       ci = types M.! n
