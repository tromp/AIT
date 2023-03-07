module Main (main) where

import System.IO
import Data.Char
import Control.Applicative
import Debug.Trace

data Term = App Term Term | Abs Term | Var Int

instance Show Term where
    showsPrec d (Abs t) = showParen (d>7) $
        showString "\\" . shows t
    showsPrec d (App l r) = showParen (d>8) $
        showsPrec 8 l . showString " " . showsPrec 9 r
    showsPrec d (Var i) = shows (i+1)

parse :: String -> Maybe (Term, String)
parse ('0' : '0' : xs) = do
    (t, xs') <- parse xs
    return (Abs t, xs')
parse ('0' : '1' : xs) = do
    (l, xs') <- parse xs
    (r, xs'') <- parse xs'
    return (App l r, xs'')
parse ('1' : xs) = do
    (os, '0':xs') <- return $ span (=='1') xs
    return (Var (length os), xs')

data Term' = Return Closure | Apply Term' Term Env

data Closure = TE Term Env | IDX Int

type Env = [Closure]

whnf :: Term -> Env -> Term'
whnf (Var i) env = case env !! i of
  i@(IDX _) -> Return i
  TE t e -> whnf t e
whnf t@(Abs _) env = Return (TE t env)
whnf (App l r) env = case whnf l env of
  Return (TE (Abs l') env') -> whnf l' (TE r env : env')
  l' -> Apply l' r env

nf :: Int -> Term -> Env -> Term
nf d t env = nf' d (whnf t env) where
  nf' d (Apply l r env) = App (nf' d l) (nf d r env)
  nf' d (Return (TE (Abs t) env)) = Abs (nf (d+1) t (IDX d : env))
  nf' d (Return (TE t _)) = t
  nf' d (Return (IDX i)) = Var (d - i - 1)

encode :: String -> Term
encode = foldr (\x -> Abs . (App . App (Var 0) . code $ x)) nil where
  nil = code '1';
  code '0' = Abs (Abs (Var 1))
  code '1' = Abs (Abs (Var 0))
  code  x  = encode (showsBin 8 (ord x) "")
  showsBin n x = if n==0 then id else let (x',b) = divMod x 2 in
     showsBin (n-1) x' . (intToDigit b :)

decode :: Term -> String
decode (Abs (Abs (Var 0))) = "" -- empty
decode (Abs (Var 0 `App` (Abs (Abs (Var 0))) `App` y)) = '1':decode y
decode (Abs (Var 0 `App` (Abs (Abs (Var 1))) `App` y)) = '0':decode y
decode (Abs (Var 0 `App` (Abs (Var 0 `App` (Abs (Abs (Var b0)))
                    `App` (Abs (Var 0 `App` (Abs (Abs (Var b1)))
                    `App` (Abs (Var 0 `App` (Abs (Abs (Var b2)))
                    `App` (Abs (Var 0 `App` (Abs (Abs (Var b3)))
                    `App` (Abs (Var 0 `App` (Abs (Abs (Var b4)))
                    `App` (Abs (Var 0 `App` (Abs (Abs (Var b5)))
                    `App` (Abs (Var 0 `App` (Abs (Abs (Var b6)))
                    `App` (Abs (Var 0 `App` (Abs (Abs (Var b7)))
                    `App` (Abs (Abs (Var 0))))))))))))))))))) `App` y))
  = chr (foldr (\x z->2*z+1-x) 0 [b7,b6,b5,b4,b3,b2,b1,b0]):(decode y)
decode (Abs (Var 0 `App` x `App` y)) = "<" ++ decode x ++ "," ++ decode y ++ ">"
decode x = '(': shows x ")"

main = do
    hSetBuffering stdout NoBuffering
    Just (t, input) <- parse . filter (not . isSpace) <$> getContents
    putStr . decode . nf 0 (App t (encode input)) $ []
