module Main where
import System.IO
import Data.List
import Data.Maybe
import Text.Parsec
import Control.Applicative hiding ((<|>), many)
data WHNF a = WHNF { ann :: Maybe a, fun :: (WHNF a -> WHNF a) }
expr = char '0' *> (buildLambda <$ char '0' <*> expr
               <|>  buildApply  <$ char '1' <*> expr <*> expr)
   <|> buildVar <$> pred.length <$> many (char '1') <* char '0'
buildLambda e env = WHNF Nothing $ \arg -> e (arg:env)
buildApply e1 e2 env = e1 env `fun` e2 env
buildVar n env = env !! n
whnfConst = WHNF Nothing . const
whnfTrue  = WHNF Nothing whnfConst
whnfFalse = whnfConst $ WHNF Nothing id
whnfAnn x = WHNF (Just x) undefined
whnfToString = map whnfToChar . whnfToList where
  whnfToList = unfoldr $ \l -> let
     niltest = whnfConst . whnfConst $ whnfAnn undefined
   in const (l `fun` whnfTrue, l `fun` whnfFalse) <$> ann (l `fun` niltest)
  whnfToChar iw = fromJust . ann $ iw `fun` whnfAnn '0' `fun` whnfAnn '1'
stringToWhnf = foldr pairToWhnf whnfFalse . map (bitToWhnf . fromEnum) where
  bitToWhnf n = if even n then whnfTrue else whnfFalse
  pairToWhnf fw gw = WHNF Nothing $ \hw -> hw `fun` fw `fun` gw
buildIO prog = whnfToString . (prog [] `fun` ) . stringToWhnf
main = do
  hSetBuffering stdout NoBuffering
  interact $ either (error.show) id . parse (buildIO <$> expr <*> getInput) ""
