module Main where
import Control.Applicative hiding ((<|>), many)
import Text.Parsec
import System.IO
import Data.List
import Data.Char
data WHNF a = WHNF { ann :: Maybe a, fun :: (WHNF a -> WHNF a) }
type EXPR a = [WHNF a] -> WHNF a
expr :: Parsec String () (EXPR a)
expr = char '0' *> (buildLambda <$ char '0' <*> expr
               <|>  buildApply  <$ char '1' <*> expr <*> expr)
               <|> buildVar <$> pred.length <$> many (char '1') <* char '0'
buildLambda e env = WHNF Nothing $ \arg -> e (arg:env)
buildApply e1 e2 env = fun (e1 env) (e2 env)
buildVar n env = env !! n
listToChurch = foldr pairToChurch churchFalse
pairToChurch fw gw = WHNF Nothing $ \hw -> fun (fun hw fw) gw
eat = WHNF Nothing . const
churchTrue = WHNF Nothing eat
churchFalse = eat $ WHNF Nothing id
churchToList = unfoldr $ \f -> let
    test = eat . eat . eat $ WHNF (Just undefined) undefined
  in const (fun f churchTrue, fun f churchFalse) <$> ann (fun (fun f test) test)
bitToChurch n = if even n then churchTrue else churchFalse
churchToBit iw = n where
  Just n = ann $ fun (fun iw $ WHNF (Just 0) undefined) (WHNF (Just 1) undefined)
stringToChurch = listToChurch . map (bitToChurch . fromEnum)
churchToString = map (intToDigit . churchToBit) . churchToList
buildIO prog = churchToString . fun (prog []) . stringToChurch
main = do
  hSetBuffering stdout NoBuffering
  interact $ either (error.show) id . parse (buildIO <$> expr <*> getInput) ""
