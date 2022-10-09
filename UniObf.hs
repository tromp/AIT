module Main where
import System.IO
import Data.List
import Text.Parsec
import Control.Applicative hiding ((<|>), many)
data W = W { ann :: !Char, fun :: W -> W }
wC = W ' ' . const
wT  = W ' ' wC
wF = wC $ W ' ' id
wA x = W x undefined
bL e v = W ' ' $ \a -> e (a:v)
bA e1 e2 v = e1 v `fun` e2 v
expr = char '0' *> (bL <$ char '0' <*> expr <|>  bA  <$ char '1' <*> expr <*> expr)
                <|> flip (!!) <$> pred . length <$> many (char '1') <* char '0'
b2w n = if even n then wT else wF
p2w f g = W ' ' $ \h -> h `fun` f `fun` g
cs = wC . wC $ wA ':'
w2l l = if ann (l `fun` cs) /= ':' then [] else l `fun` wT : w2l (l `fun` wF)
w2c iw = ann $ iw `fun` wA '0' `fun` wA '1'
bIO prog = map w2c . w2l . (prog [] `fun` ) . foldr (p2w .b2w . fromEnum) wF
main = do hSetBuffering stdout NoBuffering
          interact $ either (error.show) id . parse (bIO <$> expr <*> getInput) ""
