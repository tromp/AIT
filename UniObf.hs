import System.IO
import Text.Parsec
import Control.Applicative hiding ((<|>), many)
data W = S !Char | F (W -> W); (F f) <@> w = f w; wC = F . const; wT = F wC; wF = wC $ F id
bL e v = F $ \a -> e (a:v); bA e1 e2 v = e1 v <@> e2 v
expr = char '0' *> (bL <$ char '0' <*> expr <|>  bA  <$ char '1' <*> expr <*> expr)
     <|> flip (!!) <$> pred . length <$> many (char '1') <* char '0'
b2w n = if even n then wT else wF; p2w x y = F $ \z -> z <@> x <@> y; cs = wC . wC $ S ':'
w2l l = case (l <@> cs) of { S ':' -> l <@> wT : w2l (l <@> wF); F  _  -> [] }
w2c iw = c where (S c) = iw <@> S '0' <@> S '1'
bIO prog = map w2c . w2l . (prog [] <@>) . foldr (p2w .b2w . fromEnum) wF
main = do hSetBuffering stdout NoBuffering
          interact $ either (error.show) id . parse (bIO <$> expr <*> getInput) ""
