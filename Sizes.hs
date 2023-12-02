{-
for lambdalisp.blc:

Unary:       163654
Tree:        129128
Levenshtein: 126903
Elias gamma: 125862
Huffman:     118902
-}

import Data.List

main = do
    ts <- toks <$> getContents
    putStrLn $ unwords ["Unary:      ", show $ sum $ map szU ts]
    putStrLn $ unwords ["Catalan:    ", show $ sum $ map szT ts]
    putStrLn $ unwords ["Levenshtein:", show $ sum $ map szL ts]
    putStrLn $ unwords ["Elias omega:", show $ sum $ map szE ts]
    putStrLn $ unwords ["Huffman:    ", show $ huf ts]

data Tok = Abs | App | Var Int deriving (Eq, Ord)

toks :: String -> [Tok]
toks "" = []
toks ('0':'0':xs) = Abs : toks xs
toks ('0':'1':xs) = App : toks xs
toks xs | (ys, '0':xs) <- span (== '1') xs = Var (length ys - 1) : toks xs

-- size, unary encoding
szU :: Tok -> Int
szU Abs = 2
szU App = 2
szU (Var v) = 2 + v

-- size, tree encoding
szT :: Tok -> Int
szT Abs = 2
szT App = 2
szT (Var v) = 2 * length (takeWhile (<= v) (scanl (+) 0 cats))

cats :: [Int]
cats = [c (2*n) n `div` (n+1) | n <- [0..]]

-- size, Levenshtein encoding
szL :: Tok -> Int
szL Abs = 2
szL App = 2
szL (Var v) = 1 + l v
  where
    l 0 = 1
    l n = 1 + l k + k where k = floor (logBase 2 (fromIntegral n))

-- size, Elias omega encoding
szE :: Tok -> Int
szE Abs = 2
szE App = 2
szE (Var v) = 1 + l (v + 1)
  where
    l 1 = 1
    l n = 1 + l k + k where k = floor (logBase 2 (fromIntegral n))

-- size, optimal Huffman encoding (a lower bound)
huf :: [Tok] -> Int
huf = go . map length . group . sort
  where
    go [_] = 0
    go xs | x:y:xs <- sort xs = x+y + go (x+y : xs)

-- misc
c :: Integral a => a -> a -> a
c n 0 = 1
c n k = c (n-1) (k-1) * n `div` k
