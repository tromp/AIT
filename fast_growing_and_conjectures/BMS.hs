-- https://arxiv.org/pdf/2307.04606
-- Well-Orderedness of the Bashicu Matrix System
-- Samuel Vargovˇc´ık
-- July 12, 2023

import Data.List

type Matrix = [Int]

-- proper mod
pmod :: Int -> Int -> Int
pmod a b = ((a `mod` b) + b) `mod` b

showbms :: Int -> [Int] -> String
showbms rows mat = concat $ map (row (pad mat)) [rows-1, rows-2..0] where
  pad mat = replicate ((rows - length mat) `pmod` rows) 0 ++ mat
  row mat r = go (drop r mat) where
    go []    = "0\n"
    go (n:m) = show n ++ "\t" ++ go (drop (rows-1) m)

expand :: Int -> [Int] -> [Int]
expand mod [] = []
expand mod mat@(m1:m) = pre0 ++ m where
  pre1 = take (fromIntegral m1) (m ++ [0,0..])
  pre0 = map (\(i,mi) -> mi + if mi+i >= m1+mod then m1 else 0) (zip [0..] pre1)

matrix0 n = map (const n) [1..n]    -- single column of n n's

bms :: Int -> [[Int]]
bms rows = go (rows-1) (matrix0 rows) where
  go mod  [] = []
  go mod mat = mat : go (if mod==0 then rows-1 else pred mod) (expand mod mat)

bmsize :: Int -> [[Int]] -> String
bmsize rows [] = show rows
bmsize rows (m:ms) = show rows ++ "^(" ++ bmsize rows ms ++ ")^" ++ show (length m)

-- main = mapM_ (putStrLn . showbms 2) $ bms 2
main = putStrLn . bmsize 2 . bms $ 2