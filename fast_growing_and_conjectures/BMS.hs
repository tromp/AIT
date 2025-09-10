-- this program implements the Flattened Address Matrix System (FAMS) variant described in
-- https://codegolf.stackexchange.com/questions/18028/largest-number-printable/273656#273656
-- by user https://codegolf.stackexchange.com/users/101119/patcail
-- except that addresses run in reverse (parent addresses are always larger than their children)
-- and elements don't contain the address of their parent, but the distance to their parent
-- So it should perhaps be called Flattened Distance Matrix System (FDMS)
-- https://arxiv.org/abs/2307.04606
-- Well-Orderedness of the Bashicu Matrix System
-- Rachel Hunter
-- July 12, 2023

import Data.List

type Matrix = [Int]

showbms :: Int -> [Int] -> String
showbms rows mat = concat (map (row (pad mat)) [rows-1, rows-2..0]) where
  pad mat = replicate ((rows - length mat) `mod` rows) 0 ++ mat
  row mat r = go (drop r mat) where
    go []    = "\n"
    go (n:m) = show n ++ "\t" ++ go (drop (rows-1) m)

expand :: Int -> [Int] -> [Int]
expand mod [] = []
expand mod mat@(m0:m) = pre0 ++ m where
  pre1 = take (fromIntegral m0) m
  pre0 = map (\(i,mi) -> mi + if mi+i >= m0+mod then m0 else 0) (zip [0..] pre1)

-- 2 columns of n n's followed by a column of n 0s
matrix0 n = replicate (2*n) n ++ replicate n 0

-- return list of iteratively expanded matrices up to one with 0 head
bms :: Int -> [[Int]]
bms rows = go (rows-1) (matrix0 rows) where
  go mod mat@(0:_) = [mat]
  go mod mat = mat : go (pred (if mod==0 then rows else mod)) (expand mod mat)

bmsize :: [[Int]] -> Int
bmsize = sum . map head

main = do
  mapM_ print $ bms 2
  mapM_ (putStrLn . showbms 2) $ bms 2
  print . bmsize . bms $ 2
