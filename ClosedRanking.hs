-- https://oeis.org/A114852
import System.Environment
import Data.Ord
import Data.Array
import Data.Maybe
import Data.List
import Data.Function.Memoize
 
-- rank and unrank size items to/from 0..size-1
data Ranking a = Ranking {
  size   :: Integer,
  unrank :: Integer -> a,
  rank   :: a -> Integer
}

-- rank pairs (a0,0)..(a0,size0-1), (a1,0)..(a1,size1-1), ... ,(ak,0)..(ak,sizek-1)
sizeRanking :: Eq a => [(a, Integer)] -> Ranking (a, Integer)
sizeRanking itemSizes = Ranking size unrank rank where
  size = sum . map snd $ itemSizes
  unrank = exhaust itemSizes where
    exhaust ((a,sz):iS) i = if i < sz then (a,i) else exhaust iS (i - sz)
  rank (a,i) = i + sum (map snd (takeWhile ((/= a) . fst) itemSizes))

data T = V Int | L T | A T T deriving (Eq,Read,Show)

termsize :: T -> Int
termsize (V i)   = 2 + i
termsize (L b)   = 2 + termsize b
termsize (A x y) = 2 + termsize x + termsize y

-- number of free variables in term
nfree :: T -> Int
nfree = go 0 where
  go d (V i)   = if i >= d then 1 else 0
  go d (L b)   = go (d+1) b
  go d (A x y) = go d x + go d y

-- number of bound variables in lambda body
nbound :: T -> Int
nbound = go 0 where
  go d (V i)   = if i == d then 1 else 0
  go d (L b)   = go (d+1) b
  go d (A x y) = go d x + go d y

-- sum of indices of bound variables in lambda body
sumbound :: T -> Int
sumbound = go 0 where
  go d (V i)   = if i == d then i else 0
  go d (L b)   = go (d+1) b
  go d (A x y) = go d x + go d y

-- list of redexes in a term
redexes :: T -> [T]
redexes (V i) = []
redexes (L b) = redexes b
redexes t@(A (L x) y) = t: redexes x ++ redexes y
redexes (A x y) = redexes x ++ redexes y

subst :: Int -> T -> T -> T
subst i (V j)   c = if i == j then c else V (if j > i then j-1 else j)
subst i (A a b) c = A (subst i a c) (subst i b c)
subst i (L a)   c = L (subst (i+1) a (incv 0 c))

incv :: Int -> T -> T
incv i (V j)   = V (if i <= j then j+1 else j)
incv i (A a b) = A (incv i a) (incv i b)
incv i (L a)   = L (incv (i+1) a)

-- reduce a redex
reduce :: T -> T
reduce (A (L x) y) = subst 0 x y

-- size change for reducing a redex
delta :: T -> Int
delta (A (L x) y) = sumbound x * (nfree y - 1) + (nbound x - 1) * (termsize y - 2) - nfree (L x) - 6
-- case nbound x of
--   0 -> delta = -4 - termsize y - nfree (L x) < 0
--   1 -> delta = sumbound x * (nfree y - 1) - nfree (L x) - 6 >= 0
--                only when sumbound x > 0 && nfree y >= 1 + 6 / sumbound x
delta t = 0

-- binary encoding
blc :: T -> String
blc (V i) = take (i+1) ['1','1'..] ++ "0"
blc (L b) = "00" ++ blc b
blc (A x y) = "01" ++ blc x ++ blc y

-- term has with no shrinking redex
minimal = all (>= 0) . map delta . redexes

-- terms that are closed within k nested lambdas, of size LessthanorEqual to n
closedLE :: Int -> Int -> [(Int,T)]
closedLE k n = if n < 2 then [] else
             [(2+l,L t) | (l,t) <- closedLE (k+1) (n-2)]
             -- this non-uniform enumeration prevents efficient Ranking
          ++ [(2+l1+l2,A t1 t2) | (l1,t1) <- closedLE k (n-2), (l2,t2) <- closedLE k (n-2-l1)]
          ++ [(2+i,V i) | i<-[0..k-1]]

nClosed :: (Int -> Int -> Integer) -> Int -> Int -> Integer
nClosed memo k n = if n<2 then 0 else
  memo (k+1) (n-2) +                                -- lambda
  sum [memo k i * memo k (n-2-i) | i <- [2..n-2]] + -- app
  if n-2<k then 1 else 0                            -- variable

memoNclosed = memoFix2 nClosed

termRanking :: (Int -> Int -> Ranking T) -> Int -> Int -> Ranking T
termRanking memo k n = Ranking sz unrnk rnk where
  sz = memoNclosed k n
  lamRnk = memo (k+1) (n-2)
  appRnk = sizeRanking [(l, memoNclosed k l * memoNclosed k (n-2-l)) | l <- [2..n-2]]
  unrnk i = if i < size lamRnk then L (unrank lamRnk i)
            else if i < size lamRnk + size appRnk
            then A x y else V (fromIntegral (n-2)) where
              (l,i')  = unrank appRnk (i - size lamRnk)
              yrnk    = memo k (n-2-l)
              (ix,iy) = i' `divMod` size yrnk
              x       = unrank (memo k l) ix
              y       = unrank (memo k (n-2-l)) iy
              
  rnk (L b)   = rank lamRnk b
  rnk (A x y) = size lamRnk + rank appRnk (l, ix * size yrnk + iy) where
                  l  = termsize x
                  ix = rank (memo k l) x
                  yrnk = memo k (n-2-l)
                  iy = rank yrnk y
  rnk (V i)   = size lamRnk + size appRnk

closedRanking = memoFix2 termRanking

ctr = Ranking sz unrnk rnk where
  sizeR = sizeRanking [(l, memoNclosed 0 l) | l <- [0..]]
  sz = undefined
  unrnk i = unrank (closedRanking 0 l) i' where
    (l,i') = unrank sizeR i
  rnk t = rank sizeR (l,i') where
    l = termsize t
    i' = rank (closedRanking 0 l) t

main = do
  args <- getArgs
  let processLines f = getContents >>= mapM_ putStrLn . f . filter (not . null) . lines
  let lshow a = show (termsize a, a)
  case args of
    ["size"]   -> print $ size ctr
    ["rank"]   -> processLines $ map ( show .   rank ctr) . map read
    ["unrank"] -> processLines $ map (lshow . unrank ctr) . map read
    _ -> putStrLn "usage: ctr [size|rank|unrank]"
