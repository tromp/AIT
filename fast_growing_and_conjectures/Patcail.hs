-- https://codegolf.stackexchange.com/questions/139355/golf-a-number-bigger-than-tree3/219466#219466
import Data.Char
import Data.Bits
import Data.List
import Data.Maybe
import Control.Applicative
import Control.Monad.State.Strict

data Tree = Nil | Cons Tree Tree deriving (Eq)

asInt :: Tree -> Maybe Int
asInt Nil = Just 0
asInt (Cons Nil t) = fmap succ (asInt t)
asInt (Cons   _ _) = Nothing

instance Show Tree where
  show t = case asInt t of
    Just n  -> show n
    Nothing -> let (Cons t0 t1) = t in "[" ++ show t0 ++ "," ++ show t1 ++ "]" where

-- also see A014486.hs for computing decimal version directly
showBin :: Tree -> String
showBin Nil = "0"
showBin (Cons c1 c2) = "1" ++ showBin c1 ++ showBin c2

toDec :: String -> Int
toDec = foldl' (\acc x -> acc * 2 + digitToInt x) 0

treesN :: Int -> [Tree]
treesN 0 = [Nil]
treesN n = [Cons t0 t1 | (n0,t0) <- treesUpToN (n-1), t1 <- treesN (n-1-n0)]

treesUpToN :: Int -> [(Int,Tree)]
treesUpToN n = (0,Nil) : [(1+n0+n1,Cons t0 t1) | n > 0, (n0,t0) <- treesUpToN (n-1), (n1,t1) <- treesUpToN (n-1-n0)]

trees :: [Tree]
trees = [0..] >>= treesN

predT :: Monad m => Tree -> m Tree
predT (Cons Nil t) = return t
predT (Cons t0 t1) = do
  t0' <- predT t0
  let t = Cons t0' t1
  subst t1 t t where
    -- subst :: Tree -> Tree -> Tree -> m Tree
    subst x y = go where
      -- go :: Tree -> m Tree
      go t = if t==x then return y else case t of
        Nil        -> return Nil
        Cons t0 t1 -> do
           t0' <- go t0
           t1' <- go t1
           return $ Cons t0' t1'

count :: Monad m => Tree -> m Int
count Nil = return 0
count t = do
  t' <- predT t
  n <- count t'
  return (succ n)

predIt :: Monad m => Tree -> m [Tree]
predIt Nil = return [Nil]
predIt t = do
  t' <- predT t
  fmap (t :) (predIt t')

limIO :: Int -> Tree -> IO ()
limIO lim t = do
  putStr $ "> " ++ showBin t ++ "  " ++ show t ++ "  "
  case runFuel lim (count t) of
    Just n -> putStrLn $ "->  " ++ show n
    Nothing -> putStrLn "FAIL"

main = mapM_ (limIO 512) trees

t1 :: Int -> Tree
t1 0 = Nil
t1 n = Cons Nil . t1 . pred $ n

t2 :: Int -> Int -> Tree
t2 m n = Cons (t1 m) (t1 n)

t3 :: Int -> Int -> Int -> Tree
t3 m n o = Cons (t2 m n) (t1 o)

-- newtype needed to provide alternative instances of Applicate/Monad
newtype Fuel a = Fuel { unFuel :: StateT Int Maybe a }

burn :: Fuel ()
burn = Fuel $ do
    e <- Control.Monad.State.Strict.get
    guard $ e > 0
    put   $ e - 1

-- essentially keep old instances
instance Functor Fuel where
    fmap f (Fuel m) = Fuel (fmap f m)
instance MonadFail Fuel where
    fail = Fuel . fail
instance Alternative Fuel where
    empty = Fuel empty
    Fuel a <|> Fuel b = Fuel (a <|> b)

-- add a burn
instance Applicative Fuel where
    pure x = Fuel (pure x)
    Fuel f <*> Fuel x = Fuel $ do
        unFuel burn
        f <*> x
instance Monad Fuel where
    Fuel m >>= f = Fuel $ do
        x <- m
        unFuel burn
        unFuel (f x)

runFuel :: Int -> Fuel a -> Maybe a
runFuel e (Fuel m) = evalStateT m e

runFuelLeft :: Int -> Fuel a -> Maybe (a,Int)
runFuelLeft e (Fuel m) = runStateT m e

{--

We only write numbers or list trees on the left side of +
[0,n] = 1 + n
[0,[0,n]] = 1 + [0,n] = 1 + 1 + n = 2 + n
[1,n] = 1 + let p = [0,n] in [0,p] = 1 + 1 + p = 1 + 1 + 1 + n = 3 + n	(1 <= n)
[2,n] = 1 + let p = [1,n] in [1,p] = 1 + 3 + p = 1 + 3 + 3 + n = 7 + n	(2 <= n)
 ...
[m,n] = 2^{m+1}-1 + n	(m <= n)

Define f n = [n,n] = 2^{n+1}-1 + n

n     2^{n+1}-1     f n
---------------------------
0	   1          1
1	   3          4
2	   7          9
3	  15         18
4	  31         35
5	  63         68

        2^n <= f   n < 2^(n+2)-2              (2^n = f n iff n = 0)
2^2^...^2^n <  f^i n < 2^2^...2^(n+2) - 2     (i > 1)

 [n,[n,n]] = 2^{n+1}-1 + [n,n] = 2^{n+1}-1 + f n = 2^{n+2}-2 + n = 2^{n+1+1}-2-1 + n+1 = f (n+1) - 2
 [n,[n,[n,n]]] = 2^{n+1}-1 + [n,[n,n]] = 3 * (2^{n+1}-1) + n
 [[0,n],[n,n]] = 1 + let p = [n,[n,n]] in [n,p] = [n,[n,[n,n]]]

[[0,n],n] = 1 + let p = [n,n] in [p,p] = 1 + f p = 1 + f^2 n > f^2 n
                                                             < f^2 (n+1)
[[0,[0,n]],n] = 1 + let p = [[0,n],n] in [[0,p],p] = 1 + 1 + f^2 p = 2 + f^2 (1 + f^2 n) > f^4 n
                                                                                         < f^4 (n+1)
[[0,[0,[0,n]]],n] = 1 + let p = [[0,[0,n]],n] in [[0,[0,p]],p] > f^4 p > f^8 n
                                                                       < f^8 (n+1)
[[0,]^m n,n] = [m+n,n] > f^2^m n
                       < f^2^m (n+1)
[[1,n],n] = [3+n,n] > f^2^3 n                                 (1 <= n)
                    < f^2^3 (n+1)
[[2,n],n] = [7+n,n] > f^2^7 n                                 (2 <= n)
                    < f^2^7 (n+1)
[[m,n],n] = [2^(m+1)-1+n,n] > f^2^(2^(m+1)-1) n               (m <= n)
                            < f^2^(2^(m+1)-1) (n+1)
[[n,n],n] = [f n,n] > f^2^(2^(n+1)-1) n > f^2^2^n n > 2^^2^2^n
                    < f^2^(2^(n+1)-1) (n+1)
[[0,[n,n]],n] = 1 + let p = [[n,n],n] in [[p,p],p] > 2^^2^2^p > 2^^2^2^2^^2^2^n > 2^^2^^2^2^n > 2^^^2^1

[2,0] = 1 + [[5,5],5] = 1 + [68,5] > f^2^63 5
                                   < f^2^63 6

 [[0,[0,[n,n]]],n] = 1 + let p = [[0,[n,n]],n] in [[0,[p,p]],p] > 2^^2^^2^2^p > 2^^2^^2^^2^^2^2^n
     [[1,[n,n]],n] > 2^^^2^3
     [[n,[n,n]],n] > 2^^^2^2^n
 [[0,[n,[n,n]]],n] = 1 + let p = [[n,[n,n]],n] in [[p,[p,p]],p] > 2^^^2^2^p > 2^^^2^2^2^^^2^2^n > 2^^^2^^^2^2^n
 [[0,[0,[n,[n,n]]]],n] = 1 + let p = [[0,[n,[n,n]]],n] in [[0,[p,[p,p]]],p] > 2^^^2^^^2^^^2^^^2^2^n
 [[1,[n,[n,n]]],n] > 2^^^^2^3
 [[n,[n,[n,n]]],n] > 2^^^^2^2^n
[[[0,n],[n,n]],n] = 1 + let p = [[n,[n,[n,n]]],n] in [[p,[p,[p,p]]],p] > 2^^^^2^2^p > 2^^^^2^^^^2^2^n

     [[0,[1+n,[n,n]]],n] = 1 + let p = [[1+n,[n,n]],n] in [[[0,p],[p,p]],p] > 2^^^^2^^^^2^^^^2^^^^2^2^n 
     [[1,[1+n,[n,n]]],n] > 2^^^^^2^3
     [[n,[1+n,[n,n]]],n] > 2^^^^^2^2^n
 [[0,[n,[1+n,[n,n]]]],n] > 2^^^^^2^^^^^2^2^n 
 [[1,[n,[1+n,[n,n]]]],n] > 2^^^^^^2^3
 [[n,[n,[1+n,[n,n]]]],n] > 2^^^^^^2^2^n
 [[1+n,[1+n,[n,n]]],n] = 1 + let p = [[n,[n,[1+n,[n,n]]]],n] in [[p,[p,[[0,p],[p,p]]]],p] > 2^^^^^^2^^^^^^2^2^n 
[[2+n,[n,n]],n] = 1 + let p = [[1+n,[1+n,[n,n]]],n] in [[1+p,[1+p,[p,p]]],p] > 2^^^^^^2^^^^^^2^^^^^^2^^^^^^2^2^n

         [[0,[2+n,[n,n]]],n] = 1 + let p = [[2+n,[n,n]],n] in [[2+p,[p,p]],p] > 2^^^^^^^2^3
         [[1,[2+n,[n,n]]],n] > 2^^^^^^^2^5
         [[n,[2+n,[n,n]]],n] > 2^^^^^^^2^2^n
     [[0,[n,[2+n,[n,n]]]],n] > 2^^^^^^^2^^^^^^^2^n
     [[1,[n,[2+n,[n,n]]]],n] > 2^^^^^^^^2^3
     [[n,[n,[2+n,[n,n]]]],n] > 2^^^^^^^^2^2^n
       [[1+n,[2+n,[n,n]]],n] = 1+let p=[[n,[n,[2+n,[n,n]]]],n] in [[p,[p,[2+p,[p,p]]]],p]> 2^^^^^^^^2^^^^^^^^2^2^n
   [[0,[1+n,[2+n,[n,n]]]],n] > 2^^^^^^^^2^^^^^^^^2^^^^^^^^2^^^^^^^^2^2^n
   [[1,[1+n,[2+n,[n,n]]]],n] > 2^^^^^^^^^2^4
   [[n,[1+n,[2+n,[n,n]]]],n] > 2^^^^^^^^^2^2^n
   [[0,[n,[1+n,[2+n,[n,n]]]]],n] > 2^^^^^^^^^2^^^^^^^^^2^2^n
   [[1,[n,[1+n,[2+n,[n,n]]]]],n] > 2^^^^^^^^^^2^3
   [[n,[n,[1+n,[2+n,[n,n]]]]],n] > 2^^^^^^^^^^2^2^n
 [[1+n,[1+n,[2+n,[n,n]]]],n] = 1 + let p = [[n,[n,[1+n,[2+n,[n,n]]]]],n] in [[p,[p,[1+p,[2+p,[p,p]]]]],p] > 2^^^^^^^^^^2^^^^^^^^^^2^2^n
 [[2+n,[2+n,[n,n]]],n] = 1 + let p = [[1+n,[1+n,[2+n,[n,n]]]],n] in [[1+p,[p+p,[2+p,[p,p]]]],p] > 2^^^^^^^^^^2^^^^^^^^^^2^^^^^^^^^^2^^^^^^^^^^2^2^n
[[3+n,[n,n]],n] = 1 + let p = [[2+n,[2+n,[n,n]]],n] in [[2+p,[2+p,[p,p]]],p] > 2^^^^^^^^^^2^^^^^^^^^^2^^^^^^^^^^2^^^^^^^^^^2^^^^^^^^^^2^^^^^^^^^^2^^^^^^^^^^2^^^^^^^^^^2^2^n

[[   n, [n,n]],n] > 2^^^^2^0
[[[0,n],[n,n]],n] > 2^^^^^2^1
[[ 2+n, [n,n]],n] > 2^^^^^^^2^2
[[[1,n],[n,n]],n] > 2^^^^^^^^^^^2^3
...
[[[2,n],[n,n]],n] > 2^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^2^7
...
[[[n,n],[n,n]],n] > 2^{3+2^((2^(n+1)-1)-1)}2^2^n > 2^{2^2^n}2^2^n

[[[0,n],n],n] = 1 + let p = [[[n,n],[n,n]],n] in [[[p,p],[p,p]],p]

[[1,0],0] > let p = [4,0] > 2^^^^2^2^2^^^^2 in [[[p,p],[p,p]],p] > 2^{2^2^p}2^2^p

(F1) f_0 n      = n+1
(F2) f_{α+1} n  = f_α^n n
(F3) f_ω n      = f_n n

f_{ω+1} 2 = f_ω^2 2 = f_ω (f_ω 2) = f_ω (f_2 2) = f_ω 8 = f_8 8
f_{ω+1} 3 = f_ω^3 3 = f_ω^2 (f_2^3 3) = f_ω^2 (24*2^24*2^{24*2^24})

f_{ω+1} 2 < [[1,0],0] < f_{ω+1} 3 

--}
