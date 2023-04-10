-- Show that `BLC` is compressible, establishing that for some k,
-- BBU(ceil(113/114 n) + k) >= BB(n).
--
-- In order to do this, we exploit holes in the code left by
-- applications of `id` (e.g. \x. id x) which are useless because
-- there's a smaller, equivalent lambda term (e.g. \x. x).
--
-- The actual code will start with a 6 bit codon to create 64
-- available prefixes to complete, followed by 113 bit blocks
-- each encoding a 114 bit infix of the ordinary BLC encoding,
-- finished off by another block of up to 114 bit in length.

import qualified Data.Map as M
import Control.Monad

-- State machine abstracting from parsing BLC terms.
-- The states are as follows:
--
-- H 0 -- final state
-- H k -- we're between tokens, expecting `k` more terms ("holes").
-- Z k -- H k followed by a 0 bit, so either an application or an abstraction
-- V k -- H k followed by one or more 1 bits, so in the middle of a variable

data S = H !Int | Z !Int | V !Int
    deriving (Eq, Ord, Show)

step :: S -> [S]
step (H 0) = []              -- final state
step (H n) = [Z n, V n]      -- 0 bit or 1 = variable
step (Z n) = [H n, H (n+1)]  -- 00 = abstraction or 01 = application
step (V n) = [H (n-1), V n]  -- 1+0 = variable end; 1+ = continue variable

-- Check that all terms fit into a prefix code... (plausible == repeat True)
plausible :: [Bool]
plausible = go 1 (M.singleton (H 1) 1)
  where
    -- `c` tracks the number of unused prefixes;
    -- `m` tracks the active states

    -- The analysis is similar to Kraft's inequality, but rather than
    -- computing various 2^-k, we multiply the number of available
    -- prefixes by 2 whenever we extend the prefixes.
    go c m
        = ((c == cost m) :) -- note: stronger than >=
        . go (2*(c - M.findWithDefault 0 (H 0) m))
        $ M.fromListWith (+) $ do
            (s, n) <- M.assocs m
            s <- step s
            pure (s, n)

    -- cost: each prefix is mapped directly so the cost is 1
    cost m = sum $ do
        (h, n) <- M.assocs m
        pure $ 1*n

c0 :: Integer
c0 = 64 -- 6 bits

-- check whether we can compress prefixes of length 0,1,...
-- if we start in state `s` with at least `c0` available prefixes,
-- or `c0+1` prefixes if we are in a `V _` state
compress :: S -> [Bool]
compress s = go i (M.singleton s 1 : repeat M.empty)
  where
    i = case s of
        H _ -> c0
        Z _ -> c0
        V _ -> c0 + 1 -- includes extra prefix

    -- `c` tracks the number of unused prefixes;
    -- `m` tracks the active states
    go c ms@(m : _)
        = ((c >= cost m) :)
        . go (2*(c - M.findWithDefault 0 (H 0) m))
        . take 6
        . (: ms)
        $ M.fromListWith (+) $ do
            (s, n) <- M.assocs m
            s <- step s
            pure (s, n)
          ++ do
            -- we discard states corresponding to terms that contain
            -- an application of `id` (which takes 6 bits: 01 00 10)
            (H h, n) <- M.assocs (ms !! 5)
            guard $ h > 0
            pure (H h, -n)

    -- cost: We want to *compress*, so add a factor of 2 (one bit) to the cost
    cost m = sum $ do
        (h, n) <- M.assocs m
        let w = case h of
                H _ -> 2*c0
                Z _ -> 2*c0
                V _ -> 2*(c0 + 1) -- include extra prefix
        pure $ w*n

check :: Int -> Bool
check n = and $ do
    let maxN = 1 + (n+1) `div` 2 -- 1 + maximum number of holes we can fill
    s <- H 0 : do
        i <- [maxN,maxN-1..1]
        [H i, Z i, V i]
    pure $ compress s !! n

bound :: Int
bound = head $ dropWhile (not . check) $ [1..]

main :: IO ()
main = print bound
-- output: 114
