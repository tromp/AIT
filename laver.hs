import Control.Monad

mx = 7

-- Consider a shelf satisfying  a |> 0 = a+1 on { 0, 1, ..., mx }. Note that
--   mx |> (a + 1) = mx |> (a |> 0) = (mx |> a) |> (mx |> 0)
--                 = (mx |> a) |> 0 = (mx |> a) + 1.
-- Together with mx |> 0 = 0 implies mx |> a = a by induction; furthermore,
--   a |> (b + 1) = a |> (b |> 0) = (a |> b) |> (a |> 0) = (a |> b) |> (a + 1)
-- holds. So assuming that |> is well-defined, the following implementation
-- is correct (termination is a bit convoluted but works out).

-- | shelf defined by  a |> 0 = a + 1
laver0 a b
    | a == mx   = b
    | b == 0    = a + 1
    | otherwise = laver0 (laver0 a (b - 1)) (a + 1)

-- We can derive the following two property by induction on that definition:
--    a |> b > a  if  a < mx
-- So since
--   a + 1 = a |> 0 = a |> (mx + 1) = (a |> mx) |> (a + 1)
-- we must have a |> mx = mx, since otherwise we would have a < mx and
-- a |> mx < mx which would imply the contradiction
--   a + 1 = (a |> mx) |> (a + 1) > a |> mx > a.

-- Next we apply the map \x -> mx - x. Note that a |> mx = mx becomes
-- a |> 0 = 0, and mx |> a = a becomes 0 |> a = a

-- | shelf defined by  a |> mx = a-1
laver1 a b
    | a == 0 = b
    | b == mx = a - 1
    | otherwise = laver1 (laver1 a (b + 1)) (a - 1)

-- This definition still depends on mx, but this is easily avoided:
-- a |> b is computed by mx - b iterations of the map \x -> x |> (a - 1),
-- starting with a - 1; since (a |> 0) |> (a - 1) = 0 |> (a - 1) = a - 1,
-- so we can also iterate the map mx + 1 - b times starting with 0.
-- The period of the iterated sequence must divide mx + 1 for |> to be
-- well-defined, so the following definition is justified. Note that it
-- does not depend on mx.

-- | memoized version of `laver1`
laver 0 b = b
laver a b = let ls = lavers !! a in ls !! ((-b) `mod` length ls)

{-# NOINLINE lavers #-}
lavers = [0] : map go [0..] where
    go a = 0 : takeWhile (/= 0) (iterate (\b -> laver b a) a)

main = do
    table mx "laver0" laver0
    table mx "laver1" laver1
    table 15 "laver"  laver
    mapM_ print [(length l, l) | l <- [lavers !! (2^n-1) | n <- [0..12]]]
 where
    table mx name laver = do
        putStrLn name
        forM_ [0..mx] $ \i -> do
            putStrLn $ unwords [showW (laver i j) | j <- [0..mx]]
        putStrLn ""
    w = length (show mx)
    showW = reverse . take w . (++ repeat ' ') . reverse . show
