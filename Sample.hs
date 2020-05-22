-- sample for BLC ghc plugin (see BLC.hs)
module Sample where

data List a = Cons a (List a)
    deriving Show

infixr `Cons`

data Digit = Zero | One
    deriving Show

Zero `xor` x = x
One `xor` One = Zero
One `xor` Zero = One

f (Cons a xs@(Cons b _)) = xor a b `Cons` f xs

ts = One `Cons` Zero `Cons` Zero `Cons` f ts

mainLC _ = ts

{-
compiles to:
0101000110100001000001100001100000011000000001011001011111101110010111100000100000110011111111101111001011010001000010100011010000001010101100111100101110110000000001110000101100000100101111011100000000011000010110000011001011110111000000000100001011000001100101111011100000000011110000000000011110
-}

-- some code for testing that is ignored by the BLC plugin
toList :: List a -> [a]
toList (Cons x xs) = x : toList xs

main = do
    print $ take 10 $ toList $ ts
