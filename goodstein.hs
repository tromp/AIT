{-# LANGUAGE RankNTypes #-}

-- We encode the Goodstein sequence without recursion using second order
-- types. The key insight is that the Goodstein function is intimately
-- connected to fundamental sequences and a slight variation on the Hardy
-- hierarchy. So we can define (countable) ordinal numbers by
--
--   data O = Limit (Nat -> O) | Succ O | Zero
--
-- where the 'Limit' constructor takes a function that produces the
-- fundamental sequence of the ordinal.
--
-- cf. https://en.wikipedia.org/wiki/Goodstein%27s_theorem
--     https://en.wikipedia.org/wiki/Hardy_hierarchy
--
-- In order to avoid recursion, we use Church encodings for the data
-- types below. This also makes a translation into Lambda Calculus
-- straight-forward.

------------------------------------------------------------------------------
-- natural numbers
newtype N   = N { n_ :: forall r. (r -> r) -> r -> r }

-- zero
nZ :: N
nZ = N (\s z -> z)

-- successor
nS :: N -> N
nS n = N (\s z -> n_ n s (s z))

------------------------------------------------------------------------------
-- ordinal numbers
newtype O   = O { o_ :: forall r. ((N -> r) -> r) -> (r -> r) -> r -> r }

-- zero
oZ :: O
oZ = O (\l s z -> z)

-- successor
oS :: O -> O
oS n = O (\l s z -> s (o_ n l s z))

-- limit of fundamental sequence
oL :: (N -> O) -> O
oL f = O (\l s z -> l (\n -> o_ (f n) l s z))

-- `add n m` only works if in Cantor normal form, a_k >= b_1, where
--   n = sum(i=1 to k, w^a_i),  m = sum(i=1 to l, w^b_i)
add :: O -> O -> O
add n m = o_ m oL oS n

w :: O
w = oL (\n -> n_ n oS oZ)

mul :: O -> O -> O
mul n m = o_ m oL (`add` n) oZ

expw :: O -> O
expw n = o_ n oL (`mul` w) (oS oZ)

------------------------------------------------------------------------
-- lists
newtype L a = L { l_ :: forall r. (a -> r -> r) -> r -> r }

nil :: L a
nil = L (\c n -> n)

infixr 5 #
(#) :: a -> L a -> L a
x # xs = L (\c n -> c x (l_ xs c n))

hd :: L a -> a
hd xs = l_ xs (\x xs -> x) undefined

tl :: L a -> L a
tl xs = L (\c n -> l_ xs (\x xs f -> f x (xs c)) (\_ -> n) (\x y -> y))

map' :: (a -> b) -> L a -> L b
map' f xs = L (\c -> l_ xs (c . f))

(##) :: L a -> L a -> L a
xs ## ys = L (\c n -> l_ xs c (l_ ys c n))



------------------------------------------------------------------------------
-- Goodstein sequence

-- conversion to hereditary base 2 representation
base2 :: N -> O
base2 n = n_ n go id hd (oZ # nil) where
    go :: ((L O -> O) -> L O -> O) -> (L O -> O) -> L O -> O
    go f lf xs = f (lf . tl) (xs ## map' (add (expw (lf xs))) xs)

-- goodstein sequence
goodstein :: N -> N
goodstein n = o_ (base2 n) l s z (nS nZ) where
    z = id
    s n m = n (nS m)
    l f m = f (nS (nS m)) m

test :: Integer -> Integer
test n = n_ (goodstein (N (\f x -> iterate f x !! fromInteger n))) succ 0
