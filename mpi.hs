-- adapted from http://www.cs.ox.ac.uk/people/jeremy.gibbons/publications/spigot.pdf
pi0 = go 1 0 2 1 1 3
  where
     go q r t k n l = if 4*q+r-t<n*t
         then n : go (2*q) (2*(r-n*t)) t k (2*(3*q+r)`div`t-2*n) l
         else go (q*k) ((2*q+r)*l) (t*l) (k+1) ((q*(7*k+2)+r*l)`div`(t*l)) (l+2)

-- same series, but simplified arithmetic
pi1 = go 1 0 1 1
  where
    -- This is using the series pi/2 = 1/1 + 1/3 + (1*2)/(3*5) + (1*2*3)/(3*5*7) ...
    -- a/c is the sum of the first (n-1) terms, b/c is the n-th term.
    --
    -- To check whether a digit can be produced, we check that the parities
    -- of (a+b) `div` c and (a+2*b) `div` c are the same. This is clumsy in
    -- Haskell, but with Church numerals, the parity can be computed by
    -- `\n. n not true`, and `xor` can be incorporated by using a different
    -- value for `true`.
    go n a b c = if d' == 0
        then d : go n (2*a) (2*b) c
        else go (n+1) (a'*n') (b*n) (c*n')
      where
        n' = 2*n + 1
        a' = a + b
        d  = a' `div` c `mod` 2
        d' = ((a' + b) `div` c + d) `mod` 2

-- Same series, but produce the n-th digits after 2n terms. The first
-- 50,000 digits are correct, so the probability of this being wrong
-- under the "random" model for the digits of pi is less than 2^-50,000.
pi_probably = go 1 0 1 1
  where
    step cont n a b c = cont (n+1) ((a+b)*n') (b*n) (c*n')
      where
        n' = 2*n + 1
    go = step (step go')
    go' n a b c = (a `div` c `mod` 2) : go n (2*a) (2*b) c
