tpi = go 1 1 1 1 where
-- This is using the series pi/2 = 1/1 + 1/3 + (1*2)/(3*5) + (1*2*3)/(3*5*7) ...
-- a/c is 2^j times the sum of the first n terms minus the valur of the j bits already output
-- b/c is 2^j times the n-th term product [1..n] / product [1,3..2*n+1]
  go b a c = let
      prod bit a' n = bit : go (2*b) (2*a') c n
    in if a >= c
      then prod 1 (a-c)
      else if a + b < c
        then prod 0 a
        else \n -> let
          n21 = 2*n + 1
          bn = b*n
        in go bn (a*n21 + bn) (c*n21) (n+1)

main = print $ take 42 tpi
