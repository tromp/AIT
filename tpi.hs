tpi = go 1 1 1 1
  where
    -- This is using the series pi/2 = 1/1 + 1/3 + (1*2)/(3*5) + (1*2*3)/(3*5*7) ...
    -- a/c is 2^j times the sum of the first n terms minus the valur of the j bits already output
    -- b/c is 2^j times the n-th term product [1..n] / product [1,3..2*n+1]
    go n a b c = if a >= c
        then 1 : go n (2*(a-c)) (2*b) c
        else if a + b < c
          then 0 : go n (2*a) (2*b) c
          else go (n+1) (a*n21 + bn) bn (c*n21)
      where
        n21 = 2*n + 1
        bn = b*n
-- For base b, change (2,-2*n,1) to (b,-b*n,1) and (1,0,2) to (1,0,b) for b <= 3, (1,0,1) for b > 3

main = print $ take 42 tpi
