primes = let
  one  = \cont (x:xs) ->   x:cont xs
  zero = \cont (x:xs) -> '0':cont xs
  succ n = one . n
  primes n = '1':f (primes sn) where
    f = sn f
    sn = succ n
 in '0':'0':primes zero

main = putStr primes
