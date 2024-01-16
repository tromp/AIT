import Control.Monad
import Control.Monad.Fix

-- nubBy(((>1).).gcd)[2..]

primes = let
  one  = \cont (x:xs) ->     x:cont xs
  zero = \cont (x:xs) -> False:cont xs
  succ n = one . n
  primes n = True:f (primes sn) where
    f = sn f
    sn = succ n
 in False:False:primes zero

main2 = print . take 4096 $ primes

main=putStrLn.take 4096$
 let
 f='0'
 o c(x:y)=x:c y
 z c(x:y)=f:c y
 p n='1':ap fix p(o.n)
 in f:f:p z

--let f='.';o c(x:y)=x:c y;z c(x:y)=f:c y;p n='p':ap fix p(o.n)in f:f:p z
