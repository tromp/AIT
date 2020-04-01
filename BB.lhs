> import System.Environment(getArgs)
> import System.IO
> import Data.List
> import Data.Maybe
> import Lambda
> import AIT

Enumerate all lambda terms of given openness and size

> openness :: Int -> Int -> [DB]
> openness o n = if n < 2 then [] else lams ++ apps ++ vars where
>   lams = map DBLam $ openness (o+1) (n-2)
>   apps = [DBApp t1 t2 | n1 <- [2..n-2], t1 <- openness o n1, t2 <- openness o (n-2-n1)]
>   vars = map DBVar [n-2 | n-2 < o]

Enumerate all closed lambda terms of given size

> closed :: Int -> [DB]
> closed = openness 0

Repeated reduction of whole or part

> trail :: (DB -> DB) -> DB -> [DB]
> trail f t = t : case reduce t of
>                   Just t1 -> trail f (f t1)
>                   Nothing -> []

Equality modulo free vars

> eqfree :: Int -> DB -> DB -> Bool
> eqfree n (DBLam body1) (DBLam body2) = eqfree (n+1) body1 body2
> eqfree n (DBApp fun1 arg1) (DBApp fun2 arg2) = eqfree n fun1 fun2 && eqfree n arg1 arg2
> eqfree n (DBVar i1) (DBVar i2) = i1 == i2 || (i1 >= n && i2 >= n)
> eqfree _ _ _ = False

Need bound on cycle detection length

> maxdepth :: Int
> maxdepth = 3

> data BBClass = NormalForm DB | Diverging | Unknown

Ponder reduction behaviour

> classify :: DB -> IO ()
> classify t = if isnf t then putStrLn . show . size $ t else if size t > 999 then putStrLn "ABORT" else do
>             putStrLn ("classify " ++ show t)
>             let Just r = reduct t
>             let (_:reducts) = catMaybes . map reduct . take maxdepth $ trail deep_optimize r
>             -- mapM_ (putStrLn . show) reducts
>             let Just t1 = fmap deep_optimize . reduce $ t
>             if t1 /= t && (contracts t || not (any (eqfree 0 r) $ reducts)) then classify t1 else putStrLn "cycles"

> main :: IO ()
> main = do
>   args <- getArgs
>   case args of
>     [n] -> do
>       -- mapM_ (\t -> putStrLn (show t) >> classify t) . filter expands . closed $ read n
>       mapM_ classify . filter expands . closed $ read n
>     [n, p] -> do
>       mapM_ (\t -> classify t) $ [read p]
>     _ -> putStrLn "usage: BB <Int>"

pondering (\1 1 1) (\\1 2 2)
pondering (\\1 2 2) (\\1 2 2) (\\1 2 2)
pondering (\1 (\\1 2 2) (\\1 2 2))  (\\1 2 2)
pondering (\\1 2 2) (\\1 2 2) (\\1 2 2)

