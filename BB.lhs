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

Ponder reduction behaviour

> maxdepth :: Int
> maxdepth = 9

> ponder :: DB -> IO ()
> ponder t = if isnf t then putStrLn . show . size $ t else do
>             putStrLn ("pondering " ++ show t)
>             let Just r = reduct t
>             let (_:reducts) = catMaybes . map reduct . take maxdepth $ trail deep_optimize r
>             let Just t1 = fmap deep_optimize . reduce $ t
>             if contracts t || not (r `elem` reducts) then ponder t1 else putStrLn "cycles"

> main :: IO ()
> main = do
>   args <- getArgs
>   case args of
>     [n] -> do
>       mapM_ ponder . filter expands . closed $ read n
>     _ -> putStrLn "usage: BB <Int>"

pondering \(\1 1) (\2 (\2 2))
pondering \(\2 (\2 2)) (\2 (\2 2))
pondering \1 (\(\3 (\2 2)) (\3 (\2 2)))
pondering \1 (\2 (\(\4 (\2 2)) (\4 (\2 2))))
pondering \1 (\2 (\3 (\(\5 (\2 2)) (\5 (\2 2)))))
pondering \1 (\2 (\3 (\4 (\(\6 (\2 2)) (\6 (\2 2))))))
pondering \1 (\2 (\3 (\4 (\5 (\(\7 (\2 2)) (\7 (\2 2)))))))
pondering \1 (\2 (\3 (\4 (\5 (\6 (\(\8 (\2 2)) (\8 (\2 2))))))))
pondering \1 (\2 (\3 (\4 (\5 (\6 (\7 (\(\9 (\2 2)) (\9 (\2 2)))))))))
pondering \1 (\2 (\3 (\4 (\5 (\6 (\7 (\8 (\(\10 (\2 2)) (\10 (\2 2))))))))))
pondering \1 (\2 (\3 (\4 (\5 (\6 (\7 (\8 (\9 (\(\11 (\2 2)) (\11 (\2 2)))))))))))

