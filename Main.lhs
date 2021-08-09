> import System.Environment(getArgs)
> import System.IO
> import AIT

> main :: IO ()
> main = do
>   hSetBinaryMode stdin True

I originally had
    hSetBinaryMode stdout True
as well, but that prevents Unicode output of lambda

>   hSetBuffering stdout NoBuffering
>   args <- getArgs
>   case args of
>     (action:progfile:strings) -> do
>       progtext <- readFile progfile
>       input    <- getContents
>       putStr $ uni action progtext input strings
>     _ -> mapM_ putStrLn usage
