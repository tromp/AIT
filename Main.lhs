> import System.Environment(getArgs)
> import System.IO
> import AIT

> main :: IO ()
> main = do
>   hSetBinaryMode stdin True
>   hSetBinaryMode stdout True
>   hSetBuffering stdout NoBuffering
>   args <- getArgs
>   case args of
>     (action:progfile:strings) -> do
>       progtext <- readFile progfile
>       input    <- getContents
>       putStr $ uni action progtext input strings
>     _ -> mapM_ putStrLn usage
