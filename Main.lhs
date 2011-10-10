> import System(getArgs)
> import System.IO
> import AIT(uni)

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
>     _ -> putStrLn "Usage: blc action progfile [args]..."
