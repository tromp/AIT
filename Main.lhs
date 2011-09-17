> import System(getArgs)
> import System.IO
> import Data.List.Split(splitOn)
> import Control.Monad(liftM)
> import AIT(uni)

> main :: IO ()
> main = do
>   hSetBinaryMode stdin True
>   hSetBinaryMode stdout True
>   hSetBuffering stdout NoBuffering
>   args <- getArgs
>   case args of
>     (action:specs@(_:_)) -> do
>       (progtext:strings) <- mapM mkdata specs
>       putStr $ uni action progtext strings where
>         mkdata = liftM concat . mapM litOrFile . splitOn "++"
>         litOrFile "stdin" = getContents
>         litOrFile ('@':s) = readBinaryFile s
>         litOrFile  s      = return s
>     _ -> putStrLn "Usage: blc action [@]progfile [ [@]data[++[@]data]... ]..."

> readBinaryFile :: FilePath -> IO String
> readBinaryFile fn = openBinaryFile fn ReadMode >>= hGetContents
