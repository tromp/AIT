import System.Environment(getArgs)
import Control.Monad.State
import Control.Monad.Writer
import Control.Applicative hiding ((<|>),many)
import Text.ParserCombinators.Parsec
 
putc = do (     _,      _,b,      _) <- get; tell [b]
getc = do (  left,  right,_,b:input) <- get; put (  left,  right,     b,input)
prev = do (l:left,  right,b,  input) <- get; put (  left,b:right,     l,input)
next = do (  left,r:right,b,  input) <- get; put (b:left,  right,     r,input)
decr = do (  left,  right,b,  input) <- get; put (  left,  right,pred b,input)
incr = do (  left,  right,b,  input) <- get; put (  left,  right,succ b,input)
loop body = do (_,_,b,_) <- get; when (b /= '\0') (body >> loop body)
parseInstr = liftM loop (between (char '[') (char ']') parseInstrs)
             <|> prev <$ char '<'
             <|> next <$ char '>'
             <|> decr <$ char '-'
             <|> incr <$ char '+'
             <|> putc <$ char '.'
             <|> getc <$ char ','
             <|> return () <$ noneOf "]"
parseInstrs = liftM sequence_ (many parseInstr)
main = do [name] <- getArgs
          source <- readFile name
          input <- getContents
          let init = ("", repeat '\0', '\0', input)
          putStrLn $ either show (execWriter . (`evalStateT` init)) (parse parseInstrs name source)
