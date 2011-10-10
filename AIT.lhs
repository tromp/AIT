> module AIT(uni) where
> import Lambda
> import Data.List(unfoldr)
> import Data.Char(chr,ord,intToDigit,digitToInt)

Encode an expression as a binary string.

> class Encodeable a where
>   encode :: a -> String

Size in bits of an expression, assuming no free variables

>   size :: a -> Int
>   size = length . encode

> instance Encodeable DB where
>   encode z = prebin z "" where
>     prebin (DBVar 0) s = '1':'0':s
>     prebin (DBVar i) s | i>0 = '1':(prebin (DBVar (i-1)) s)
>     prebin (DBVar   _) _ = error "Negative de-Bruijn index"
>     prebin (DBLam   e) s = '0':'0':(prebin e s)
>     prebin (DBApp x y) s = '0':'1':(prebin x (prebin y s))

Size in bits of an expression, assuming no free variables

> instance Encodeable CL where
>   encode z = prebin z "" where
>     prebin (CVar _) _ = error "can't encode variables"
>     prebin CombS s = '0':'0':s
>     prebin CombK s = '0':'1':s
>     prebin (CApp x y) s = '1':(prebin x (prebin y s))

Interpret an expression as a list of binary strings.

> bshow :: DB -> String
> bshow (DBLam (DBLam (DBVar 0))) = "" -- empty
> bshow (DBLam ((DBVar 0) `DBApp` (DBLam (DBLam (DBVar 0))) `DBApp` y))
>   = '1':(bshow y)
> bshow (DBLam ((DBVar 0) `DBApp` (DBLam (DBLam (DBVar 1))) `DBApp` y))
>   = '0':(bshow y)
> bshow (DBLam ((DBVar 0)
>   `DBApp` (DBLam ((DBVar 0) `DBApp` (DBLam (DBLam (DBVar b0)))
>   `DBApp` (DBLam ((DBVar 0) `DBApp` (DBLam (DBLam (DBVar b1)))
>   `DBApp` (DBLam ((DBVar 0) `DBApp` (DBLam (DBLam (DBVar b2)))
>   `DBApp` (DBLam ((DBVar 0) `DBApp` (DBLam (DBLam (DBVar b3)))
>   `DBApp` (DBLam ((DBVar 0) `DBApp` (DBLam (DBLam (DBVar b4)))
>   `DBApp` (DBLam ((DBVar 0) `DBApp` (DBLam (DBLam (DBVar b5)))
>   `DBApp` (DBLam ((DBVar 0) `DBApp` (DBLam (DBLam (DBVar b6)))
>   `DBApp` (DBLam ((DBVar 0) `DBApp` (DBLam (DBLam (DBVar b7)))
>   `DBApp` (DBLam (DBLam (DBVar 0))))))))))))))))))) `DBApp` y))
>   = chr (foldr (\x z->2*z+1-x) 0 [b7,b6,b5,b4,b3,b2,b1,b0]):(bshow y)
> bshow (DBLam ((DBVar 0) `DBApp` x `DBApp` y))
>   = "<"++(bshow x)++","++(bshow y)++">"
> bshow x = '(': (shows x ")")

Substitute an expression for all variables binding to o'th enclosing lambda

> subst :: Int -> DB -> DB -> DB
> subst o x v@(DBVar i) | i==o = adjust 0 x
>                       | i >o = DBVar (pred i)
>                       | otherwise = v
>   where adjust n e@(DBVar j) | j >= n = DBVar (j+o)
>                              | otherwise = e
>         adjust n (DBLam body) = DBLam (adjust (succ n) body)
>         adjust n (DBApp fun arg) = DBApp (adjust n fun) (adjust n arg)
> subst o x (DBLam body) = DBLam (subst (succ o) x body)
> subst o x (DBApp fun arg) = DBApp (subst o x fun) (subst o x arg)

Optimize an expression; repeatedly contract redexes that reduce in size

> optimize :: DB -> DB
> optimize x = let ox = opt x in if ox == x then x else optimize ox where
>   opt (DBLam body) = DBLam (opt body)
>   opt t@(DBApp (DBLam body) arg) | size s < size t = opt s where
>     s = subst 0 arg body
>   opt (DBApp fun arg) = DBApp (opt fun) (opt arg)
>   opt e = e

Bitstring functions -----------------------------------------------------

> cons :: LC Id -> LC Id -> LC Id
> cons x y = Lam (Id "z") $ Var (Id "z") `App` x `App` y

> lcTrue :: LC Id
> lcTrue  = Lam (Id "x") $ Lam (Id "y") $ Var (Id "x")

> lcFalse :: LC Id
> lcFalse = Lam (Id "x") $ Lam (Id "y") $ Var (Id "y")

> listtoLC :: [LC Id] -> LC Id
> listtoLC = foldr cons lcFalse

> bittoLC :: Char -> LC Id
> bittoLC '0' = lcTrue;
> bittoLC '1' = lcFalse;
> bittoLC _ = error "Character is not 0 or 1"

> bitstoLC :: String -> LC Id
> bitstoLC = listtoLC . map bittoLC

> fromByte :: Char -> String
> fromByte = reverse . take 8 . unfoldr (\x->Just(intToDigit(x`mod`2),x`div`2)) . ord

> bytestoLC :: String -> LC Id
> bytestoLC = listtoLC . map (bitstoLC . fromByte)

> toBytes :: String -> String
> toBytes [] = []
> toBytes bytes = chr num : toBytes rest where
>   (byte,rest) = splitAt 8 bytes
>   num = foldl (\x y -> 2*x + (digitToInt y)) 0 $ pad8 byte
>   pad8 = take 8 . (++ repeat '0')

> usesBytes :: String -> Maybe String
> usesBytes action = if last action=='8' then Just (init action) else Nothing

> uni :: String -> String -> String -> [String] -> String
> uni opn progtext inp args = let
>   (op,input) = case usesBytes opn of
>     Just op' -> (op',bytestoLC inp)
>     Nothing  -> (opn, bitstoLC inp)
>   prog = read progtext :: LC Id
>   machine = foldl (\p -> App p . bitstoLC) (App prog input) args
>   tex = concatMap (\c -> if c=='\\' then "\\lambda " else [c])
>   nl = (++ "\n")
>  in case op of
>   "m" -> nl .                 bshow . nf . toDB $ machine
>   "p" -> nl .                  show             $ prog
>   "f" -> nl .                  show . nf . toDB $ prog
>   "e" -> nl .     show . strongCL . toCL . toDB $ prog
>   "c" -> nl .     show . toCL . optimize . toDB $ prog
>   "x" -> nl .   encode . toCL . optimize . toDB $ prog
>   "d" -> nl .            show . optimize . toDB $ prog
>   "t" -> nl .      tex . show . optimize . toDB $ prog
>   "b" ->               encode . optimize . toDB $ prog
>   "B" -> toBytes .     encode . optimize . toDB $ prog
>   "s" -> nl .     show . size . optimize . toDB $ prog
>   a   -> "Action " ++ a ++ " not recognized.\n"
