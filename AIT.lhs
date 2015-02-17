> module AIT(uni,usage) where
> import Lambda
> import Data.List(unfoldr)
> import Data.Char(chr,ord,intToDigit,digitToInt)
> import qualified Data.DList as DL
> import Data.Array.Unboxed
> import Control.Monad.Writer

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

> type Point = (Int,Int)

> diagram :: Bool -> DB -> UArray Point Char
> diagram alt = diagArray . runWriter . diagWrite 0 0 where
>   dy = if alt then 0 else 1
>   diagWrite :: Int -> Int -> DB -> Writer (DL.DList (Point,Char)) (Point, Point)
>   diagWrite y x (DBLam e) = do
>     dim@((_,x1),_) <- diagWrite (y+1) x e
>     tell $ DL.fromList [((y,i),'_') | i <- [x..x1]]
>     return dim
>   diagWrite y x (DBApp f a) = do
>     ((fy,fx),(fxl,fxr)) <- diagWrite y x f
>     let fx1 = if alt then fxr else fxl
>     ((ay,ax),(axl,_)) <- diagWrite y (fx+2) a
>     let my = 1-dy + max fy ay
>     tell $        DL.fromList [((i,fx1),'|') | i <- [fy+1..my+dy]]
>       `DL.append` DL.fromList [((i,axl),'|') | i <- [ay+1..my]]
>       `DL.append` DL.fromList [((my,i),'_') | i <- [fx1+1..axl-1]]
>     return ((my+dy,ax),(fx1,axl))
>   diagWrite y x (DBVar n) = do
>     tell $ DL.fromList [((y-i,x+1),'|') | i <- [1-dy..n]]
>     return ((y-1+dy,x+2),(x+1,x+1))
>   diagArray :: ((Point,Point),DL.DList (Point,Char)) -> UArray (Int,Int) Char
>   diagArray (((y,x),_),pc) = accumArray (const id) ' ' ((0,0),(y,x+1))
>                  $ [((j,x+1),'\n') | j <- [0..y]] ++ reverse (DL.toList pc)

> boxChar :: Bool -> UArray Point Char -> String
> boxChar alt a = boxer 0 1 >>= boxUtf8 where
>   (_,(y,x)) = bounds a
>   boxer :: Int -> Int -> String
>   boxer j i | i>x = if j<y' then boxer (j+1) 1 else [] where
>                        y' = if alt then y else y-1
>   boxer j i = boxVar (a!(j,i-1)) (a!(j,i)) (a!(j,i+1)) (j<y && a!(j+1,i)=='|') : boxMid (a!(j,i+2)) : boxer j (i+4) where
>     boxMid '_' = '\x80'
>     boxMid c = c
>     boxVar  _  ' '  _  _     = ' '
>     boxVar '_' '|' '_' _     = '\xbc' -- +
>     boxVar ' ' '|' ' ' _     = '\x82' -- |
>     boxVar '_' '|' ' ' True  = '\xa4' -- 4
>     boxVar '_' '|' ' ' False = '\x98' -- J
>     boxVar ' ' '|' '_' True  = '\x9c' -- F
>     boxVar ' ' '|' '_' False = '\x94' -- L
>     boxVar  _  '_'  _  True  = '\xac' -- T
>     boxVar  _  '_'  _  False = '\x80' -- -
>     boxVar  _   c   _  _     = error $ "Unexpected char" ++ [c]
>   boxUtf8 :: Char -> String
>   boxUtf8 c = pref c ++ [c] where
>     pref  ' ' = ""
>     pref '\n' = ""
>     pref  _   = "\xe2\x94"

> toPBM :: UArray Point Char -> String
> toPBM a = "P1\n" ++ show x ++ " " ++ show (2*y+1) ++ "\n" ++ tobmp True 0 0 where
>   (_,(y,x)) = bounds a
>   tobmp :: Bool -> Int -> Int -> String
>   tobmp False  j i | i>x = tobmp True j 0
>   tobmp True   j i | i>x = if j<y then tobmp False (j+1) 0 else []
>   tobmp bottom j i = pixel bottom (a!(j,i)) ++ tobmp bottom j (i+1)
>   pixel _      ' ' = " 0"
>   pixel bottom '_' = if bottom then " 1" else " 0"
>   pixel _      '|' = " 1"
>   pixel _      c = [c]

> uni :: String -> String -> String -> [String] -> String
> uni op progtext input args = let
>   prog = read progtext :: LC Id
>   machine = \inp -> foldl (\p -> App p . bitstoLC) (App prog inp) args
>   tex = concatMap (\c -> if c=='\\' then "\\lambda " else [c])
>   nl = (++ "\n")
>  in case op of
>   "run"     -> nl .   bshow . nf . toDB . machine $  bitstoLC input
>   "run8"    -> nl .   bshow . nf . toDB . machine $ bytestoLC input
>   "print"   -> nl .                     show             $ prog
>   "nf"      -> nl .                     show . nf . toDB $ prog
>   "comb_nf" -> nl .        show . strongCL . toCL . toDB $ prog
>   "comb"    -> nl .        show . toCL . optimize . toDB $ prog
>   "bcl"     -> nl .      encode . toCL . optimize . toDB $ prog
>   "diagram" -> elems   . diagram False . optimize . toDB $ prog
>   "Diagram" -> elems   . diagram  True . optimize . toDB $ prog
>   "boxchar" -> boxChar False . diagram False . optimize . toDB $ prog
>   "Boxchar" -> boxChar True . diagram  True . optimize . toDB $ prog
>   "pbm"     -> toPBM   . diagram False . optimize . toDB $ prog
>   "Pbm"     -> toPBM   . diagram  True . optimize . toDB $ prog
>   "tex"     -> nl .         tex . show . optimize . toDB $ prog
>   "printlc" -> nl .               show . optimize . toDB $ prog
>   "blc"     ->                  encode . optimize . toDB $ prog
>   "Blc"     -> toBytes .        encode . optimize . toDB $ prog
>   "size"    -> nl .        show . size . optimize . toDB $ prog
>   "help"    -> unlines usage
>   a         -> "Action " ++ a ++ " not recognized.\n"

> usage :: [String]
> usage = [
>   "Usage: blc action progfile [args]...",
>   "run\trun given program applied to standard input bits and args",
>   "run8\trun given program applied to standard input bytes and args",
>   "print\tshow program",
>   "nf\tshow normal form",
>   "comb_nf\tnormal form through SK reduction",
>   "comb\tshow translation to combinatory logic",
>   "bcl\tencode in binary combinatory logic",
>   "diagram\tshow ascii diagram",
>   "Diagram\tshow alternative ascii diagram",
>   "boxchar\tshow boxdrawing character diagram",
>   "Boxchar\tshow boxdrawing character alternative diagram",
>   "pbm\tshow diagram in portable bitmap format",
>   "Pbm\tshow alternative diagram in portable bitmap format",
>   "tex\tshow program as TeX",
>   "printlc\tshow lambda calculus program with de Bruijn indices",
>   "blc\tencode as binary lambda calculus bits",
>   "Blc\tencode as Binary lambda calculus bytes",
>   "size\tshow size in bits",
>   "help\tshow this text"
>   ]
