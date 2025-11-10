> module AIT(Encodeable(..),reduce,optimize,strict,subst,occurs,noccurs,contracts,expands,reduct,uni,usage) where
> import Lambda
> import Data.List(unfoldr,foldl',group,sortBy)
> import Data.Char(chr,ord,intToDigit)
> import Data.Function
> import qualified Data.DList as DL
> import Data.Array.Unboxed
> import Control.Applicative
> import Control.Monad.Writer
> import Numeric

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

Size in bits with variables using Levenshtein coding
https://en.wikipedia.org/wiki/Levenshtein_coding
0, 10, 1100, 1101, 1110000, 1110001, 1110010, 1110011, 11101000, 11101001, ...

map (size .DBVar) [0..17] = [2, 3, 4, 5, 6, 7, 8, 9,10,11,12,13,14,15,16,17,18,19]
map (size2.DBVar) [0..17] = [2, 3, 5, 5, 8, 8, 8, 8, 9, 9, 9, 9, 9, 9, 9, 9,13,13]
                                  +1    +2 +1    -1 -1 -2 -3 -4 -5 -6 -7 -8 -5 -6 

> encode2 :: DB -> String
> encode2 z = prebin z "" where
>   prebin (DBVar 0) s = '1':'0':s
>   prebin (DBVar i) s | i>0 = ('1':) . prebin (DBVar (length (showi "") - 1)) . tail . showi $ s where
>     showi = showBin i
>   prebin (DBVar   _) _ = error "Negative de-Bruijn index"
>   prebin (DBLam   e) s = '0':'0':(prebin e s)
>   prebin (DBApp x y) s = '0':'1':(prebin x (prebin y s))

> size2 :: DB -> Int
> size2 = length . encode2

Size in bits with Mateusz context sensitive encoding for closed lambda terms
which skips the inital 0 bit on top level LAM/APP 
and the final 1 bit on variable binding outermost lambda

> encode0 :: DB -> String
> encode0 z = prebin 0 z "" where
>   prebin :: Int -> DB -> String -> String
>   prebin 0 (DBVar _) _ = error "bad index"
>   prebin n (DBVar 0) s = if n==1 then '1':s else '1':'0':s
>   prebin n (DBVar i) s = '1':(prebin (n-1) (DBVar (i-1)) s)
>   prebin n (DBLam   e) s = (if n==0 then id else ('0':)) $ '0':(prebin (n+1) e s)
>   prebin n (DBApp x y) s = (if n==0 then id else ('0':)) $ '1':(prebin n x (prebin n y s))

> size0 :: DB -> Int
> size0 = length . encode0

> {-- adaption for alternate encoding as used in int4.lam
>   prebin (DBVar i) s | i>0 = '1':'1':(prebin (DBVar (i-1)) s)
>   prebin l@(DBLam   e) s = succpref ++ '0':'0':(prebin se s) where
>     mf = minFree 0 l
>     succpref = trace ("mf "++show l++" ="++show mf) $ if mf > 0 then replicate (2*mf) '+' else ""
>     se = if mf > 0 then adjust mf 1 e else e
>   prebin a@(DBApp x y) s = succpref ++ ('0':'1':(prebin sx (prebin sy s))) where
>     mf = minFree 0 a
>     succpref = if mf > 0 then replicate (2*mf) '+' else ""
>     sx = if mf > 0 then adjust mf 0 x else x
>     sy = if mf > 0 then adjust mf 0 y else y
>   adjust by n e@(DBVar j) | j >= n = DBVar (j-by)
>                        | otherwise = e
>   adjust by n (DBLam body) = DBLam (adjust by (succ n) body)
>   adjust by n (DBApp fun arg) = DBApp (adjust by n fun) (adjust by n arg)
>   minFree :: Int -> DB -> Int
>   minFree n (DBVar i) = if i < n then -1 else i-n
>   minFree n (DBLam e) = minFree (n+1) e
>   minFree n (DBApp fun arg) = posmin (minFree n fun) (minFree n arg)
>   posmin (-1) x = x
>   posmin x (-1) = x
>   posmin x y = min x y
> --}

Size in bits of an expression, assuming no free variables

> instance Encodeable CL where
>   encode z = prebin z "" where
>     prebin (CVar _) _ = error "can't encode variables"
>     prebin CombK s = '0':'0':s
>     prebin CombS s = '0':'1':s
>     prebin CombI s = "11010000" ++ s         -- S K K
>     prebin CombB _ = error "can't encode B"
>     prebin CombC _ = error "can't encode C"
>     prebin CombR _ = error "can't encode R"
>     prebin (CApp x y) s = '1':(prebin x (prebin y s))

> encodeOK :: CL -> String
> encodeOK z = prebin z "" where
>   prebin (CVar _) _ = error "can't encode variables"
>   prebin CombI s = "0010" ++ s
>   prebin CombK s = "0000110" ++ s
>   prebin CombB s = "0000000111100111010" ++ s
>   prebin CombC s = "0000000101111010110" ++ s
>   prebin CombS s = "00000001011110100111010" ++ s
>   prebin CombR s = "0000000101110101110" ++ s
>   prebin (CApp x y) s = '0':'1':(prebin x (prebin y s))

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

Does variable occur in term?

> occurs :: Int -> DB -> Bool
> occurs n (DBLam body) = occurs (n+1) body
> occurs n (DBApp fun arg) = occurs n fun || occurs n arg
> occurs n (DBVar i) = i == n

Number of time variable occurs in term

> noccurs :: Int -> DB -> Int
> noccurs n (DBLam body) = noccurs (n+1) body
> noccurs n (DBApp fun arg) = noccurs n fun + noccurs n arg
> noccurs n (DBVar i) = if i == n then 1 else 0

> single :: DB -> [(DB, Int)]
> single x = [(x, size x)]

Optimize an expression; repeatedly contract redexes that reduce in size
Return list of candidates paired with their size; the head is the shortest
and remaining ones (up to a maximum of width) are larger by less than the function's first argument,
i.e. the slack.
The second argument n is the number of non-decreasing in size beta reductions considered.

> optimize :: Int -> Int -> Int -> DB -> [(DB, Int)]
> optimize width slack = opt where
>   opt :: Int -> DB -> [(DB, Int)]
>   opt _ v@(DBVar i) = [(v, (2+i))]

eta rule : optimize \x. f x, where x is not free in f, as f

>   opt n (DBLam body) = do
>     (b,_) <- opt n body
>     single $ case b of
>       (DBApp fun (DBVar 0)) | not (occurs 0 fun) -> subst 0 undefined fun
>       _                                          -> DBLam b
>   opt n (DBApp fun arg) = let
>       funs = opt n fun
>       args = opt n arg
>       prune = pr . sortBy (compare `on` snd)
>       pr [] = error "Nothing to prune"
>       -- could allow more slack for application on variable, to allow O8 = \_.C3 C2
>       pr (hd@(_,ts):tl) = take width . map head . group $ hd: takeWhile ((<= ts+slack) . snd) tl
>     in prune $ do
>       (fun', fs) <- funs
>       (arg', as) <- args
>       let (t, ts) = (DBApp fun' arg', 2+fs+as)
>       case fun' of
>         DBLam body -> [(t,ts) | occurs 0 body]
>           ++ [ot | let t' = subst 0 arg' body,
>                    let n' = if size t' < ts then n else n-1,
>                    n' >= 0,
>                    ot <- opt n' t']
>         _ -> [(t,ts)]

Simpleminded strictness analyzer

> strict :: Int -> DB -> Bool
> strict n (DBLam body) = strict (n+1) body
> strict n (DBApp fun _) = strict n fun
> strict n (DBVar i) = i == n

Reduction step

> reduce :: DB -> Maybe DB
> reduce (DBLam body) = reduce body >>= Just . DBLam
> reduce (DBApp (DBLam body) arg) = Just $ subst 0 arg body
> reduce (DBApp fun arg) = case reduce fun of
>                            Just f    -> Just $ DBApp f arg
>                            Nothing   -> reduce arg >>= Just. DBApp fun
> reduce (DBVar _) = Nothing

Reduct

> reduct :: DB -> Maybe DB
> reduct (DBLam body) = reduct body
> reduct a@(DBApp (DBLam _) _) = Just a
> reduct (DBApp fun arg) = reduct fun <|> reduct arg
> reduct (DBVar _) = Nothing

Safe reductions (guaranteed to reach normal form)

> contracts :: DB -> Bool
> contracts x = case reduct x of
>               Just t@(DBApp (DBLam body) arg) -> size (subst 0 arg body) < size t
>               _ -> True

Of interest to Busy Beaver

> expands :: DB -> Bool
> expands x = x == fst (head (optimize 1 0 1 x)) && case reduct x of
>               Just t@(DBApp (DBLam body) arg) -> size (subst 0 arg body) > size t
>               _ -> False

Bitstring functions -----------------------------------------------------

> cons :: LC Id -> LC Id -> LC Id
> cons x y = Lam (Id "z") $ Var (Id "z") `App` x `App` y

> lcTrue :: LC Id
> lcTrue  = Lam (Id "x") $ Lam (Id "y") $ Var (Id "x")

> lcFalse :: LC Id
> lcFalse = Lam (Id "x") $ Lam (Id "y") $ Var (Id "y")

> bittoLC :: Char -> LC Id
> bittoLC '0' = lcTrue;
> bittoLC '1' = lcFalse;
> bittoLC _ = error "Character is not 0 or 1"

> bitstoLC :: LC Id -> String -> LC Id
> bitstoLC nil = foldr cons nil . map bittoLC

> fromByte :: Char -> String
> fromByte = reverse . take 8 . unfoldr (\x->Just(intToDigit(x`mod`2),x`div`2)) . ord

> bytestoLC :: LC Id -> String -> LC Id
> bytestoLC nil = foldr cons nil . map (bitstoLC lcFalse . fromByte)

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
> boxChar alt a = boxer 0 1 where
>   (_,(y,x)) = bounds a
>   boxer :: Int -> Int -> String
>   boxer j i | i>x = if j<y' then boxer (j+1) 1 else [] where
>                        y' = if alt then y else y-1
>   boxer j i = boxVar (a!(j,i-1)) (a!(j,i)) (a!(j,i+1)) (j<y && a!(j+1,i)=='|') : boxMid (a!(j,i+2)) : boxer j (i+4) where
>     boxMid '_' = '─'
>     boxMid c = c
>     boxVar  _  ' '  _  _     = ' '
>     boxVar '_' '|' '_' _     = '┼'
>     boxVar ' ' '|' ' ' _     = '│'
>     boxVar '_' '|' ' ' True  = '┤'
>     boxVar '_' '|' ' ' False = '┘'
>     boxVar ' ' '|' '_' True  = '├'
>     boxVar ' ' '|' '_' False = '└'
>     boxVar  _  '_'  _  True  = '┬'
>     boxVar  _  '_'  _  False = '─'
>     boxVar  _   c   _  _     = error $ "Unexpected char" ++ [c]

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
>   machine = \inp -> foldl' (\p -> App p . bitstoLC lcFalse) (App prog inp) args
>   tex = concatMap (\c -> if c=='\\' then "\\lambda " else [c])
>   html = concatMap (\c -> if c=='\\' then "\0955 " else [c])
>   nl = (++ "\n")
>   opt = fst . head . optimize 57 2 1
>   -- increasing slack to 3 requires ALSO increasing width to 937 for loader
>   -- increasing slack to 4 requires ALSO increasing width to 4105 for loader
>   boxdiag b = boxChar b . diagram b
>  in case op of
>   "run"     -> nl .   bshow . nf . toDB . machine $  bitstoLC lcFalse input
>   "runf"    -> nl .    show . nf . toDB . machine $  bitstoLC lcFalse input
>   "runO"    -> nl .   bshow . nf . toDB . machine $  bitstoLC (error "Omega") input
>   "run8"    -> nl .   bshow . nf . toDB . machine $ bytestoLC lcFalse input
>   "print"   -> nl .                show             $ prog
>   "db"      -> nl .                show      . toDB $ prog
>   "nf"      -> nl .                show . nf . toDB $ prog
>   "hnf"     -> nl .               show . hnf . toDB $ prog
>   "nf_size" -> nl .         show . size . nf . toDB $ prog
>   "comb_nf" -> nl .   show . strongCL . toCL . toDB $ prog
>   "comb"    -> nl .        show . toCL . opt . toDB $ prog
>   "combOK"  -> nl .      show . toCLOK . opt . toDB $ prog
>   "blcOK"   ->       encodeOK . toCLOK . opt . toDB $ prog
>   "bcw"     -> nl .       show . toBCW . opt . toDB $ prog
>   "bcl"     ->           encode . toCL . opt . toDB $ prog
>   "diagram" -> elems   . diagram False . opt . toDB $ prog
>   "Diagram" -> elems   . diagram  True . opt . toDB $ prog
>   "boxchar" ->           boxdiag False . opt . toDB $ prog
>   "Boxchar" ->           boxdiag  True . opt . toDB $ prog
>   "pbm"     -> toPBM   . diagram False . opt . toDB $ prog
>   "Pbm"     -> toPBM   . diagram  True . opt . toDB $ prog
>   "tex"     -> nl .         tex . show . opt . toDB $ prog
>   "nfhtml"  -> nl .         html . show . nf . toDB $ prog
>   "html"    -> nl .        html . show . opt . toDB $ prog
>   "printlc" -> nl .               show . opt . toDB $ prog
>   "blc"     ->                  encode . opt . toDB $ prog
>   "blc2"    ->                 encode2 . opt . toDB $ prog
>   "size"    -> nl .       show . size  . opt . toDB $ prog
>   "size2"   -> nl .       show . size2 . opt . toDB $ prog
>   "size0"   -> nl .       show . size0 . opt . toDB $ prog
>   "help"    -> unlines usage
>   a         -> "Action " ++ a ++ " not recognized.\n"

> usage :: [String]
> usage = [
>   "Usage: blc action progfile [args]...",
>   "run\trun given program applied to standard input bits and args",
>   "run8\trun given program applied to standard input bytes and args",
>   "print\tshow program",
>   "nf\tshow normal form",
>   "hnf\tshow head normal form",
>   "nf_size\tshow size of normal form",
>   "comb_nf\tnormal form through SK reduction",
>   "comb\tshow translation to combinatory logic",
>   "combOK\tshow Oleg Kiselyov's translation to combinatory logic",
>   "bcw\tencode in BCW combinators",
>   "bcl\tencode in binary combinatory logic",
>   "diagram\tshow ascii diagram",
>   "Diagram\tshow alternative ascii diagram",
>   "boxchar\tshow boxdrawing character diagram",
>   "Boxchar\tshow boxdrawing character alternative diagram",
>   "pbm\tshow diagram in portable bitmap format",
>   "Pbm\tshow alternative diagram in portable bitmap format",
>   "tex\tshow program as TeX",
>   "nfhtml\tshow normal form as html",
>   "html\tshow program as html",
>   "printlc\tshow lambda calculus program with de Bruijn indices",
>   "blc\tencode as binary lambda calculus bits",
>   "blc2\tencode as Levenshtein binary lambda calculus bits",
>   "size\tshow size in bits",
>   "size2\tshow size with levenshtein encoded de bruijn indices",
>   "size0\tshow size with Mateusz encoding",
>   "help\tshow this text"
>   ]
