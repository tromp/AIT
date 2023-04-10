Look for BLC busy beavers while bounding halting probability
Author: Bertram Felgenhauer / John Tromp
 
> import System.IO
> import Debug.Trace
> import Data.List hiding (insert)
> import Data.Char
> import Data.Bits
> import Data.Word
> import Data.Set hiding (size, foldr)
> import Control.Applicative
> import Control.Exception.Assert
 
terms with de Bruijn indices (internal: starting at 0)
note: Bot marks useless subterms that do not contribute to the normal form

> data L = Var !Int | App L L | Abs L | Bot
>     deriving (Eq, Ord)

> instance Read L where
>     readsPrec _ s
>         | '(':s <- s, [(n,s)] <- reads s, ')':s <- s = [(Var (n-1),s)]
>         | c:s <- s, isDigit c = [(Var (digitToInt c-1),s)]
>         | '^':s <- s, [(t,s)] <- reads s = [(Abs t,s)]
>         | '`':s <- s, [(t,s)] <- reads s, [(u,s)] <- reads s = [(App t u,s)]

> cons :: L -> L -> L
> cons x xs = Abs (App (App (Var 0) x) xs)

> omega = let dbl = Abs (App (Var 0) (Var 0)) in App dbl dbl

generate n bits data extensions terminated by t for given program with no prefix in given Set

> genBits :: Set Word64 -> Word64 -> Int -> L -> [(Word64,L)]
> genBits set prog _ _ | member prog set = []
> genBits _  prog 0 t = [(prog,t)]
> genBits set prog n t = do
>     bit <- [0,1]
>     let progb = (prog `shiftL` 1) .|. (fromIntegral bit)
>     let bt = Abs (Abs (Var (1-bit)))
>     (prg,bits) <- genBits set progb (n-1) t
>     return (prg, cons bt bits)

generate progs of size n with no prefix in set

> gen2 :: Set Word64 -> Int -> [(Word64, L)]
> gen2 set n = do
>     (code,len,t) <- gen 0 n
>     (prog,bits) <- genBits set (bit len .|. code) (n-len) (Var (998))
>     return $ (prog, App t bits)

generate terms within v lambda binders of size up to n

> gen :: Int -> Int -> [(Word64,Int,L)]
> gen v n =
>     [(bit (i+2) - 2, i+2, Var i) | i <- [0..min (n-2) (v-1)]] ++
>     [((((bit la .|. wa) `shiftL` lb) .|. wb), 2+la+lb, App a b) | n >= 6, (wa,la,a) <- gen v (n-4), (wb,lb,b) <- gen v (n-2-la)] ++
>     [(w, 2+la, Abs a) | n >= 4, (w,la,a) <- gen (v+1) (n-2)]

> size :: L -> Int
> size (Var i)   = i + 2
> size (App a b) = 2 + size a + size b
> size (Abs a)   = 2 + size a

> subst :: Int -> L -> L -> L
> subst i (Var j)   c = if i == j then c else Var (if j > i then j-1 else j)
> subst i (App a b) c = App (subst i a c) (subst i b c)
> subst i (Abs a)   c = Abs (subst (i+1) a (incv 0 c))
> subst i Bot       _ = Bot

> incv :: Int -> L -> L
> incv i (Var j)   = Var (if i <= j then j+1 else j)
> incv i (App a b) = App (incv i a) (incv i b)
> incv i (Abs a)   = Abs (incv (i+1) a)
> incv i Bot       = Bot

number of occurrences of a variable

> noccur :: Int -> L -> Int
> noccur i (Var j)   = if i == j then 1 else 0
> noccur i (App a b) = noccur i a + noccur i b
> noccur i (Abs a)   = noccur (i+1) a
> noccur i Bot       = 0

replace free variables (of a redex) by bottom

> botFree :: Int -> L -> L
> botFree i (Var j)   = if j >= i then Bot else Var j
> botFree i (App a b) = App (botFree i a) (botFree i b)
> botFree i (Abs a)   = Abs (botFree (i+1) a)
> botFree _ Bot       = Bot

> strict :: L -> Bool
> strict (Abs a) = str 0 a where
>   str i (Abs a) = str (i+1) a
>   str i (Var j) = i == j
>   str i (App a _) = str i a
> strict _ = False

> data FreeNess = None | Applied | Unapplied deriving (Eq, Show)

> freeness :: Int -> L -> FreeNess
> freeness i (Var j)   = if j < i then None else Unapplied
> freeness i (App a b) = case freenessA i a of
>   None -> freeness i b
>   Applied -> Applied
>   Unapplied -> if freeness i b == Applied then Applied else Unapplied
> freeness i (Abs a)   = freeness (i+1) a
> freeness _ Bot       = None

> freenessA :: Int -> L -> FreeNess
> freenessA i (Var j)   = if j < i then None else Applied
> freenessA i (App a b) = case freenessA i a of
>   None -> freeness i b
>   Applied -> Applied
>   Unapplied -> if freeness i b == Applied then Applied else Unapplied
> freenessA i (Abs a)   = error $ "applied " ++ show (Abs a)  ++ " in App"
> freenessA _ Bot       = None

trouble terms

> todo :: L -> Maybe L
> todo a = trace ("-- TODO: " ++ pr a) Nothing

guaranteed normal form

> gnf :: L -> L
> gnf (App a b) = case gnf a of
>   Abs a -> gnf (subst 0 a b)
>   a -> App a (gnf b)
> gnf (Abs a) = Abs (gnf a)
> gnf a = a

try to find normal form; Nothing means no normal form
(logs cases where it bails out; should really be in IO...)

> normalForm :: L -> Maybe L

size 34 (\1 1 1 1) C2 and (\1 (1 1) 1) C2 

> normalForm a@(App (Abs (App (App (App (Var 0) (Var 0)) (Var 0)) (Var 0))) (Abs (Abs (App (Var 1) (App (Var 1) (Var 0)))))) = Just (gnf a)
> normalForm a@(App (Abs (App (App (Var 0) (App (Var 0) (Var 0))) (Var 0))) (Abs (Abs (App (Var 1) (App (Var 1) (Var 0)))))) = Just (gnf a)

size 35 (\1 1 1) C3 and (\1 (1 1) 1) (\\2 2 (1 2))

> normalForm a@(App (Abs (App (App (Var 0) (Var 0)) (Var 0))) (Abs (Abs (App (Var 1) (App (Var 1) (App (Var i) (Var j))))))) | i+j==1 = todo a

size 36 (\1 1) (\1 (1 (\\2 (2 1)))) and \(\1 1 1 1) C2 and \(\1 (1 1) 1) C2 

> normalForm a@(App (Abs (App (Var 0) (Var 0))) (Abs (App (Var 0) (App (Var 0) (Abs (Abs (App (Var 1) (App (Var 1) (Var 0))))))))) = todo a
> normalForm a@(Abs (App (Abs (App (App (App (Var 0) (Var 0)) (Var 0)) (Var 0))) (Abs (Abs (App (Var 1) (App (Var 1) (Var 0))))))) = Just (gnf a)
> normalForm a@(Abs (App (Abs (App (App (Var 0) (App (Var 0) (Var 0))) (Var 0))) (Abs (Abs (App (Var 1) (App (Var 1) (Var 0))))))) = Just (gnf a)

size 37 (\1 1) (\1 (1 (\\2 (3 1)))) and (\1 1) (\1 (1 (\\3 (2 1)))) and (\1 1) (\1 (\2 (1 (2 (\2))))) and (\1 1) (\1 (\2 (2 (\2) 1))) and (\1 1) (\1 (\\3 (2 1)) 1) and \(\1 1) (\2 (1 (\2 (2 1)))) and \ size 35 ones and what is going on

> normalForm a@(App (Abs (App (Var 0) (Var 0))) (Abs (App (Var 0) (App (Var 0) (Abs (Abs (App (Var 1) (App (Var 2) (Var 0))))))))) = todo a
> normalForm a@(App (Abs (App (Var 0) (Var 0))) (Abs (App (Var 0) (App (Var 0) (Abs (Abs (App (Var 2) (App (Var 1) (Var 0))))))))) = todo a
> normalForm a@(App (Abs (App (Var 0) (Var 0))) (Abs (App (Var 0) (Abs (App (Var 1) (App (Var 0) (App (Var 1) (Abs (Var 1))))))))) = todo a
> normalForm a@(App (Abs (App (Var 0) (Var 0))) (Abs (App (Var 0) (Abs (App (Var 1) (App (App (Var 1) (Abs (Var 1))) (Var 0))))))) = todo a
> normalForm a@(App (Abs (App (Var 0) (Var 0))) (Abs (App (App (Var 0) (Abs (Abs (App (Var 2) (App (Var 1) (Var 0)))))) (Var 0)))) = todo a
> normalForm a@(Abs (App (Abs (App (Var 0) (Var 0))) (Abs (App (Var 1) (App (Var 0) (Abs (App (Var 1) (App (Var 1) (Var 0))))))))) = todo a
> normalForm a@(Abs (App (Abs (App (App (Var 0) (Var 0)) (Var 0))) (Abs (Abs (App (Var 1) (App (Var 1) (App (Var i) (Var j)))))))) | i+j==1 = todo a

> -- normalForm a0 =  trace ("nf0 " ++ pr a0) nf0 a0 where
> normalForm a0 =  nf0 a0 where

>   nf0 (Abs a) = Abs <$> nf0 a
>   nf0 a = nf 0 [] a

normal form with given minimum index of what can be considered free variable f
and list of previous redexes s that led to current term and whose reoccurance would indicate a loop

>   nf f s (Abs a) = Abs <$> nf (f+1) s a
>   nf f s r@(App a b) = do
>     a <- nf f s a
>     b <- if strict a then nf f s b else Just (simplify b)
>     let r = botFree 0 (App a b)
>     if noNF f (App a b) then Nothing else case a of
>         Abs a
>             | r `elem` s   -> Nothing
>             | length s > 28 -> todo a0
>             | otherwise    -> nf f (r:s) (subst 0 a b)
>         _ -> do
>             nf f s b >>= Just . App a
>   nf _ _ t = Just t

>   noNF :: Int -> L -> Bool
>   noNF f a = let is = bit f in isB is a || isB3 is a where

various terms W that allow W W -> H[W W] for strict head context H,
leading to infinite head reductions

>   isW :: Int -> L -> Bool
>   isW is (Var i) = istest is i
>   isW is (Abs a) = isB (2*is+1) a
>   isW _ Bot = True
>   isW _ _ = False

>   isB :: Int -> L -> Bool
>   isB is (App a@(App _ _) b) = isB is a || (isF is a && isB is b)
>   isB is (App a@(Var _) b) | isF is a = isB is b
>   isB is (App a b) = isW is a && (isW is b || isB is b)
>   isB is (Abs a) = isB (2*is) a
>   isB _ Bot = True
>   isB _ a = False

>   istest :: Int -> Int -> Bool
>   istest is i = is `testBit` i && is >= bit (i+1)

>   isF :: Int -> L -> Bool
>   isF is (Var i) = bit (i+1) > is
>   isF is (App a _) = isF is a
>   isF _ _ = False

various terms W that allow W _ W -> H[W _ W] for strict head context H,
leading to infinite head reductions

>   isW3 :: Int -> L -> Bool
>   isW3 is (Var i) = istest is i
>   isW3 is (Abs a) = isB3 (2*is+1) a
>   isW3 _ Bot = True
>   isW3 _ _ = False

>   isB3 :: Int -> L -> Bool
>   isB3 is (App a@(App (App _ _)  _) b) = isB3 is a || (isF is a && isB3 is b)
>   isB3 is (App (App a _) b) = (isW3 is a && (isW3 is b || isB3 is b)) || (isF is a && isB3 is b)
>   isB3 is (App a (Abs b)) = (isW3 is a && (isW3 (2*is) b || isB3 (2*is) b)) || (isF is a && isB3 (2*is) b)
>   isB3 is (App a@(Var _) b) = isF is a && isB3 is b
>   isB3 is (Abs a) = isB3 (2*is) a
>   isB3 _  Bot = True
>   isB3 _  _ = False

simplification

> simplify :: L -> L
> simplify = simp where
>     simp (Abs a) = Abs (simp a)
>     simp (App a b) = case simp a of
>         Abs a | (Var _) <- b                    -> simp (subst 0 a b)
>         Abs a | a <- simpA a b, noccur 0 a <= 1 -> simp (subst 0 a b)
>         a -> App a (simp b)
>     simp t = t

>     -- simplify a based on its argument
>     simpA a (Abs b)
>         | noccur 0 b == 0 = simpE 0 a -- \b erases first argument
>         | b == Var 0      = simpI 0 a -- \b is id = \1
>     simpA a _ = a

>     -- the first argument of variable i is not needed, so replace it by Bot
>     simpE i (App (Var j) b)
>         | i == j = App (Var j) Bot
>     simpE i (App a b) = App (simpE i a) (simpE i b)
>     simpE i (Abs a) = Abs (simpE (i+1) a)
>     simpE _ a = a

>     -- variable i will be substituted by id = \1
>     simpI i (App (Var j) b)
>         | i == j = simpI i b
>     simpI i (App a b) = App (simpI i a) (simpI i b)
>     simpI i (Abs a) = Abs (simpI (i+1) a)
>     simpI _ a = a

> mapmax :: (Word64, L, L) -> (Int, L, Set Word64) -> (Int, L, Set Word64)
> mapmax (p,t,a) (mx, mt, set) =
>   let
>     lt = size t
>     set' = insert p set
>   in case freeness 0 t of
>     None ->  if lt > mx then (lt, a, set') else (mx, mt, set')
>     Applied -> (mx, mt, set)
>     otherwise -> (mx, mt, set')

> go :: Int -> Set Word64 -> IO ()
> go n set = do
>   let (mx, a, set') = foldr mapmax (0,Bot,set) [(p,t,a) | (p,a) <- gen2 set n, Just t <- [normalForm a]]
>   print (n, mx, P a)
>   go (n+1) set'

> main :: IO ()
> main = do
>     hSetBuffering stdout LineBuffering
>     go 0 Data.Set.empty

printing

> instance Show L where
>     show (Var i) = showParen (i < 0 || i > 8) (shows $ if i < 0 then i else i+1) ""
>     show (Abs t) = "^" ++ show t
>     show (App s t) = "`" ++ show s ++ show t
>     show Bot = "_"

alternative printing

> newtype P = P L
>     deriving (Eq, Ord)

> instance Show P where
>     showsPrec _ (P a) = prs a

> prs :: L -> ShowS
> prs = go 0 where
>     go p (Var i)   = shows (i+1)
>     go p (App a b) = showParen (p > 1) $ go 1 a . (' ':) . go 2 b
>     go p (Abs a)   = showParen (p > 0) $ ('\\':) . go 0 a
>     go p Bot       = ('_':)

> pr :: L -> String
> pr a = prs a ""
