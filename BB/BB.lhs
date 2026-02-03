Look for BLC busy beavers.
Author: Bertram Felgenhauer / John Tromp
 
> import System.IO
> import Debug.Trace
> import Data.List
> import Data.Char
> import Data.Bits
> import Control.Applicative
> import Data.Char(isAlphaNum)
> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text, (<>), (<+>), parens)
> import Text.ParserCombinators.ReadP
> import qualified Data.Set as S
 
terms with de Bruijn indices (internal: starting at 0)
note: Bot marks useless subterms that do not contribute to the normal form

> data L = Var !Int | App L L | Abs L | Bot
>     deriving (Eq, Ord)

> instance Read L where
>   readsPrec _ s
>     | '(':s <- s, [(n,s)] <- reads s, ')':s <- s = [(Var (n-1),s)]
>     | c:s <- s, isDigit c = [(Var (digitToInt c-1),s)]
>     | '^':s <- s, [(t,s)] <- reads s = [(Abs t,s)]
>     | '`':s <- s, [(t,s)] <- reads s, [(u,s)] <- reads s = [(App t u,s)]

generate terms of size n with all variables < v

> gen :: Int -> Int -> [L]
> gen v n =
>     [Var (n-2) | n >= 2, n-2 < v] ++
>     [App a b | i <- [2..n-4], a <- gen v i, b <- gen v (n-2-i)] ++
>     [Abs a | n >= 4, a <- gen (v+1) (n-2)]

> size :: L -> Int
> size (Var i)   = i + 2
> size (App a b) = 2 + size a + size b
> size (Abs a)   = 2 + size a
> size Bot       = 1

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

data structure for Past Head Terms  with limited Capacity for sum size

> data PHT = PHT L (S.Set L) Int deriving (Show)

> insertPHT :: L -> PHT -> Maybe PHT
> insertPHT r (PHT t s c) = let c' = c - size r in if c' < 0
>   then trace ("-- TODO: " ++ prnt t) Nothing
>   else Just $ PHT t (r `S.insert` s) c'

> elemPHT :: L -> PHT -> Bool
> elemPHT r (PHT _ s _) = r `S.member` s

try to find normal form; Nothing means either no normal form or a TODO alert

> normalForm :: Int -> L -> Maybe L
> normalForm lim a0 = {-- trace ("nf0 " ++ prnt a0) $ --} nf0 a0 where
>   nf0 (Abs a) = Abs <$> nf0 a
>   nf0 a = nf False 0 (PHT a0 S.empty lim) a >>= Just . snd

The following example shows why the set of previous redexes must be reset
when switching from nf to whnf reduction. The redex in nf leads to reduction
in the argument of the body function, where the same redex is now applied
to a term K y, so that reduction need no longer proceed into the body.

(\x. x x) (\x\y. y (x x (\_.y)))
--------------------------------
(\x\y. y (x x (\_.y))) (\x\y. y (x x (\_.y)))
---------------------------------------------
\y. y ( (\x\y. y (x x (\_.y))) (\x\y. y (x x (\_.y))) (\_.y))
        ---------------------------------------------
\y. y ( (\y. y ((\x\y. y (x x (\_.y))) (\x\y. y (x x (\_.y))) (\_.y))) (\_.y))
        ---------------------------------------------------------------------
\y. y (                                                                    y))

reduce to (weak head if weak) normal form with given minimum index of what can be considered free variable f
and list of previous redexes s that led to current term and whose reoccurance would indicate a loop

> nf :: Bool -> Int -> PHT -> L -> Maybe (Int, L)
> nf weak f p@(PHT a0 s c) (App a_ b_) = do
>   (c,a) <- nf True f (if weak then p else PHT a0 S.empty c) a_
>   let { r@(App ra _) = botFree 0 ab; ab = App a b; b = simplify b_ }
>   p'@(PHT _ s c) <- insertPHT r (PHT a0 s c)
>   if noNF f ab || elemPHT ra p then Nothing else case a of
>     Abs a -> if elemPHT r p then Nothing else do
>       nf weak f p' (subst 0 a b)
>     _ -> if weak then Just (c,ab) else do
>       (c,a') <- nf weak f p' a
>       (c,b') <- nf weak f (PHT a0 s c) b
>       Just (c, App a' b')
> nf weak f p (Abs a) | not weak = nf weak (f+1) p a >>= (\(c,t) -> Just (c, Abs t))
> nf _ _ (PHT _ _ c) t           = Just (c,t)

> noNF :: Int -> L -> Bool
> noNF f a = let is = bit f in isB is a || isB23 is a where -- bit f acts as sentinel

various terms W that allow W W -> H[W W] for strict head context H,
leading to infinite head reductions

> isW :: Int -> L -> Bool
> isW is (Var i) = istest is i
> isW is (Abs a) = isB (2*is+1) a
> isW _ _ = False

> isB :: Int -> L -> Bool
> isB is (App a b) | isF is a = isB is b
> isB is (App a@(App _ _) b) = isB is a
> isB is (App a b) = isW is a && (isW is b || isB is b)
> isB is (Abs a) = isB (2*is) a
> isB _ a = False

> istest :: Int -> Int -> Bool
> istest is i = is `testBit` i && is >= bit (i+1)

does a term have a free variable in head position?

> isF :: Int -> L -> Bool
> isF is (Var i) = bit (i+1) > is
> isF is (App a _) = isF is a
> isF _ _ = False

various terms W that allow W _ W -> H[W _ W] for strict head context H,
leading to infinite head reductions

> isW3a :: Int -> L -> Bool
> isW3a is (Var i) = istest is i
> isW3a is (Abs a) = isB3 (2*is+1) a
> isW3a _ _ = False

> isB23 :: Int -> L -> Bool
> isB23 is (App a b) = isW3a is a && (isW3b is b || isB3 is b)
> isB23 _  _ = False

> isW3b :: Int -> L -> Bool
> isW3b is (Var i) = istest is i
> isW3b is (Abs (Abs a)) = isB3 (4*is+1) a
> isW3b _ _ = False

> isB3 :: Int -> L -> Bool
> isB3 is (App a b) | isF is a = isB3 is b
> isB3 is (App a@(App (App _ _)  _) b) = isB3 is a
> isB3 is (App (App a _) b) = isW3b is a && (isW3b is b || isB3 is b)
> isB3 is (Abs a) = isB3 (2*is) a
> isB3 _  _ = False

simplification

> simplify :: L -> L
> simplify = simp where
>   simp (Abs a) = Abs (simp a)
>   simp (App a b) = case simp a of
>     Abs a | (Var _) <- b                    -> simp (subst 0 a b)
>     Abs a | a <- simpA a b, noccur 0 a <= 1 -> simp (subst 0 a b)
>     a -> App a (simp b)
>   simp t = t

>     -- simplify a based on its argument
>   simpA a (Abs b)
>     | noccur 0 b == 0 = simpE 0 a -- \b erases first argument
>     | b == Var 0      = simpI 0 a -- \b is id = \1
>   simpA a _ = a

>   -- the first argument of variable i is not needed, so replace it by Bot
>   simpE i (App (Var j) b)
>     | i == j = App (Var j) Bot
>   simpE i (App a b) = App (simpE i a) (simpE i b)
>   simpE i (Abs a) = Abs (simpE (i+1) a)
>   simpE _ a = a

>   -- variable i will be substituted by id = \1
>   simpI i (App (Var j) b)
>     | i == j = simpI i b
>   simpI i (App a b) = App (simpI i a) (simpI i b)
>   simpI i (Abs a) = Abs (simpI (i+1) a)
>   simpI _ a = a

stop at 36 to avoid resource killing terms like the 37 bit

> wtf = read "`^`1^`2`2^2^``111" :: L -- (\1 (\2 (2 (\2)))) (\1 1 1)

> main :: IO ()
> main = do
>  hSetBuffering stdout LineBuffering
>  mapM_ print [f n | n <- [0..36]] where
>    f n = (n, maxsize, maxt, nNF) where
>      nfs = [(size nf,P t) | t <- gen 0 n, Just nf <- [normalForm 42000000 t]]
>      (maxsize, maxt, nNF) = foldl' maxicnt (0,P Bot,0) nfs
>      maxicnt (ms,mt,n) st = (ms',mt',n+1) where (ms',mt') = max (ms,mt) st

printing

> instance Show L where
>   show (Var i) = showParen (i < 0 || i > 8) (shows $ if i < 0 then i else i+1) ""
>   show (Abs t) = "^" ++ show t
>   show (App s t) = "`" ++ show s ++ show t
>   show Bot = "_"

alternative printing

> newtype P = P L deriving (Eq, Ord)

A ReadP parser for De Bruijn term

> instance Read P where
>   readsPrec _ = map (\(l,s)->(P l,s)) . readP_to_S pL

> pL, pLAtom, pLVar, pLLam, pLApp :: ReadP L
> pL = pLLam +++ pLApp

> pLVar = do
>   skipSpaces
>   v <- readS_to_P (readsPrec 9)
>   return $ Var (v-1)

> schar :: Char -> ReadP ()
> schar c = do skipSpaces; _ <- char c; return ()

> pLLam = do
>   schar '\\'
>   e <- pL
>   return $ Abs e

> pLApp = do
>   es <- many1 pLAtom
>   return $ foldl1 App es

> pLAtom = pLVar +++ (do schar '('; e <- pL; schar ')'; return e)

> instance Show P where
>   showsPrec _ (P a) = prs a

> prs :: L -> ShowS
> prs = go 0 where
>   go p (Var i)   = shows (i+1)
>   go p (App a b) = showParen (p > 1) $ go 1 a . (' ':) . go 2 b
>   go p (Abs a)   = showParen (p > 0) $ ('\\':) . go 0 a
>   go p Bot       = ('_':)

> prnt :: L -> String
> prnt a = prs a ""
