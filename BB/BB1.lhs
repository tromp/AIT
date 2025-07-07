Look for BBλ_1 busy beavers.
Author: Bertram Felgenhauer / John Tromp
 
> import System.IO
> import Debug.Trace
> import Data.List
> import Data.Char
> import Data.Bits
> import Control.Applicative
> import Control.Monad
> import Data.Char(isAlphaNum)
> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text, (<>), (<+>), parens)
> import Text.ParserCombinators.ReadP
 
> bb0 :: Integer -> Integer
> bb0 1 = 0
> bb0 2 = 0
> bb0 3 = 0
> bb0 4 = 4
> bb0 5 = 0
> bb0 6 = 6
> bb0 7 = 7
> bb0 8 = 8
> bb0 9 = 9
> bb0 10 = 10
> bb0 11 = 11
> bb0 12 = 12
> bb0 13 = 13
> bb0 14 = 14
> bb0 15 = 15
> bb0 16 = 16
> bb0 17 = 17
> bb0 18 = 18
> bb0 19 = 19
> bb0 20 = 20
> bb0 21 = 22
> bb0 22 = 24
> bb0 23 = 26
> bb0 24 = 30
> bb0 25 = 42
> bb0 26 = 52
> bb0 27 = 44
> bb0 28 = 58
> bb0 29 = 223
> bb0 30 = 160
> bb0 31 = 267
> bb0 32 = 298
> bb0 33 = 1812
> bb0 34 = 6+5* 2^2^2^2
> bb0 35 = 6+5* 3^3^3
> bb0 36 = 6+5* 2^2^2^3
> bb0 n = error "too large"

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

> church :: Integer -> L
> church n = Abs (Abs (it n)) where
>   it 0 = Var 0
>   it n = App (Var 1) (it (n-1))

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

test whether term has unapplied instances of free variable

> isClosed :: L -> Bool
> isClosed = closed 0 where
>   closed f (Var i) = i < f
>   closed f (Abs a) = closed (f+1) a
>   closed f (App a b) = closed f a && closed f b

> isClosed1 :: L -> Bool
> isClosed1 = closed1 0 where
>   closed1 f (Var i) = i < f
>   closed1 f (Abs a) = closed1 (f+1) a
>   closed1 f (App a b) = apclosed1 f a && closed1 f b
>   apclosed1 f (Var i) = i <= f
>   apclosed1 f (Abs a) = closed1 (f+1) a
>   apclosed1 f (App a b) = apclosed1 f a && closed1 f b

try to find normal form; Nothing means either no normal form or a TODO alert

> normalForm :: Int -> L -> Maybe L
> normalForm lim a0 = {-- trace ("nf0 " ++ pr a0) $ --} nf0 a0 where

   nf0 (Abs a) = Abs <$> nf0 a

>   nf0 a = nf False 0 [] a

reduce to (head if hnf) normal form with given minimum index of what can be considered free variable f
and list of previous redexes s that led to current term and whose reoccurance would indicate a loop

>   nf :: Bool -> Int -> [L] -> L -> Maybe L
>   nf hnf f s (Abs a) | not hnf = Abs <$> nf hnf (f+1) s a
>   nf hnf f s (App a b) = do
>     a <- nf True f (if hnf then s else []) a -- empty redex history when switching from nf to hnf
>     b <- Just (simplify b)
>     let r@(App ra _) = botFree 0 (App a b)
>     let nf' = nf hnf f (r:s)
>     if noNF f (App a b) || ra `elem` s then Nothing else case a of
>         Abs a
>             | r `elem` s   -> Nothing
>             | length s > lim -> trace ("-- TODO: " ++ pr a0) Nothing
>             | otherwise    -> nf' (subst 0 a b)
>         Var v | v==f -> oracle b
>         _ -> do
>             a' <- if hnf then Just a else nf' a
>             b' <- if hnf then Just b else nf' b
>             Just $ App a' b'
>   nf _ _ _ t = Just t
>   oracle t = do
>     nf <- nf0 t
>     guard $ isClosed nf
>     let sz = fromIntegral . size $ nf
>     if sz > 35
>       then trace ("-- TODOR: " ++ pr a0) Nothing
>       else return . church . bb0 $ sz


> noNF :: Int -> L -> Bool
> noNF f a = let is = bit f in isB is a || isB3 is a  || isB23 is a where -- bit f acts as sentinel

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

> main :: IO ()
> main = do
>     hSetBuffering stdout LineBuffering
>     mapM_ print [f n | n <- [0..22]] where
>     f n = maximum $ (n,0,P Bot) : [(n,size t,P a) | a <- gen 1 n, Just t <- [normalForm 20 a]]

printing

> instance Show L where
>     show (Var i) = showParen (i < 0 || i > 8) (shows $ if i < 0 then i else i+1) ""
>     show (Abs t) = "^" ++ show t
>     show (App s t) = "`" ++ show s ++ show t
>     show Bot = "_"

alternative printing

> newtype P = P L
>     deriving (Eq, Ord)

A ReadP parser for DeBruijn term

> instance Read P where
>   readsPrec _ = map (\(l,s)->(P l,s)) . readP_to_S pL

> pL, pLAtom, pLVar, pLLam, pLApp :: ReadP L
> pL = pLLam +++ pLApp

> pLVar = do
>     skipSpaces
>     v <- readS_to_P (readsPrec 9)
>     return $ Var (v-1)

> schar :: Char -> ReadP ()
> schar c = do skipSpaces; _ <- char c; return ()

> pLLam = do
>     schar '\\'
>     e <- pL
>     return $ Abs e

> pLApp = do
>     es <- many1 pLAtom
>     return $ foldl1 App es

> pLAtom = pLVar +++ (do schar '('; e <- pL; schar ')'; return e)

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
