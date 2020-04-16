Look for BLC busy beavers.
Author: Bertram Felgenhauer / John Tromp
 
> import System.IO
> import Debug.Trace
> import Data.List
> import Control.Applicative
> import qualified Data.Set as S
 
terms with de Bruijn indices (internal: starting at 0)
note: Bot marks useless subterms that do not contribute to the normal form

> data L = Var !Int | App L L | Abs L | Bot
>     deriving (Eq, Ord, Show)

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

> headarg :: L -> L -> Maybe L
> headarg (App (Var 0) a) t = Just $ subst 0 a t
> headarg (App a b) t = headarg a t
> headarg _ _ = Nothing

> selfish :: L -> Bool
> selfish t@(Abs body) = case headarg body t >>= nf0 of
>   Just hanf -> botFree 0 hanf == botFree 0 t
>   Nothing -> False
> selfish _ = False

> strict :: L -> Bool
> strict (Abs a) = str 0 a where
>   str i (Abs a) = str (i+1) a
>   str i (Var j) = i == j
>   str i (App a _) = str i a
>   -- str _ Bot = False
> strict _ = False

Closer examination of trouble terms

> examine :: L -> Maybe L
> examine a0 = ex a0 where
>   ex (Abs a) = Abs <$> ex a
>   ex (App a b) | isW [] a && (selfish b || b `elem` []) = trace ("-- DONE: " ++ pr a0) Nothing
>   ex _ = trace ("-- TODO: " ++ pr a0) Nothing

> showset :: S.Set L -> String
> showset s = "[" ++ intercalate ", " (map pr (S.toList s)) ++ "]"

try to find normal form; Nothing means no normal form
(logs cases where it bails out; should really be in IO...)

> nf0 :: L -> Maybe L
> nf0 a0 =  nfp S.empty a0 where
>   nfp :: S.Set L -> L -> Maybe L
>   -- nfp s a = trace ("nf " ++ showset s++ " " ++ pr a) $ nf s a
>   nfp s a = nf s a
>   nf :: S.Set L -> L -> Maybe L
>   nf s (Abs a) = Abs <$> nfp s a
>   nf s r@(App a b) = do
>     a <- nfp s a
>     -- b <- if trace ("strict " ++ pr a ++ " = " ++ show (strict a)) (strict a) then nfp s b else Just (simplify b)
>     b <- if strict a then nfp s b else Just (simplify b)
>     let r = botFree 0 (App a b)
>     -- case trace ("r = " ++ pr r ++ " case " ++ pr a ++ " of") a of
>     case a of
>         _   | isB [] (App a b) -> Nothing
>         Abs a
>             | r `S.member` s -> Nothing
>             | S.size s > 9 -> examine a0
>             | otherwise      -> nfp (r `S.insert` s) (subst 0 a b)
>         _ -> do
>             b <- nfp s b
>             return (App a b)
>   nf _ t = Just t

simplification

> simplify :: L -> L
> simplify = simp where
>     -- simp a | isB [] a || loop3 a = Bot
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

various terms W that allow W W -> H[W W] for head context H,
leading to infinite head reductions

> isW :: [Int] -> L -> Bool
> isW is (Var i) = i `elem` is
> isW is (Abs a) = isB (0 : map succ is) a
> isW _ Bot = True
> isW _ _ = False

> isB :: [Int] -> L -> Bool
> isB is (App a@(App _ _) _) = isB is a
> isB is (App a b) = isW is a && (isW is b || isB is b)
> isB is (Abs a) = isB (map succ is) a
> isB _ Bot = True
> isB _ a = False

various terms W that allow W _ W -> H[W _ W] for head context H,
leading to infinite head reductions

> isW3 :: [Int] -> L -> Bool
> isW3 is (Var i) = i `elem` is
> isW3 is (Abs a) = isB3 (0 : map succ is) a
> isW3 _ Bot = True
> isW3 is a = isB3 is a

> isB3 :: [Int] -> L -> Bool
> isB3 is (App a@(App (App _ _)  _) _) = isB3 is a
> isB3 is (App (App a _) b) = isW3 is a && isW3 is b
> isB3 is (Abs a) = isB3 (map succ is) a
> isB3 _ Bot = True
> isB3 _ a = False

> loop3 :: L -> Bool
> loop3 (App a (Abs b)) = isW3 [] a && isW3 [] b
> loop3 _ = False

-- TODO: (\1 1) (\1 (1 (\2)) (\2))
T = \x. x (x (K x)) (K x)
-- TODO: (\1 1) (\1 (1 (\\3)) 1)
-- TODO: (\1 1) (\(\1 (1 (\3))) 1)
-- TODO: (\1 1) (\(\1 (2 (\2))) 1)
-- TODO: (\1 1) (\(\2 (1 (\2))) 1)
-- TODO: (\1 1 1) (\\1 (\3) 1)


> main :: IO ()
> main = do
>     hSetBuffering stdout LineBuffering
>     -- print $ nf0 debug
>     mapM_ print [f n | n <- [0..34]]
>   where
>     f n = maximum $
>         (n,0,P Bot) : [(n,size t,P a) | a <- gen 0 n, Just t <- [nf0 a]]

how is size-32 (\1 (\2)) (\1 1 (\1 2)) seen to loop?
Let T = \1 1 (\1 2) = \x. x x <x>
If we denote \x. x A as <A>, and \_. x as K x, then
    (\1 (\2)) T
 -> T (K T)
 -> K T (K T) <K T>
 -> T <K T>
 -> <K T> <K T> <<K T>>
 -> <K T> (K T) <<K T>>
 -> K T (K T) <<K T>>
 -> T <<K T>>
  etc.

> dbgdbl :: L
> dbgdbl = Abs (App (Var 0) (Var 0))
> dbgu :: L
> dbgu = Abs (App (Var 0) (Abs (Var 1)))
> dbgt :: L
> dbgt = Abs (App (Var 0) (App (Var 0) dbgu))
> debug :: L
> debug = dbgdbl `App` dbgt

printing

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