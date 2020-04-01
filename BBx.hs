-- Look for BLC busy beavers.
--
-- Author: Bertram Felgenhauer <int-e@gmx.de>

import System.IO
import Debug.Trace
import Control.Applicative
import qualified Data.Set as S

-- terms with de Bruijn indices (internal: starting at 0)
-- note: Bot marks useless subterms that do not contribute to the normal form
data L = Var !Int | App L L | Abs L | Bot
    deriving (Eq, Ord, Show)

-- generate terms of size n with all variables < v
gen :: Int -> Int -> [L]
gen v n =
    [Var (n-2) | n >= 2, n-2 < v] ++
    [App a b | i <- [2..n-4], a <- gen v i, b <- gen v (n-2-i)] ++
    [Abs a | n >= 4, a <- gen (v+1) (n-2)]

size :: L -> Int
size (Var i)   = i + 2
size (App a b) = 2 + size a + size b
size (Abs a)   = 2 + size a

subst :: Int -> L -> L -> L
subst i (Var j)   c = if i == j then c else Var (if j > i then j-1 else j)
subst i (App a b) c = App (subst i a c) (subst i b c)
subst i (Abs a)   c = Abs (subst (i+1) a (incv 0 c))
subst i Bot       _ = Bot

incv :: Int -> L -> L
incv i (Var j)   = Var (if i <= j then j+1 else j)
incv i (App a b) = App (incv i a) (incv i b)
incv i (Abs a)   = Abs (incv (i+1) a)
incv i Bot       = Bot

{-
-- rewriting, unused
step :: L -> Maybe L
step (App (Abs a) b) = Just (subst 0 a b)
step (App a b)       = ((\a' -> App a' b) <$> step a) <|>
                       ((\b' -> App a b') <$> step b)
step (Abs a)         = Abs <$> step a
step _               = Nothing

redex :: L -> Maybe L
redex (App (Abs a) b) = Just (App (Abs a) b)
redex (App a b)       = redex a <|> redex b
redex (Abs a)         = redex a
redex _               = Nothing
-}

-- count occurrences of a variable
occur :: Int -> L -> Int
occur i (Var j)   = if i == j then 1 else 0
occur i (App a b) = occur i a + occur i b
occur i (Abs a)   = occur (i+1) a
occur i Bot       = 0

-- try to find normal form; Nothing means no normal form
-- (logs cases where it bails out; should really be in IO...)
nf :: L -> Maybe L
nf a0 = go S.empty a0 where
    go :: S.Set L -> L -> Maybe L
    go s (Abs a) = Abs <$> go s a
    go s (App a b) = do
        a <- go s a
        b <- return (simp b)
        let r = botFree 0 (App a b)
        case a of
            _   | isW a && isW b -> Nothing
            Abs a
                | r `S.member` s -> Nothing
                | S.size s > 10  -> trace ("-- TODO: " ++ pr a0) Nothing
                | otherwise      -> go (r `S.insert` s) (subst 0 a b)
            _ -> do
                b <- go s b
                return (App a b)
    go s t = Just t

    -- replace free variables (of a redex) by bottom
    botFree i (Var j)   = if j >= i then Bot else Var j
    botFree i (App a b) = App (botFree i a) (botFree i b)
    botFree i (Abs a)   = Abs (botFree (i+1) a)
    botFree i Bot       = Bot

-- simplification
simp :: L -> L
simp = go where
    go (Abs a) = Abs (go a)
    go (App a b) = case go a of
        Abs a | a <- simpA 0 a b, occur 0 a <= 1 -> go (subst 0 a b)
        a -> App a (go b)
    go t = t

    -- simplify a based on its argument
    simpA i a (Abs b)
        | occur 0 b == 0 = simpE i a -- \b erases first argument
        | b == Var 0     = simpI i a -- \b is id = \1
    simpA i a _ = a

    -- the first argument of variable i is not needed, so replace it by Bot
    simpE i (App (Var j) b)
        | i == j = App (Var j) Bot
    simpE i (App a b) = App (simpE i a) (simpE i b)
    simpE i (Abs a) = Abs (simpE (i+1) a)
    simpE i a = a

    -- variable i will be substituted by id = \1
    simpI i (App (Var j) b)
        | i == j = simpI i b
    simpI i (App a b) = App (simpI i a) (simpI i b)
    simpI i (Abs a) = Abs (simpI (i+1) a)
    simpI i a = a

-- various terms W that allow W W -> H[W W] for head context H,
-- leading to infinite head reductions
isW :: L -> Bool
isW = go [] where
    go is (Var i) = i `elem` is
    go is (Abs a) = go' (0 : map succ is) a
    -- go is Bot = True
    go _ _ = False

    go' is (App a@(App _ _) _) = go' is a
    go' is (App a b) = go is a && go is b
    go' is (Abs a) = go' (map succ is) a
    go' _ _ = False

main :: IO ()
main = do
    hSetBuffering stdout LineBuffering
    mapM_ print [f n | n <- [0..32]]
  where
    f n = maximum $
        (n,0,P Bot) : [(n,size t,P a) | a <- gen 0 n, Just t <- [nf a]]

-- printing
newtype P = P L
    deriving (Eq, Ord)

instance Show P where
    showsPrec _ (P a) = prs a

prs :: L -> ShowS
prs = go 0 where
    go p (Var i)   = shows (i+1)
    go p (App a b) = showParen (p > 1) $ go 1 a . (' ':) . go 2 b
    go p (Abs a)   = showParen (p > 0) $ ('\\':) . go 0 a
    go p Bot       = ('_':)

pr :: L -> String
pr a = prs a ""
