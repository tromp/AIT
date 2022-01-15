{-# LANGUAGE BangPatterns #-}
import Data.Char
import Data.List
import qualified Data.Set as S
import qualified Data.Map.Strict as M
import System.Environment
import System.Exit

data L = Var !Int | Abs L | App L L

instance Show L where
    show (Var i) = showParen (i < 0 || i > 9) (shows i) ""
    show (Abs t) = "^" ++ show t
    show (App s t) = "`" ++ show s ++ show t

instance Read L where
    readsPrec _ s
        | '(':s <- s, [(n,s)] <- reads s, ')':s <- s = [(Var n,s)]
        | c:s <- s, isDigit c = [(Var (digitToInt c),s)]
        | '^':s <- s, [(t,s)] <- reads s = [(Abs t,s)]
        | '`':s <- s, [(t,s)] <- reads s, [(u,s)] <- reads s = [(App t u,s)]

-- T = label tracking provenance of subterms; M = additional dependencies
type T = [Int]
type M = [(T, T)]

data LC
    = VarC !Char T !Int
    | AbsC !Char T LC
    | AppC !Char T LC LC
    | AlphaC !Char T
    | BotC !Char T

label (VarC _ p _) = p
label (AbsC _ p _) = p
label (AppC _ p _ _) = p
label (AlphaC _ p) = p
label (BotC _ p) = p

instance Show LC where
    show (VarC c p i)   = c : show p ++ show i
    show (AbsC c p t)   = c : show p ++ "^" ++ show t
    show (AppC c p s t) = c : show p ++ "`" ++ show s ++ show t
    show (AlphaC c p)   = c : show p ++ "α"
    show (BotC c p)     = c : show p ++ "⊥"

step :: LC -> Maybe (LC, T, M)
step (VarC _ _ _)                = Nothing
step (AbsC c p t)
    | Just (t, q, m) <- step t   = Just (AbsC c p t, q, m)
    | otherwise                  = Nothing
step (AppC c p s t)
    | AbsC _ _ s <- s
    , (t, _, m) <- subst 0 0 t s = Just (t, p, ([],label t) : m)
    | Just (s, q, m) <- step s   = Just (AppC c p s t, q, m)
    | Just (t, q, m) <- step t   = Just (AppC c p s t, q, m)
    | otherwise                  = Nothing
step (AlphaC c p)                = Just (alphaC c p, p, [])

subst i n s t@(VarC c p j)
    | i == j    = (mark n s, n+1, [(n:label s, p)])
    | i < j     = (VarC c p (j-1), n, [])
    | otherwise = (t, n, [])
subst i n s (AbsC c p t)
    | (t, n, m) <- subst (i+1) n (shift i s) t
    = (AbsC c p t, n, m)
subst i n s (AppC c p t u)
    | (t, n, m1) <- subst i n s t
    , (u, n, m2) <- subst i n s u
    = (AppC c p t u, n, m1 ++ m2)
subst i n s t = (t, n, [])

mark n (VarC c p i)   = VarC c (n:p) i
mark n (AbsC c p t)   = AbsC c (n:p) (mark n t)
mark n (AppC c p t u) = AppC c (n:p) (mark n t) (mark n u)
mark n (AlphaC c p)   = AlphaC c (n:p)
mark n (BotC c p)     = BotC c (n:p)

shift i t@(VarC c p j)
    | j >= i           = VarC c p (j+1)
    | otherwise        = t
shift i (AbsC c p t)   = AbsC c p (shift (i+1) t)
shift i (AppC c p s t) = AppC c p (shift i s) (shift i t)
shift _ t              = t

alphaC c p = AbsC c (0:p) (AbsC c (1:p) (AbsC c (2:p) (AppC c (3:p) (AppC c (4:p) (VarC c (5:p) 2) (VarC c (6:p) 0)) (AppC c (7:p) (VarC c (8:p) 1) (AbsC c (9:p) (VarC c (10:p) 1))))))

mkT xs = (\(t, _, _) -> t) (go (read xs) ['a'..] 0) where
    go (App s t) xs n
        | (s, xs, n) <- go s xs n
        , (t, xs, n) <- go t xs n
        = (AppC 'z' [n] s t, xs, n+1)
    go (Var 0) (x:xs) n
        = (AlphaC x [n], xs, n+1)


combs = [("S",s), ("S1", s1), ("S2", s2), ("S3", s3), ("S4", s4), ("S5", s5),
         ("K",k), ("K1", k1), ("K2", k2), ("K3", k3), ("K4", k4),
         ("I",i), ("B", b), ("C", c), ("W", w)]
  where
    s = s1
    s1 = mkT "```0`0```00``00`00`0`0``00`0000"
    s2 = mkT "````0`````0`0`000`00`00000`0`00"
    s3 = mkT "````0```0`0``0`00`000`0000`0`00"
    s4 = mkT "````0```0``0`0`000`00`0000`0`00"
    s5 = mkT "````0````0`0`000`00``00000`0`00"

    k = k3
    k1 = mkT "````00````0`000000`00"
    k2 = mkT "```00`````0`000000`00"
    k3 = mkT "``0`00``````0`0000000"
    k4 = mkT "```0``00``0000``0`000"

    i = mkT "``0`0``0`000``0`000"
    b = mkT "``0```0`0``0`000`000`0`0`00"
    c = mkT "```0`````000``000`00`0000"
    w = mkT "``00`0``0`000"

usage = do
    putStr $ unlines
        ["Render reduction of given combinator in terms of α to normal form as HTML."
        ,""
        ,"Usage:"
        ,"    $0 [-f] S|K|I|B|C|W|S1..S5|K1..K4 > out.html"
        ,"    $0 [-f] NAME T > out.html"
        ,"where"
        ,"    -f: full reduction with unneeded subterms"
        ,"    S1..S5 are alternative encodings of S (S = S1)"
        ,"    K1..K4 are alternative encodings of K (K = S3)"
        ,"    T := 0 | `TT"]
    exitFailure

main = do
    args <- getArgs
    !(full, args) <- pure $ case args of
            "-f":args -> (True, args)
            args      -> (False, args)
    !(t, n) <- case args of
            [n] | Just t <- lookup n combs -> pure (t, take 1 n)
            [n, t] -> pure (mkT t, n)
            _ -> usage
    let clrs = ["f00","cb0","0d0","0bc","00f","c0c",
                "e50","6c0","0c6","05c","60e","e06",
                "900","660","080","066","009","606"]
    putStr $ unlines $
        ["<!doctype html>"
        ,"<html>"
        ,"<title>Reduction: " ++ n ++ " in terms of alpha</title>"
        ,"<style>"
        ,"p { margin: 0 0 0 0 }"
        ,"b { font-weight: normal }"
        ,"s, u { text-decoration: none }"
        ,"s { padding: 0 0.15em 0 0.15em }"
        ,"u + s { padding-left: 0 }"
        ,"u:hover, s:hover, u:hover ~ * { background-color: #cdf }"] ++
        ["." ++ [c] ++ " { color: #" ++ p ++ " }" | (c, p) <- zip ['a'..] clrs] ++
        [".z { color: #000 }"
        ,"</style>"]
    let post = if full then map (\(t, _, _) -> t) else clean
    putStr $ unlines $ map (\l -> "<p>" ++ render l) (post (trace (t, [], [])))

trace :: (LC,T,M) -> [(LC,T,M)]
trace c@(t, _, _) = c : case step t of Nothing -> []; Just c -> trace c

-- replace unneeded subterms in a reduction by BotC
clean :: [(LC,T,M)] -> [LC]
clean cs = map erase (map erase ts)
  where
    ts = map (\(t,_,_) -> t) cs

    deps = M.fromListWith (++) $
        [(a,[b]) | (_,_,m) <- cs, (a,b) <- m] ++ (ts >>= nest [])

    nest q (VarC c p _)   = [(p, [q])]
    nest q (AbsC c p t)   = [(p, [q])] ++ nest p t
    nest q (AppC c p t u) = [(p, [q])] ++ nest p t ++ nest p u
    nest q (AlphaC c p)   = [(p, [q])]
    nest q (BotC c p)     = [(p, [q])]

    needed = complete S.empty (S.fromList ((labels (last ts) ++ (cs >>= \(_,p,_) -> [p])) >>= tails))

    complete seen new
        | seen <- seen `S.union` new
        , next <- S.fromList (S.toList new >>= \k -> M.findWithDefault [] k deps >>= tails) `S.difference` seen
        = if S.null next then seen else complete seen next

    labels (VarC _ p _) = [p]
    labels (AbsC _ p t) = [p] ++ labels t
    labels (AppC _ p t u) = [p] ++ labels t ++ labels u
    labels (AlphaC _ p) = [p]
    labels (BotC _ p) = [p]

    erase t@(VarC c p _)
        | p `S.member` needed = t
        | otherwise           = BotC c p
    erase (AbsC c p t)
        | p `S.member` needed = AbsC c p (erase t)
        | otherwise           = BotC c p
    erase (AppC c p t u)
        | p `S.member` needed = AppC c p (erase t) (erase u)
        | otherwise           = BotC c p
    erase t@(AlphaC c p)
        | p `S.member` needed = t
        | otherwise           = BotC c p
    erase t@(BotC _ p)        = t

spanb xs = "<b>" ++ xs ++ "</b>"
spanu cs xs = "<u class=\"" ++ cs ++ "\">" ++ xs ++ "</u>"
spans cs xs = "<s class=\"" ++ cs ++ "\">" ++ xs ++ "</s>"

render (AbsC c p t) = spanb $ spanu [c] "^" ++ render t
render (AppC c p t u) = spanb $ spanu [c] "`" ++ render t ++ render u
render (VarC c p i) = spans [c] $ show i
render (AlphaC c p) = spans [c] "α"
render (BotC c p) = spans [c] "⊥"
