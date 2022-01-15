Look for small bases
 
> import System.IO
> import Data.List
> import qualified Data.Heap as Heap
> import Data.Function
> -- import Debug.Trace
> import qualified Data.Set as Set
> import System.Environment(getArgs)
> import Text.ParserCombinators.ReadP
> import qualified Data.Map.Strict as Map

terms with de Bruijn indices (internal: starting at 0)

> data L = Var !Int | App L L | Abs L deriving (Eq, Ord)

size of the binary lambda calculus encoding

> size :: L -> Int
> size (Var i)   = i + 2
> size (App a b) = 2 + size a + size b
> size (Abs a)   = 2 + size a

printing

> newtype P = P L
>     deriving (Eq, Ord)

> instance Show P where
>     showsPrec _ (P a) = prs a

> prs :: L -> ShowS
> prs = go 0 where
>     go :: Int -> L -> ShowS
>     go _ (Var i)   = shows (i+1)
>     go p (App a b) = showParen (p > 1) $ go 1 a . (' ':) . go 2 b
>     go p (Abs a)   = showParen (p > 0) $ ('λ':) . go 0 a

> instance Show L where
>   show a = prs a ""

> instance Read L where
>     readsPrec _ = readP_to_S pL

A ReadP parser for $\lambda$-expressions.

> pVar :: (Read v) => ReadP v
> pVar = do skipSpaces; readS_to_P (readsPrec 9)

> schar :: Char -> ReadP ()
> schar c = do skipSpaces; _ <- char c; return ()

> pL, pLAtom, pLVar, pLLam, pLApp :: ReadP L
> pL = pLLam +++ pLApp
>
> pLVar = do
>     v <- pVar
>     return $ Var (v-1)
>
> pLLam = do
>     schar 'λ'
>     e <- pL
>     return $ Abs e
>
> pLApp = do
>     es <- many1 pLAtom
>     return $ foldl1 App es
>
> pLAtom = pLVar +++ (do schar '('; e <- pL; schar ')'; return e)

de-Bruijn substitution

> subst :: Int -> L -> L -> L
> subst i (Var j)   c = if i == j then c else Var (if j > i then j-1 else j)
> subst i (App a b) c = App (subst i a c) (subst i b c)
> subst i (Abs a)   c = Abs (subst (i+1) a (incv 0 c))

> incv :: Int -> L -> L
> incv i (Var j)   = Var (if i <= j then j+1 else j)
> incv i (App a b) = App (incv i a) (incv i b)
> incv i (Abs a)   = Abs (incv (i+1) a)

number of occurrences of a variable

> noccur :: Int -> L -> Int
> noccur i (Var j)   = if i == j then 1 else 0
> noccur i (App a b) = noccur i a + noccur i b
> noccur i (Abs a)   = noccur (i+1) a

reduction to normal form with limited expansion
need to account for expansion in function normalization because of
SSK (λxλy.x y SSK) @ SSK
SSK (λxλy.x y SSK) -=-=-=> λy. (λxλy.x y SSK) y (λxλy.x y SSK)
(λxλy.x y SSK) SSK (λxλy.x y SSK) 
SSK (λxλy.x y SSK) SSK

> lnf :: Int -> L -> Maybe (Int, L)
> lnf n (App f b) = {-- trace ("lnf " ++ show n ++ ": " ++ show f ++ " @ " ++ show b) $ --}
>  case lnf n f of
>   Nothing -> Nothing
>   Just (n', Abs a) -> if n'' < 0 then Nothing else lnf n'' a' where
>     a' = subst 0 a b
>     n'' = case b of
>       (Var _) -> n'
>       _       -> n' - max 0 ((noccur 0 a) - 1)
>   Just (n',a) -> fmap (fmap (App a)) (lnf n' b)
> lnf n (Abs a) = fmap (fmap Abs) (lnf n a)
> lnf n a = Just (n,a)

Candidate single point bases

> bases :: [String]
> bases = [
>  "λλλ3 1 (2 (λ2))", -- minimal             level 16 cumsize 2200336
>  "λλλ2 1 (3 (λ2))", -- sizes below in ()   level 16 cumsize 1220869
>  "λλλ2 (λ2) (3 1)", -- generates {T,K,B,W} level 16 cumsize  577496
>  "λλλ3 (λ2) (2 1)", -- only finds F,I      level 16 cumsize   20312
>  "λ1(λλλ2 1 (3 1))(λλ2)",      -- <S',K>   level 16 cumsize    5817
>  "λ1(λλ2)(λλλ2 1 (3 1))(λλ2)", -- <K,S',K> level 16 cumsize    3261
>  "λ1(λλ2)(λλλ3 1 (2 1))(λλ2)", -- <K,S,K>  level 16 cumsize    2253
>  "λ1(λλλ3 1 (2 1))(λλ2)",      -- <S,K>    level 16 cumsize     244
>  "λ1(λλλ3 1 (2 1))(λλλ3)",     -- Jeroen Fokker
>  "λλλ3 (λλ2) 1 (2 1)",         -- Johannes Bader
>  "λλλλ2 1 (4 (λ2))",           -- C.A. Meredith 1963!
>  ""]

> main :: IO ()
> main = do
>   hSetBuffering stdout LineBuffering
>   args <- getArgs
>   let basis = [("A", read (bases !! (if null args then 0 else read (head args))))]
>   putStrLn $ "Using basis " ++ show basis
>   findtargets 1 (levels basis) targets
>   -- findtargets 1 (levels2 basis 12 65536) targets

> levels :: [(String,L)] -> [[(String, L)]]
> levels basis = l where l = basis : map (build id  l) [1..] 

> levels2 :: [(String,L)] -> Int -> Int -> [[(String, L)]]
> levels2 basis n len = l2 where
>   l2 = take n (levels basis) ++ map (build filt l2) [n..]
>   filt = take len -- . sortBy (compare `on` (size.snd)) 

> findtargets :: Int -> [[(String,L)]] -> [(L,String)] -> IO ()
> findtargets _ _ [] = return ()
> findtargets _ [] _ = putStrLn "Unexpected end of levels"
> findtargets n (lvl:lvls) tgts = do
>   putStrLn $ "level " ++ show n ++ " size " ++ show (length lvl)
>   go lvl [] where
>     go [] found = findtargets (n+1) lvls (tgts \\ found)
>     go ((as,comb):lvl') found = case Map.lookup comb tgtmap of
>       Just name -> do
>         putStrLn $ name ++ " = " ++ show comb ++ " = " ++ as
>         go lvl' ((comb,name) : found)
>       Nothing -> go lvl' found
>     tgtmap = Map.fromList targets

> targets :: [(L,String)]
> targets = [
>   (read"λλ  2 1 2   ","Y0"), -- A A(A(A A)A) of size 6 (14)
>   (read"λλ  2 1 1   ","W"), -- A A(A(A(A A)A)) of size 7 (9)
>   -- A M (W N) is 8 shorter than S M N and 7 shorter than S' N M
>   (read"λ   1   1   ","D"), -- A(A(A A)A)(A(A A)A) of size 9 (9)
>   (read"λ       1   ","I"), -- A(A(A(A A)A))(A(A A)A) of size 10 (14)
>   (read"λλ      2   ","K"), -- A(A A)(A(A A)A A A A A) of size 11 (15)
>   (read"λλ      1   ","F"), -- A A A(A(A A)(A A)(A A))A of size 11 (16)
>   (read"λλ  1   2   ","T"), -- A A(A(A A)A(A(A A)A)A)(A A) of size 13 (18 or 16 with eta)
>   (read"λλλ 3 1 2   ","C"), -- A(A A A(A A A)(A A)(A A))A A of size 13 (15)
>   (read"λλλ 3  (2 1)","B"), -- A(A(A(A(A A)A))(A A)A)(A(A(A A))) of size 14 (?)
>   (read"λλλ   3 1   ","K2"), -- A A(A(A A)(A A)(A A))(A(A A) A) A A (15)
>   (read"λλλ 2 1(3 1)","S'"), -- A(A(A A)A)A A A A A A(A(A A)A) of size 15 (13)
>   (read"λλλ 1 2 3   ","V'"), -- A A(A A)(A A)(A(A A(A A)) A A)(A A) of size 15
>   (read"λλ  1 2 2   ","T1"), -- A(A(A(A(A(A A))))(A A) A)(A(A A)(A A)) of size 15
>   (read"λλ  2 2 1   ","W0"), -- A A(A A)(A A(A A) A)(A A(A(A(A A) A))) of size 16
>   (read"λλλ 3 1(2 1)","S"), -- A(A(A A(A A(A A))(A(A(A A(A A))))))A A of size 16 (18)
>   (read"λλ  1 1 2   ","T0"), -- A(A A)(A(A(A(A(A A) A) A(A A)) A) A A A) of size 17
>   (read"λλ2(1 2 1)  ","Y1"), -- A(A(A A A)(A A)(A(A A) A) A)(A(A(A(A A)) A)) of size 18
>   (read"λλλ 1 3 2   ","V"), -- ((((A(A(A(A(A A)))))((((A A)A)((A A)((A A)A)))A))(A A))A)A of size 19
>   (read"λλλ2(3 2 1)  ","X"), -- ((((A(A(((A((A(AA))A))A)A)))(AA))(A((A(A((AA)A)))A)))A)A of size 20
>   (read"λλλλ4 (3 2 1)","B3"), -- 
>   (read"λλλ3 (λ3 (2 1))","CB3B"), --  > 22 according to Hunt.hs
>   (read"λλ21","I2")] -- 

Btw, shortest diverging is Omega = (A A A) (A (A A A)) of size 7

> build :: ([(String,L)] -> [(String,L)]) -> [[(String,L)]] -> Int -> [(String,L)]
> build filt as n = filt apps where
>   apps = nubOrd (Set.fromList . concatMap (map snd) . take n $ as) $
>          [(fst x ++ paren (fst y), a) | i <- [0..n-1],
>            x <- as!!(n-1-i), y <- as!!i,
>            Just a <- [fmap snd . lnf lim $ App (snd x) (snd y)]]
>   lim = if n < 16 then 42 else 14
>   paren [a] = ' ':[a]
>   paren  s  = "(" ++ s ++ ")"

> nubOrd :: Ord a => Set.Set a -> [(b,a)] -> [(b,a)] 
> nubOrd s (it@(_,x):xs)
>    | x `Set.member` s = nubOrd s xs
>    | otherwise        = it : nubOrd (Set.insert x s) xs
> nubOrd  _ _           = []
