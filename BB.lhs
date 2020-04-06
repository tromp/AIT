> import System.Environment(getArgs)
> import System.IO
> import Debug.Trace
> import Data.List
> import Data.Maybe
> import Lambda
> import AIT

Enumerate all lambda terms of given openness and size

> openness :: Int -> Int -> [DB]
> openness o n = if n < 2 then [] else lams ++ apps ++ vars where
>   lams = map DBLam $ openness (o+1) (n-2)
>   apps = [DBApp t1 t2 | n1 <- [2..n-2], t1 <- openness o n1, t2 <- openness o (n-2-n1)]
>   vars = map DBVar [n-2 | n-2 < o]

Enumerate all closed lambda terms of given size

> closed :: Int -> [DB]
> closed = openness 0

Loop detector

> doubles :: DB -> Bool
>
> doubles = go [] where
>   go is (DBVar i) = i `elem` is
>   go is (DBLam body) = go' (0 : map succ is) body
>   go _ _ = False
> 
>   go' is (DBApp a@(DBApp _ _) _) = go' is a
>   go' is (DBApp fun arg) = go is fun && go is arg
>   go' is (DBLam body) = go' (map succ is) body
>   go' _ _ = False

Complex Looping detector, recognizes terms of form \x. K^* (x^+ (\y. K^* (y^+ (x y ...) ...)) ...)

> doubledloops :: DB -> Bool
> doubledloops (DBLam body) = go0 0 body where

1 (1 (\2 1 1))

recognize K^* (x^+ (\y. K^* (y^+ (x y ...) ...)) ...) -- go0 0 "1 (\1 (2 1))"

>   go0 ix t@(DBApp _ _) = go1 ix t
>   go0 ix (DBLam body) = go0 (ix+1) body
>   go0 _ _ = False
   
recognize x^+ (\y. K^* (y^+ (x y ...) ...)) ... -- go1 0 "1 (\1 (2 1))"

>   go1 ix (DBApp (DBVar i) arg) | i==ix = go2 ix arg
>   go1 ix (DBApp fun _) = go1 ix fun
>   go1 _ _ = False

recognize x^* (\y. K^* (y^+ (x y ...) ...)) -- go2 0 "\1 (2 1)"

>   go2 ix (DBLam body) = go3 (ix+1) 0 body
>   go2 ix (DBApp (DBVar i) arg) | i==ix = go2 ix arg
>   go2 _ _ = False

recognize K^* (y^+ (x y ...) ...) -- go3 1 0 "1 (2 1)"

>   go3 ix iy t@(DBApp _ _) = go4 ix iy t
>   go3 ix iy (DBLam body) = go3 (ix+1) (iy+1) body
>   go3 _ _ _ = False
   
recognize y^+ (x y ...) ... -- go4 1 0 "1 (2 1)"

>   go4 ix iy (DBApp (DBVar i) arg) | i==iy = go5 ix iy arg
>   go4 ix iy (DBApp fun _) = go4 ix iy fun
>   go4 _ _ _ = False

recognize y^* (x y ...) -- go5 1 0 "2 1"

>   go5 ix iy (DBApp (DBVar i) arg) | i==iy = go5 ix iy arg
>   go5 ix iy t@(DBApp _ _) = go6 ix iy t
>   go5 _ _ _ = False

recognize x y ... -- go6 1 0 "2 1"

>   go6 ix iy (DBApp (DBVar i) (DBVar i2)) = i==ix && i2==iy
>   go6 ix iy (DBApp fun _) = go6 ix iy fun
>   go6 _ _ _ = False

> doubledloops _ = False

Equality modulo free vars
Could be generalized so head subterm of first arg

> eqfree :: Int -> DB -> DB -> Bool
> eqfree n (DBLam body1) (DBLam body2) = eqfree (n+1) body1 body2
> eqfree n (DBApp fun1 arg1) (DBApp fun2 arg2) = eqfree n fun1 fun2 && eqfree n arg1 arg2
> eqfree n (DBVar i1) (DBVar i2) = i1 == i2 || (i1 >= n && i2 >= n)
> eqfree _ _ _ = False

> data BBClass a = NormalForm a | Diverging | Unknown

> instance Functor BBClass where
>   fmap f (NormalForm t) = NormalForm (f t)
>   fmap _ Diverging = Diverging 
>   fmap _ Unknown = Unknown 

> instance Applicative BBClass where
>   pure = NormalForm
>   NormalForm f <*> t = fmap f t
>   Diverging    <*> _ = Diverging 
>   Unknown      <*> _ = Unknown 

> instance Monad BBClass where
>   return = NormalForm
>   NormalForm t >>= f = f t
>   Diverging    >>= _ = Diverging 
>   Unknown      >>= _ = Unknown 

Simplification

> simplify :: DB -> DB
> simplify = simp where
>   simp (DBLam a) = DBLam (simp a)
>   simp (DBApp a b) = case simp a of
>       DBLam a | a <- simpA a b, noccurs 0 a <= 1 -> simp (subst 0 b a)
>       a -> DBApp a (simp b)
>   simp t = t

>   -- simplify a based on its argument
>   simpA a (DBLam b)
>       | not (occurs 0 b) = simpE 0 a -- \b erases first argument
>       | b == DBVar 0     = simpI 0 a -- \b is id = \1
>   simpA a _ = a

>   -- the first argument of variable i is not needed, so replace it by simplest term
>   simpE i (DBApp (DBVar j) b)
>       | i == j = DBApp (DBVar j) (DBLam (DBVar 0))
>   simpE i (DBApp a b) = DBApp (simpE i a) (simpE i b)
>   simpE i (DBLam a) = DBLam (simpE (i+1) a)
>   simpE i a = a

> -- variable i will be substituted by id = \1
> simpI i (DBApp (DBVar j) b)
>     | i == j = simpI i b
> simpI i (DBApp a b) = DBApp (simpI i a) (simpI i b)
> simpI i (DBLam a) = DBLam (simpI (i+1) a)
> simpI i a = a

Classify reduction behaviour

> classify :: DB -> BBClass DB
> classify t = go [] t where
>   go :: [DB] -> DB -> BBClass DB
>   go s (DBLam a) = DBLam <$> go s a
>   go s t@(DBApp a b) = do
>       a1 <- go s a
>       let b1 = simplify b
>       case a1 of
>           _   | doubles a1 && (doubles b1 || doubledloops b1) -> Diverging
>           DBLam body
>               | any (eqfree 0 t) s -> Diverging
>               | length s > 20      -> Unknown
>               | otherwise          -> go (t:s) (subst 0 b1 body)
>           _ -> DBApp a1 <$> go s b1
>   go _ t = NormalForm t

> headarg :: DB -> DB -> Maybe DB
> headarg (DBApp (DBVar 0) arg) t = Just $ subst 0 t arg
> headarg (DBApp fun arg) t = headarg fun t
> headarg _ _ = Nothing

> ponder :: Int -> DB -> IO ()
> ponder min t = do
>   -- putStrLn $ show t
>   case classify t of
>     NormalForm nf | size nf >= min -> putStrLn $ (show . size $ nf) ++ " " ++ show t ++ " ->* " ++ show nf
>     Unknown -> case t of
>       DBApp fun t2@(DBLam body) | doubles fun -> case fmap classify (headarg body t2) of
>         Just (NormalForm nf) | eqfree 0 nf t2 -> putStrLn $ "Unknown-then-Diverging" ++ show t
>         _ -> putStrLn $ "Still-Unknown" ++ show t
>       _ -> putStrLn $ "Unknown" ++ show t
>     -- Diverging -> putStrLn $ "Diverging" ++ show t
>     _ -> return ()

> main :: IO ()
> main = do
>   args <- getArgs
>   case args of
>     [n] -> do
>       mapM_ (ponder 0) . filter expands . closed $ read n
>     [n,m] -> do
>       mapM_ (ponder $ read m) . filter expands . closed $ read n
>       -- mapM_ (ponder 0) . filter (== read m) . filter expands . closed $ read n
>     _ -> putStrLn "usage: BB <Int>"
