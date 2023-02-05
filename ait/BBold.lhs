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
>   go' is (DBApp fun arg) = go is fun && (go is arg || go' is arg)
>   go' is (DBLam body) = go' (map succ is) body
>   go' _ _ = False

> triples :: DB -> Bool
>
> triples = go [] where
>   go is (DBVar i) = i `elem` is
>   go is (DBLam body) = go' (0 : map succ is) body
>   go _ _ = False
> 
>   go' is (DBApp a@(DBApp (DBApp _ _) _) _) = go' is a
>   go' is (DBApp (DBApp fun _) arg) = go is fun && (go is arg || go' is arg)
>   go' is (DBLam body) = go' (map succ is) body
>   go' _ _ = False

> triples2 :: DB -> Bool
>
> triples2 (DBLam body) = triples body
> triples2 _ = False

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

> headarg :: DB -> DB -> Maybe DB
> headarg (DBApp (DBVar 0) arg) t = Just $ subst 0 t arg
> headarg (DBApp fun arg) t = headarg fun t
> headarg _ _ = Nothing

reduction looping behaviour when duplicated

> redloop :: DB -> Bool
> redloop t@(DBLam body) = case fmap classify (headarg body t) of
>       Just (NormalForm nf) -> eqfree 0 nf t
>       _ -> t `elem` []
> redloop _ = False

Classify reduction behaviour

> classify :: DB -> BBClass DB
> classify t = go [] t where
>   go :: [DB] -> DB -> BBClass DB
>   go s (DBLam a) = DBLam <$> go s a
>   go s t@(DBApp a b) = do
>       a1 <- go s a
>       let b1 = simplify b
>       case a1 of
>           _   | doubles a1 && (doubles b1 || redloop b1) -> Diverging
>           _   | triples a1 && triples2 b1 -> Diverging
>           DBLam body
>               | any (eqfree 0 t) s -> Diverging
>               | length s > 20      -> Unknown
>               | otherwise          -> go (t:s) (subst 0 b1 body)
>           _ -> DBApp a1 <$> go s b1
>   go _ t = NormalForm t

> ponder :: Int -> DB -> IO ()
> ponder min t = do
>   -- putStrLn $ show t
>   case classify t of
>     NormalForm nf | size nf >= min -> putStrLn $ (show . size $ nf) ++ " " ++ show t ++ " ->* " ++ show nf
>     Unknown -> putStrLn $ "Unknown" ++ show t
>     -- Diverging -> putStrLn $ "Diverging" ++ show t
>     _ -> return ()

Known nonstandard loops

> loop32 :: DB
> loop32 = read "(\\ 1 (\\ 2)) (\\ 1 1 (\\ 1 2))"

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

> loop33a :: DB
> loop33a = read "\\ 1 (\\ 3 (2 1))"

Denoting the outermost variable by z, and function composition by (.),
let T = \1 (\3 (2 1)) = \x. x (\y. z (x y)) = \x. x (z.x)
let T_i = z^i . T. Then
    T T
 -> T T_1
 -> T_1 T_2
 =  z (T T_2)
 -> z (T_2 T_3)
 =  z^3 (T T_3)
 -> z^3 (T_3 T_4)
 =  z^6 (T T_4)
 -> z^6 (T_4 T_5)
 -> z^10 (T T_5)
etc.

> loop33b :: DB
> loop33b = read "\\ 1 (\\ \\ 1 (3 2))"

If we denote \x. x A as <A>, then
T = \1 (\\1 (3 2)) = \x. x (\y. <x y>)
Denote T_0 = T, and T_{i+1} = T T_i = (\y. <T_i y>) = then
T T = T T_1 = T_1 T_2 = <T T_2> = <T_2 T_3> = <<T_1 T_3>> = <<<T T_3>>> etc.

> loop34a :: DB
> loop34a = read "\\ \\ 2 (\\ 2 (3 1))"

let T = \\2 (\2 (3 1))
Denoting function composition by (.), we have T x y = x (y.x)
(\1 1) T  = T T = \y. T (y.T) = \y\z. y (T (z.y.T)) = \y\z. y (\w. z (y (T (w.z.y.T))))  etc.

> loop34b :: DB
> loop34b = read "\\ 1 (1 (\\ \\ 1 1) 1)"   (\1 1) (\1 (1 (\\1 1) 1))

Why not found before?

> loop34c :: DB
> loop34c = read "\\ \\ 2 1 (2 1)"

let T = \\2 1 (2 1) = \x.\y. x y (x y)
(\1 1 1) T = T T T = T T (T^0 T) = T T (T T) = T (T T) (T^2 T) = T T (T^2 T) ...
T T (T^i T) = T (T^i T) (T^{i+1} T) = T (T^{i-1} T) (T^{i+1} T) ... = ... = T T (T^{i+1} T) ... etc.

> tough35a :: DB
> tough35a = read "\\ \\ 2 (2 (2 1))" -- Church 3^3^3

> tough35b :: DB
> tough35b = read "\\ \\ 2 (2 (1 2))" -- size 4186155666

> excluded :: DB -> Bool
> excluded (DBLam t) = excluded t
> excluded (DBApp fun arg) = (doubles fun && arg `elem` [loop33a, loop33b, loop34a, loop34b]) || (triples fun && arg `elem` [loop34c, tough35a, tough35b])
> excluded t = t `elem` [loop32]

> main :: IO ()
> main = do
>   putStrLn . show $ loop32
>   args <- getArgs
>   case args of
>     [n] -> do
>       mapM_ (ponder 0) . filter expands . closed $ read n
>     [n,m] -> do
>       mapM_ (ponder $ read m) . filter (\t -> expands t && not (excluded t)) . closed $ read n
>       -- mapM_ (ponder 0) . filter (== read m) . filter expands . closed $ read n
>     _ -> putStrLn "usage: BB <Int>"
