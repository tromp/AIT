import Data.List hiding ((\\))
import Data.Set hiding (map, size, foldr)
import Control.Monad
import Debug.Trace

-- CoC terms with de-Bruijn indices
data Expr = Star | Box | Var Int | Lam Expr Expr | Pi Expr Expr | App Expr Expr deriving (Eq, Ord)

instance Show Expr where
  show (Pi ta tb)  = "Π" ++ show ta ++ "." ++ show tb
  show (Lam ta tb) = "λ" ++ show ta ++ "." ++ show tb
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"
  show Box = "□"
  show Star = "*"
  show (Var i) = show i

-- number of binary encoding
size :: Expr -> Int
size (Lam ta tb) = 3 + size ta + size tb
size (Pi ta tb) = 3 + size ta + size tb
size (App f a) = 2 + size f + size a
size Box = 3
size Star = 3
size (Var i) = 3 + 2*i

-- type of free variables
type Context = [Expr]

-- Judgement of a term having a type in a context
data Judge = Judge Expr Expr Context deriving (Eq, Ord)

instance Show Judge where
  show (Judge trm typ ctx) = -- (size trm) ++ "\t" ++
    (intercalate ", " (map show.reverse$ctx)) ++ " |- " ++ show trm ++ " : " ++ show typ

--type of natural numbers
nat :: Expr
-- Nat = forall(a : *) -> (a -> a) -> a -> a
-- Nat = forall(a : *) -> forall(_ : (forall(_ : a -> a)) -> forall(_ : a) -> a
nat = Pi Star (Pi (Pi (Var 0) (Var 1)) (Pi (Var 1) (Var 2)))

zero :: Expr
zero = Lam Star (Lam (Pi (Var 0) (Var 1)) (Lam (Var 1) (Var 0)))

suck :: Expr
-- > S = \n:nat. \a:T. \f:(a -> a). \x:a. f (n a f x)
suck = Lam nat (Lam Star (Lam (Pi (Var 0) (Var 1)) (Lam (Var 1) (App (Var 1) (App (App (App (Var 3) (Var 2)) (Var 1)) (Var 0))))))

one :: Expr
one = Lam Star (Lam (Pi (Var 0) (Var 1)) (Lam (Var 1) (App (Var 1) (Var 0))))

two :: Expr
two = Lam Star (Lam (Pi (Var 0) (Var 1)) (Lam (Var 1) (App (Var 1) (App (Var 1) (Var 0)))))

three :: Expr
three = Lam Star (Lam (Pi (Var 0) (Var 1)) (Lam (Var 1) (App (Var 1) (App (Var 1) (App (Var 1) (Var 0))))))

pow :: Expr
pow = Lam nat (Lam nat (Lam Star (App (App (Var 1) (Var 0)) (App (Var 2) (Var 0)))))

-- substitute expression for bound variable and normalize, subtract a delta from larger vars
subst :: Int -> Expr -> Int -> Expr -> Expr
subst v e d (Var v')    | v == v' = e
subst v e d (Var v')    | v  < v' = Var (v' - d)
subst v e d (Lam ta b )           = Lam (subst v e d ta) (subst (succ v) (lift e) d b )
subst v e d (Pi  ta tb)           = Pi  (subst v e d ta) (subst (succ v) (lift e) d tb)
subst v e d (App f a)             = apply (subst v e d f) (subst v e d a)
subst v e d e' = e'

-- apply function to argument and normalize
apply :: Expr -> Expr -> Expr
apply (Lam ta b) a = subst 0 a 1 b
apply f a = App f a

lift :: Expr -> Expr
lift = subst 0 (Var 1) (-1)

isSort :: Expr -> Bool
isSort t = t == Star || t == Box

-- use rule numbers from both
-- https://googology.fandom.com/wiki/User_blog:Upquark11111/An_Explanation_of_Loader's_Number
-- and https://hbr.github.io/Lambda-Calculus/cc-tex/cc.pdf
-- rule 1. / 1.(a) Axiom
axiom = [Judge Star Box []]

-- rule 2. / 1.(b) Variable
iVar :: Judge -> Judge -> [Judge]
iVar (Judge _ _ _) (Judge trm srt ctx)= [Judge (Var 0) (lift trm) (trm:ctx) | isSort srt]

-- rule 3. / 2.(a) Weaken:
weaken :: Judge -> Judge -> [Judge]
weaken (Judge trm typ ctx) (Judge trm2 srt ctx2) = [Judge (lift trm) (lift typ) (trm2:ctx) | ctx==ctx2 && isSort srt]

-- rule 4. / 1.(d) Abstraction -- doesn't check typ is well-typed
iLam :: Judge -> Judge -> [Judge]
iLam (Judge _ _ _) (Judge trm typ (tp:ctx)) = [Judge (Lam tp trm) (Pi tp typ) ctx | not (isSort typ)]
iLam _ _ = []

-- rule 5 / 1.(c) Product -- doesn't check typ is well-typed
iProd :: Judge -> Judge -> [Judge]
iProd (Judge _ _ _) (Judge trm srt ctx1@(tp:ctx)) = [Judge (Pi tp trm) srt ctx | isSort srt]
iProd _ _ = []

-- rule 6. / 1.(e) Application
iApp :: Judge -> Judge -> [Judge]
iApp (Judge f (Pi t tb) ctx) (Judge a ta ctx2) = [Judge (apply f a) (subst 0 a 1 tb) ctx | ctx==ctx2 && t==ta]
iApp _ _ = []

-- generate judgements in dumb way
gen0 :: [[Judge]]
gen0 = iterate xpand [] where
  xpand prev = (do
                 j1@(Judge _ _ ctx1) <- prev
                 j2@(Judge _ _ ctx2) <- prev
                 guard $ ctx1 == ctx2
                 -- trace ("\t\t"++show j1++"\t"++show j2) $
                 weaken j1 j2 ++ iApp j1 j2 ++ iProd j1 j2 ++ iLam j1 j2 ++ iVar j1 j2
               ) ++ axiom

-- generate judgements of given size
gen :: [[Judge]]
gen = [] : axiom : map geni [2..] where
  geni n = toList . (\s -> foldr prune s [1..n-1]) . fromList $ do
             i <- [1..n-1]
             j1 <- gen !! i
             j2 <- gen !! (n-i-1)
             iApp j1 j2 ++ weaken j1 j2 ++ iVar j1 j2 ++ iProd j1 j2 ++ iLam j1 j2
  prune i s = s \\ fromList (gen!!i)

main = mapM_ (\(i,l) -> do
         putStr "EXPAND "
         print i
         mapM_ print l
         putStr "sumsize "
         print . sum . map (\(Judge trm _ _) -> 1 + size trm ) $ l
       ) (zip [0..5] gen0)
