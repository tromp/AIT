import Data.List

-- CoC terms with de-Bruijn indices
data Expr = Star | Box | Var Int | Lam Expr Expr | Pi Expr Expr | App Expr Expr deriving (Eq, Ord)

instance Show Expr where
  show Star = "*"
  show Box = "[]"
  show (Var i) = show i
  show (Lam ta tb) = "\\" ++ show ta ++ ". " ++ show tb
  show (Pi ta tb) = "(" ++ show ta ++ " -> " ++ show tb ++ ")"
  show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"

-- type of free variables
type Context = [Expr]

-- Judgement of a term having a type in a context
data Judge = Judge Expr Expr Context deriving (Eq, Ord)

instance Show Judge where
  show (Judge trm typ ctx) = "\n  " ++ (intercalate ", " (map show.reverse$ctx)) ++ " |- " ++ show trm ++ " : " ++ show typ ++ "\n"

-- nat :: Expr
-- Nat = forall(a : *) -> (a -> a) -> a -> a
-- Nat = forall(a : *) -> forall(_ : (forall(_ : a -> a)) -> forall(_ : a) -> a
-- nat = Pi Star (Pi (Pi (Var 1) (Var 1)) (Pi (Var 1) (Var 1)))

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

-- using rules from https://hbr.github.io/Lambda-Calculus/cc-tex/cc.pdf
-- rule 1.(a) Axiom
axiom = [Judge Star Box []]

-- rule 1.(b) Variable
iVar :: Judge -> [Judge]
iVar (Judge trm typ ctx) = [Judge (Var 0) (lift trm) (trm:ctx) | isSort typ]

-- rule 1.(c) Product -- doesn't check typ is well-typed
iProd :: Judge -> [Judge]
iProd (Judge trm typ (tp:ctx)) = [Judge (Pi tp trm) typ ctx | not (isSort typ)]
iProd _ = []

-- rule 1.(d) Abstraction -- doesn't check typ is well-typed
iLam :: Judge -> [Judge]
iLam (Judge trm typ (tp:ctx)) = [Judge (Lam tp trm) (Pi tp typ) ctx | not (isSort typ)]
iLam _ = []

-- rule 1.(e) Application
iApp :: Judge -> Judge -> [Judge]
iApp (Judge f (Pi t tb) ctx) (Judge a ta ctx2) | ctx == ctx2 && t == ta = [Judge (App f a) (subst 0 a 1 tb) ctx]
iApp _ _ = []

-- rule 2.(a) Weaken:
weaken :: Judge -> Judge -> [Judge]
weaken (Judge trm typ ctx) (Judge trm2 srt ctx2) | ctx == ctx2 && isSort srt = [Judge (lift trm) (lift typ) (trm2:ctx)]
weaken _ _ = []

-- generate judegments of given size
gen :: Int -> [Judge]
gen 0 = []
gen 1 = axiom
gen n = do
          j1 <- gen (n-1)
          iVar j1 ++ iProd j1 ++ iLam j1
        ++ do
          i <- [1..n-1]
          j1 <- gen i
          j2 <- gen (n-i-1)
          iApp j1 j2 ++ weaken j1 j2

main = mapM_ (print . gen) [1..5]
