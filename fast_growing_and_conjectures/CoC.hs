import Data.List
import Control.Monad
import Debug.Trace

-- HOAS CoC terms with de-Bruijn level for show
data Closed = Box | Star | Var Integer | Lam Closed (Closed -> Closed) | Pi Closed (Closed -> Closed)| App Closed Closed

-- show terms by passing de-Bruijn levels into pi and lambda functions
instance Show Closed where
  show = showi 0 where
    showi n (Pi ta tb)  = "Π" ++ showi n ta ++ "." ++ showi (n+1) (tb (Var n))
    showi n (Lam ta tb) = "λ" ++ showi n ta ++ "." ++ showi (n+1) (tb (Var n))
    showi n (App f a)   = "(" ++ showi n  f ++ " " ++ showi n a ++ ")"
    showi _ Box  = "□"
    showi _ Star = "*"
    showi n (Var i) = show (n-1-i)

-- number of bits in binary encoding
size :: Closed -> Integer
size = sz 0 where
  sz n (Lam ta tb) = 3 + sz n ta + sz (n+1) (tb (Var n))
  sz n (Pi ta tb) = 3 + sz n ta + sz (n+1) (tb (Var n))
  sz n (App f a) = 2 + sz n f + sz n a
  sz n Box = 3
  sz n Star = 3
  sz n (Var i) = 3+(n-1-i)

-- environments for binding free variables
type Env = [Closed]

-- type of environment dependent term
type Open = Env -> Closed

close :: Open -> Closed
close ot = ot [Var i | i<-[-1,-2..]]

lift :: Open -> Open
lift = ( . drop 1)

isSort :: Open -> Bool
isSort ot = case close ot of
  Box  -> True
  Star -> True
  otherwise -> False

type Context = [Open]

eqC :: Context -> Context -> Bool
eqC ctx1 ctx2 = map (show.close) ctx1 == map (show.close) ctx2

eqT :: Open -> Open -> Bool
eqT ot1 ot2 = (show.close) ot1 == (show.close) ot2

-- Judgement of a term having a type in a context
data Judge = Judge Open Open Context

instance Show Judge where
  show (Judge trm typ ctx) = -- (size trm) ++ "\t" ++
    (intercalate ", " (map (show.close).reverse$ctx)) ++ " |- " ++ show (close trm) ++ " : " ++ show (close typ)

-- use rule numbers from both
-- https://googology.fandom.com/wiki/User_blog:Upquark11111/An_Explanation_of_Loader's_Number
-- and https://hbr.github.io/Lambda-Calculus/cc-tex/cc.pdf
-- rule 1. / 1.(a) Axiom		----------
--					Γ |- * : □
axiom = [Judge (const Star) (const Box) []]

-- rule 2. / 1.(b) Variable		  Γ |- X : K
--					--------------
--					Γ,x:X |- x : X
iVar :: Judge -> [Judge]
iVar (Judge trm srt ctx)= [Judge (\(hd:_)->hd) (lift trm) (trm:ctx) | isSort srt]

-- rule 3. / 2.(a) Weaken:		Γ |- X : Y       Γ |- S : K
--					---------------------------
--					       Γ,x:S |- X : Y
weaken :: Judge -> Judge -> [Judge]
weaken (Judge trm typ ctx) (Judge trm2 srt ctx2) = [Judge (lift trm) (lift typ) (trm2:ctx) | eqC ctx ctx2 && isSort srt]

-- rule 4. / 1.(d) Abstraction		      Γ,x:A |- X : Y
--					-------------------------
--					Γ |- (λx:A. X) : (Πx:A. Y)
iLam :: Judge -> [Judge]
iLam (Judge trm typ (tp:ctx)) = [Judge (\env->Lam (tp env) (\x->trm (x:env)))
                                       (\env-> Pi (tp env) (\x->typ (x:env)))
                                       ctx | not (isSort typ)]
iLam _ = []

-- rule 5 / 1.(c) Product		  Γ,x:A |- X : K
--					------------------
--					Γ |- (Πx:A. X) : K
iProd :: Judge -> [Judge]
iProd (Judge trm srt (tp:ctx)) = [Judge (\env-> Pi (tp env) (\x->trm (x:env))) srt ctx | isSort srt]
iProd _ = []

-- apply function to argument and normalize
apply :: Open -> Open -> Open
apply f a = \env -> let { fe = f env; ae = a env } in case fe of
  (Lam ta fb) -> fb ae
  (Pi  ta fb) -> fb ae
  _           -> App fe ae

-- rule 6. / 1.(e) Application		Γ |- X : (Πx:T. Z)     Γ |- S : T
--					---------------------------------
--					      Γ |- (X S) : Z[x := S]
iApp :: Judge -> Judge -> [Judge]
iApp (Judge f ot ctx) (Judge a ta ctx2) = [Judge (apply f a) (apply ot a) ctx
                                          | (Pi t fb) <- [close ot], eqC ctx ctx2 && eqT (const t) ta]

-- generate judgements in dumb way
gen0 :: [[Judge]]
gen0 = iterate xpand [] where
  xpand prev = (do
                 j1@(Judge _ _ ctx1) <- prev
                 j2@(Judge _ _ ctx2) <- prev
                 guard $ eqC ctx1 ctx2
                 -- trace ("\t\t"++show j1++"\t"++show j2) $
                 weaken j1 j2 ++ iApp j1 j2 ++ iProd j2 ++ iLam j2 ++ iVar j2
               ) ++ axiom

-- generate judgements of given size
gen :: [[Judge]]
gen = [] : axiom : map geni [2..] where
  geni n = do
             j1 <- gen !! (n-1)
             iVar j1 ++ iProd j1 ++ iLam j1
           ++ do
             i <- [1..n-1]
             j1 <- gen !! i
             j2 <- gen !! (n-i-1)
             iApp j1 j2 ++ weaken j1 j2

altmain = putStrLn "Look Ma, no subst " >> mapM_ (\(i,l) -> do
         putStr "EXPAND "
         print i
         mapM_ print l
         putStr "length "
         print $ length l
         putStr "sumsize "
         print . sum . map (\(Judge trm _ _) -> 1 + size (close trm)) $ l
       ) (zip [0..6] gen0)

derive :: Integer -> String
derive n = show n ++ "^" ++ show (foldr (\(Judge trm _ _) b -> b * size (close trm)) 1 (gen0!!fromIntegral n))

main = mapM_ (\n -> putStrLn $ "derive " ++ show n ++ " = " ++ derive n) [0..]

{--
Rules

1.  ----------				Axiom
    Γ |- * : □

      Γ |- X : K
2.  --------------			Variable
    Γ,x:X |- x : X

    Γ |- X : Y       Γ |- S : K
3.  ---------------------------		Weaken
           Γ,x:S |- X : Y

           Γ,x:A |- X : Y
4.  -------------------------		Abstraction
    Γ |- (λx:A. X) : (Πx:A. Y)

      Γ,x:A |- X : K
5.  ------------------			Product
    Γ |- (Πx:A. X) : K

    Γ |- X : (Πx:T. Z)     Γ |- S : T
6.  ---------------------------------	Application
           Γ |- (X S) : Z[x := S]

Proof of 0 : nat

(0)		|- * : □					R1		1
(1)	      *	|- 0 : *					R2(1)		2
(2)	    *,0	|- 1 : *					R3(1,1)		5
(3)	      *	|- Π0.1 : *					R5(2)		6
(4)	 *,Π0.1 |- 1 : *					R3(1,3)		9
(5)    *,Π0.1,1 |- 0 : 2					R2(4)		10
(6)	 *,Π0.1 |- λ1.0 : Π1.2					R4(5)		11
(7)	      * |- λΠ0.1.λ1.0 : ΠΠ0.1.Π1.2			R4(6)A		12
(8)		|- λ*.λΠ0.1.λ1.0 : Π*.ΠΠ0.1.Π1.2		R4(7)		13

Proof of 0 : nat (i.e. |- λ*.λΠ0.1.λ1.   0  : Π*.ΠΠ0.1.Π1.2) requires 13 rules
Proof of 1 : nat (i.e. |- λ*.λΠ0.1.λ1.(1 0) : Π*.ΠΠ0.1.Π1.2) requires 31 rules

--}
