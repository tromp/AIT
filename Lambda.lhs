The Lambda module implements a simple abstract syntax for
$\lambda$-calculus together with a parser and a printer for it.
It also exports a simple type of identifiers that parse and
print in a nice way.

> {-# LANGUAGE PatternSynonyms, LambdaCase #-}
> module Lambda(LC(..), DB(..), CL(..),  Id(..), lam, isnf, nf, hnf, evalLC, toLC, toCL, toCLOK, strongCL, toDB, showBCW, toBCW) where
> import Prelude hiding ((<>))
> import Data.List(union, (\\), elemIndex)
> import Data.Char(isAlphaNum)
> import Text.PrettyPrint.HughesPJ(Doc, renderStyle, style, text, (<>), (<+>), parens)
> import Text.ParserCombinators.ReadP

The LC type of $\lambda$ term is parametrized over the type of the variables.
It has constructors for variables, $\lambda$-abstraction, and application.

> data LC v = Var v | Lam v (LC v) | App (LC v) (LC v)
>    deriving (Eq)

The Read instance for the LC type reads $\lambda$ term with the normal
syntax.

> instance (Eq v, Read v) => Read (LC v) where
>     readsPrec _ = readP_to_S pLC . stripComments

> stripComments :: String -> String
> stripComments "" = ""
> stripComments ('-':'-':cs) = skip cs
>   where skip "" = ""
>         skip s@('\n':_) = stripComments s
>         skip (_:s) = skip s
> stripComments (c:cs) = c : stripComments cs

A ReadP parser for $\lambda$-expressions.

> pLC, pLCAtom, pLCVar, pLCLam, pLCApp :: (Eq v, Read v) => ReadP (LC v)
> pLC = pLCLam +++ pLCApp +++ pLCLet
>
> pLCVar = do
>     v <- pVar
>     return $ Var v
>
> pLCLam = do
>     schar '\\'
>     v <- pVar
>     optional $ schar '.'
>     e <- pLC
>     return $ Lam v e
>
> pLCApp = do
>     es <- many1 pLCAtom
>     return $ foldl1 App es
>
> pLCAtom = pLCVar +++ (do schar '('; e <- pLC; schar ')'; return e)

To make expressions a little easier to read we also allow let expression
as a syntactic sugar for $\lambda$ and application.

> fix :: (Eq v, Read v) => LC v
> fix = read "\\f (\\x x x) (\\x f (x x))"

> letrec :: (Eq v, Read v) => v -> LC v -> LC v
> letrec x e | x `elem` freeVars e = App fix (Lam x e)
>            | otherwise = e

Compute the free variables of an expression.

> freeVars :: (Eq v) => LC v -> [v]
> freeVars (Var v) = [v]
> freeVars (Lam v e) = freeVars e \\ [v]
> freeVars (App f a) = freeVars f `union` freeVars a

> lcLet :: (Eq v, Read v) => (v, LC v) -> LC v -> LC v
> lcLet (x,e) b = App (Lam x b) (letrec x e)

> pLCLet :: (Eq v, Read v) => ReadP (LC v)
> pLCLet = do
>     let pDef = do
>          v <- pVar
>          schar '='
>          e <- pLC
>          return (v, e)
>     sstring "let"
>     bs <- sepBy pDef (schar ';')
>     optional (schar ';')
>     sstring "in"
>     e <- pLC
>     return $ foldr lcLet e bs

> schar :: Char -> ReadP ()
> schar c = do skipSpaces; _ <- char c; return ()
>
> eow :: ReadP ()
> eow = readS_to_P $ \s -> case s of
>     c:_ | isAlphaNum c -> []
>     _ -> [((),s)]
>
> sstring :: String -> ReadP ()
> sstring c = do skipSpaces; _ <- string c; eow; return ()
>
> pVar :: (Read v) => ReadP v
> pVar = do skipSpaces; readS_to_P (readsPrec 9)

Pretty print $\lambda$-expressions when shown.

> instance (Show v) => Show (LC v) where
>     show = renderStyle style . ppLC 0
>
> ppLC :: (Show v) => Int -> LC v -> Doc
> ppLC _ (Var v) = text $ show v
> ppLC p (Lam v e) = pparens (p>0) $ text ("\\" ++ show v ++ ".") <> ppLC 0 e
> ppLC p (App f a) = pparens (p>1) $ ppLC 1 f <+> ppLC 2 a

> pparens :: Bool -> Doc -> Doc
> pparens True d = parens d
> pparens False d = d

The Id type of identifiers.

> newtype Id = Id String
>     deriving (Eq, Ord)

Identifiers print and parse without any adornment.

> instance Show Id where
>     show (Id i) = i

> instance Read Id where
>     readsPrec _ s =
>         case span (\c -> isAlphaNum c || c=='_' || c=='\'') s of
>         ("", _) -> []
>         (i, s') -> [(Id i, s')]


> data DB = DBVar Int | DBLam DB | DBApp DB DB deriving (Eq)

With higher order abstract syntax, the abstraction in the implemented
language is represented by an abstraction in the implementation
language.

Pretty print de Bruijn terms when shown.

> instance Show DB where
>     show = renderStyle style . ppDB 0
>
> ppDB :: Int -> DB -> Doc
> ppDB _ (DBVar   v) = text $ show (v+1)
> ppDB p (DBLam   e) = pparens (p>0) $ text ("\\") <> ppDB 0 e
> ppDB p (DBApp f a) = pparens (p>1) $ ppDB 1 f <+> ppDB 2 a

The Read instance for the DB type reads DB term with the normal
syntax.

> instance Read DB where
>     readsPrec _ = readP_to_S pDB

A ReadP parser for DeBruijn term

> pDB, pDBAtom, pDBVar, pDBLam, pDBApp :: ReadP DB
> pDB = pDBLam +++ pDBApp
>
> pDBVar = do
>     skipSpaces
>     v <- readS_to_P (readsPrec 9)
>     return $ DBVar (v-1)
>
> pDBLam = do
>     schar '\\'
>     e <- pDB
>     return $ DBLam e
>
> pDBApp = do
>     es <- many1 pDBAtom
>     return $ foldl1 DBApp es
>
> pDBAtom = pDBVar +++ (do schar '('; e <- pDB; schar ')'; return e)

The following data type facilitates the Normal Form function by
using Higher Order Abstract Syntax (HOAS) for the $\lambda$-expressions.
This makes it possible to use the native substitution of Haskell.

> data HODB = HVar Int | HLam (HODB -> HODB) | HApp HODB HODB

Is a term already in normal form?

> isnf :: DB -> Bool
> isnf (DBVar   _) = True
> isnf (DBLam   e) = isnf e
> isnf (DBApp (DBLam _) _) = False
> isnf (DBApp f a) = isnf f && isnf a

To compute the normal form, first convert/compute to HODB, and
convert back.

> nf :: DB -> DB
> nf = toDB . toLC . evalLC

Head Normal Form

> hnf :: DB -> DB
> hnf v@(DBVar _) = v
> hnf (DBLam e) = DBLam (hnf e)
> hnf (DBApp f a) = case hnf f of
>   DBLam e -> hnf (subst 0 e a)
>   f'      -> DBApp f' a

> subst :: Int -> DB -> DB -> DB
> subst i (DBVar j)   c = if i == j then c else DBVar (if j > i then j-1 else j)
> subst i (DBApp a b) c = DBApp (subst i a c) (subst i b c)
> subst i (DBLam a)   c = DBLam (subst (i+1) a (incv 0 c))

> incv :: Int -> DB -> DB
> incv i (DBVar j)   = DBVar (if i <= j then j+1 else j)
> incv i (DBApp a b) = DBApp (incv i a) (incv i b)
> incv i (DBLam a)   = DBLam (incv (i+1) a)

Convert/compute to higher order abstract syntax. Do this by keeping
a mapping of the bound variables and translating them as they
are encountered.

> evalLC :: DB -> HODB
> evalLC = eval []
>   where eval m (DBVar   i) = m!!i
>         eval m (DBLam   e) = HLam $ \ x -> eval (x:m) e
>         eval m (DBApp f a) = app (eval m f) (eval m a)

The substitution step for HODB is simply a Haskell application since we
use a Haskell function to represent the abstraction.

> app :: HODB -> HODB -> HODB
> app (HLam b) = b
> app f = HApp f

Convert to de-Bruijn form. The variables are looked up in a dictionary
(we use a list here) to find the de-Bruijn indices.

> toDB :: (Eq v, Show v) => LC v -> DB
> toDB = from []
>   where from vs (Var   v) = DBVar $ maybe (error $ "Unbound variable " ++ show v) id $ elemIndex v vs
>         from vs (Lam v t) = DBLam $ from (v:vs) t
>         from vs (App l r) = DBApp (from vs l) (from vs r)

convenience function for constructing LC Int directly
from http://pchiusano.github.io/2014-06-20/simple-debruijn-alternative.html

> lam :: (LC Int -> LC Int) -> LC Int
> lam f = Lam n body where
>   body = f (Var n)
>   n = 1 + maxBV body
>   maxBV :: LC Int -> Int
>   maxBV (App fun a) = maxBV fun `max` maxBV a
>   maxBV (Lam m _) = m
>   maxBV (Var _) = error "Term not closed"

Convert back from higher order abstract syntax. Do this by inventing
a new variable at each $\lambda$.

> toLC :: HODB -> LC Int
> toLC = to 0
>   where to _ (HVar   v) = Var v
>         to n (HLam   b) = Lam n (to (succ n) (b (HVar n)))
>         to n (HApp f a) = App (to n f) (to n a)


The CL type of combinatory expressions has constructors for index variables, primitive combinators S and K, and application.

> data CL = CVar Int | CombS | CombK | CApp CL CL deriving (Eq)

> instance Show CL where
>     show = renderStyle style . ppCL 0
>
> ppCL :: Int -> CL -> Doc
> ppCL _ (CVar v) = text $ show v
> ppCL _ CombS = text "S"
> ppCL _ CombK = text "K"
> ppCL p (CApp f a) = pparens (p>1) $ ppCL 1 f <+> ppCL 2 a

Decrease variable depth

> drip :: CL -> CL
> drip i@(CApp CombSK _) = i -- ignore SK argument
> drip (CVar 0) = error "Can't drip CVar 0"
> drip (CVar i) = CVar (i-1)
> drip (CApp x y) = CApp (drip x) (drip y)
> drip x = x

Increase variable depth

> bump :: CL -> CL
> bump (CVar i) = CVar (i+1)
> bump (CApp x y) = CApp (bump x) (bump y)
> bump x = x

Oleg Kiselyov's compositional bracket abstraction
as explained on https://crypto.stanford.edu/~blynn/lambda/kiselyov.html

> toCLOK :: DB -> CL
> toCLOK db = if lvl==0 then cl else error "Kiselyov abstraction failed" where
>   (lvl,cl) = convert db
>   convert :: DB -> (Int, CL)
>   convert = \case
>     DBVar 0 -> (1, CombI)
>     DBVar e -> (n + 1, (0, CombK) # t) where t@(n, _) = convert $ DBVar (e-1)
>     DBLam e -> case convert e of
>       (0, d) -> (0, abstract d)                                         -- K d
>       (n, d) -> (n - 1, d)
>     DBApp e1 e2 -> (max n1 n2, t1 # t2) where
>       t1@(n1, _) = convert e1
>       t2@(n2, _) = convert e2
>   (0 , d1) # (0 , d2) = CApp d1 d2
>   (0 , d1) # (n , d2) = (0, CApp CombS (CApp CombK d1)) # (n - 1, d2)   -- B d1 where Bxyz=x(yz)
>   (n , d1) # (0 , d2) = (0, CApp CombSS (CApp CombK (CApp CombK d2))) # (n - 1, d1) -- R d2 where Rxyz=yzx
>   (n1, d1) # (n2, d2) = (n1 - 1, (0, CombS) # (n1 - 1, d1)) # (n2 - 1, d2)

Implement improved bracket abstraction:

> toCL :: DB -> CL
> toCL (DBVar i) = CVar i
> toCL (DBApp x y) = CApp (toCL x) (toCL y)
> toCL (DBLam e) = abstract (toCL e)

> abstract :: CL -> CL

[x] (S K M) ≡ S K (for all M)

> abstract (CApp sk@CombSK _) = sk
> abstract e = if freeIn (==0) e
>              then occabstract e

[x] M ≡ K M (x not in M)

>              else CApp CombK (drip e) where
>   freeIn _ (CApp CombSK _) = False
>   freeIn fv (CApp x y) = freeIn fv x || freeIn fv y
>   freeIn fv (CVar i) = fv i
>   freeIn _ _ = False

>   isConst = not . freeIn (const True)

[x] x ≡ I

>   occabstract (CVar 0) = CombI

[x] (M x) ≡ M (x not in M)

>   occabstract (CApp m (CVar 0)) | not (freeIn (==0) m) = drip m

[x] (L M L) ≡ [x] (S S K L M) (x in L)

>   occabstract (CApp (CApp l m) l') | l == l' -- && freeIn (==0) e1
>       = occabstract (CApp (CApp CombSSK l) m)

[x] (M (N L)) ≡ [x] (S ([x] M) N L) (M, N combinators)

>   occabstract (CApp m (CApp n l)) | isConst m && isConst n
>       = occabstract (CApp (CApp (CApp CombS (abstract m)) n) l)

Since S (K M) (S (K N) L) x = M (N (L x)) = (S (K M) N) (L x) = S (K (S (K M) N)) L x:
[x] (S (K M) (S (K N) L)) ≡ [x] (S (K (S (K M) N))) L

>   occabstract (CApp (CApp CombS (CApp CombK m)) (CApp (CApp CombS (CApp CombK n)) l))
>       = occabstract (CApp (CApp CombS (CApp CombK (CApp (CApp CombS (CApp CombK m)) n)))l)

≡ [x] (S (K (S (K M) N))) L (M, N combinators)

[x] ((M N) L) ≡ [x] (S M ([x] L) N) (M, L combinators)

>   occabstract (CApp (CApp m n) l) | isConst m && isConst l
>       = occabstract (CApp (CApp (CApp CombS m) (abstract l)) n)

[x] ((M L) (N L)) ≡ [x] (S M N L) (M, N combinators)

>   occabstract (CApp (CApp m l) (CApp n l')) | l == l' && isConst m && isConst n
>       = occabstract (CApp (CApp (CApp CombS m) n) l)

[x] (M N) ≡ S ([x] M) ([x] N)

>   occabstract (CApp e1 e2)
>       = CApp (CApp CombS (abstract e1)) (abstract e2)
>   occabstract _ = error $ "Impossible occabstract argument"

> evalCL :: CL -> CL
> evalCL (CApp x y) = eval2 (evalCL x) (evalCL y) where
>   eval2 (CApp CombK u) _ = u
>   eval2 (CApp (CApp CombS u) v) w = eval2 (eval2 u w) (eval2 v w)
>   eval2 u v = CApp u v
> evalCL x = x

> strongCL :: CL -> CL
> strongCL = strong . evalCL where
>   strong (CApp CombK x) = abstract (strong x)
>   strong f@(CApp (CApp CombS _) _) = abstract . strongCL $ CApp (bump f) (CVar 0)
>   strong f@(CApp CombS _) = abstract . abstract . strongCL $ CApp (CApp (bump(bump f)) (CVar 1)) (CVar 0)
>   strong (CApp x y) = CApp (strong x) (strong y)
>   strong x = x

BCWI+K terms: We reuse the CL type and represent combinators by their respective SK translation.

> pattern CombSK, CombSS, CombSSK :: CL
> pattern CombSK = CApp CombS CombK
> pattern CombSS = CApp CombS CombS
> pattern CombSSK = CApp CombSS CombK

> type BCW = CL

> pattern CombI, CombB, CombC, CombW :: BCW
> pattern CombI = CApp CombSK CombK
> pattern CombB = CApp (CApp CombS (CApp CombK CombS)) CombK
> pattern CombC = CApp (CApp CombS (CApp CombK (CApp (CApp CombS (CApp CombK (CApp (CApp CombS CombS) (CApp CombK CombK)))) CombK))) CombS
> pattern CombW = CApp (CApp CombS CombS) CombSK

> showBCW :: BCW -> String
> showBCW = renderStyle style . ppBCW 0
>
> ppBCW :: Int -> BCW -> Doc
> ppBCW _ (CVar v) = text $ show v
> ppBCW _ CombI = text "I"
> ppBCW _ CombB = text "B"
> ppBCW _ CombC = text "C"
> ppBCW _ CombW = text "W"
> ppBCW _ CombS = text "S"
> ppBCW _ CombK = text "K"
> ppBCW p (CApp f a) = pparens (p>1) $ ppBCW 1 f <+> ppBCW 2 a

> abstractBCW :: BCW -> BCW
> abstractBCW e = if freeIn (==0) e
>              then occabstract e
>              else CApp CombK (drip e) where
>   freeIn fv (CApp x y) = freeIn fv x || freeIn fv y
>   freeIn fv (CVar i) = fv i
>   freeIn _ _ = False
>   occabstract (CVar 0) = CombI
>   occabstract (CApp e1 (CVar 0))
>       | not (freeIn (==0) e1) = drip e1
>       | otherwise = CApp CombW (abstractBCW e1)
>   occabstract (CApp e1 e2)
>       = case (freeIn (==0) e1, freeIn (==0) e2) of
>           (False, True ) -> combB (drip e1) (abstractBCW e2)
>           (True,  False) -> combC (abstractBCW e1) (drip e2)
>           (True,  True ) -> combS (abstractBCW e1) (abstractBCW e2)
>           (False, False) -> error $ "Impossible free variable in occabstract"
>   occabstract _ = error $ "Impossible occabstract argument"
>   combS a b = CApp CombW (CApp (CApp CombB (CApp CombC a)) b)
>   -- combS a b = CApp (CApp CombS a) b
>   combB a b = CApp (CApp CombB a) b
>   combC a b = CApp (CApp CombC a) b

> toBCW :: DB -> BCW
> toBCW (DBVar i) = CVar i
> toBCW (DBApp x y) = CApp (toBCW x) (toBCW y)
> toBCW (DBLam e) = abstractBCW (toBCW e)
