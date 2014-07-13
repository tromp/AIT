The Lambda module implements a simple abstract syntax for
$\lambda$-calculus together with a parser and a printer for it.
It also exports a simple type of identifiers that parse and
print in a nice way.

> module Lambda(LC(..), DB(..), CL(..),  Id(..), nf, toCL, strongCL, toDB) where
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
>     sstring "in"
>     e <- pLC
>     return $ foldr lcLet e bs

> schar :: Char -> ReadP Char
> schar c = do skipSpaces; char c
>
> eow :: ReadP ()
> eow = readS_to_P $ \s -> case s of
>     c:_ | isAlphaNum c -> []
>     _ -> [((),s)]
>
> sstring :: String -> ReadP String
> sstring c = do skipSpaces; r <- string c; eow; return r
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
>         case span (\c -> isAlphaNum c || c=='_') s of
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

The following data type facilitates the Normal Form function by
using Higher Order Abstract Syntax for the $\lambda$-expressions.
This makes it possible to use the native substitution of Haskell.

> data HODB = HVar Int | HLam (HODB -> HODB) | HApp HODB HODB

To compute the normal form, first convert/compute to HODB, and
convert back.

> nf :: DB -> DB
> nf = toDB . toLC . evalLC

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
>   maxBV (App f a) = maxBV f `max` maxBV a
>   maxBV (Lam n _) = n

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

> combI :: CL
> combI = CApp (CApp CombS CombK) CombK

> drip :: CL -> CL
> drip i@(CApp (CApp CombS CombK) _) = i
> drip (CVar 0) = error "Can't drip CVar 0"
> drip (CVar i) = CVar (i-1)
> drip (CApp x y) = CApp (drip x) (drip y)
> drip x = x

> bump :: CL -> CL
> bump (CVar i) = CVar (i+1)
> bump (CApp x y) = CApp (bump x) (bump y)
> bump x = x

> abstract :: CL -> CL
> abstract (CApp sk@(CApp CombS CombK) _) = sk
> abstract e = if freeIn (==0) e
>              then occabstract e
>              else CApp CombK (drip e) where
>   freeIn _ (CApp (CApp CombS CombK) _) = False
>   freeIn fv (CApp x y) = freeIn fv x || freeIn fv y
>   freeIn fv (CVar i) = fv i
>   freeIn _ _ = False
>   isConst = not . freeIn (const True)
>   occabstract (CVar 0) = combI
>   occabstract (CApp e1 (CVar 0)) | not (freeIn (==0) e1) = drip e1
>   occabstract (CApp e1 (CApp e2 e3)) | isConst e1 && isConst e2
>       = occabstract (CApp (CApp (CApp CombS (abstract e1)) e2) e3)
>   occabstract (CApp (CApp e1 e2) e3) | isConst e1 && isConst e3
>       = occabstract (CApp (CApp (CApp CombS e1) (abstract e3)) e2)
>   occabstract (CApp e1 e2)
>       = CApp (CApp CombS (abstract e1)) (abstract e2)
>   occabstract _ = error $ "Impossible occabstract argument"

> toCL :: DB -> CL
> toCL (DBVar i) = CVar i
> toCL (DBApp x y) = CApp (toCL x) (toCL y)
> toCL (DBLam e) = abstract (toCL e)

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
