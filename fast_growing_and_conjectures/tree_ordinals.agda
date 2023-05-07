-- Tree ordinals and Wainer's `tau`.
--
-- cf. https://www.youtube.com/watch?v=qP9d_-H46Ww (and previous videos)
-- which is presumably based on Cichon and Wainer, "The slow-growing and
-- the Grzegorczyk hierarchies" (1983).

{-# OPTIONS --no-positivity-check --rewriting #-}
-- we don't prove termination

------------------------------------------------------------------------------
-- Setup

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

+-0 : {m : Nat} → m + 0 ≡ m
+-0 {0}                     = refl
+-0 {suc m} rewrite +-0 {m} = refl

+-suc  : {m n : Nat} → m + suc n ≡ suc (m + n)
+-suc {0}     {n}                       = refl
+-suc {suc m} {n} rewrite +-suc {m} {n} = refl

{-# REWRITE +-suc +-0 #-}

data ⊥ : Set where

id : {a : Set} → a → a
id x = x

{-# NON_TERMINATING #-}
undefined : {a : Set} → a
undefined = undefined

------------------------------------------------------------------------------
-- Iteration on `Nat`


iterNatD : {f : Nat → Nat → Set}
    → (r : Nat)
    → ({s t : Nat} → {{r ≡ suc (s + t)}} → f (suc s) t → f s (suc t))
    → f r 0 → f 0 r
iterNatD {f} r g = go r 0
  where
    go : (s t : Nat) → {{s + t ≡ r}} → f s t → f 0 r
    go 0       _ {{refl}} x = x
    go (suc s) t {{refl}} x = go s (suc t) (g x)

iterNat : {a : Set} → (r : Nat) → (a → a) → a → a
iterNat {a} r f = iterNatD {\_ _ → a} r f

------------------------------------------------------------------------------
-- Tree ordinals, TT r <--> Omega_r

-- These types are designed with two goals in mind:
--
--   1. stacks of successors are encoded as a plain `nat`,
--      to facilitate conversion between `TT 0` and `nat`
--
--   2. members of `TT r` are represented the same way in `TT (r+1)`
--
-- As cases, a tree ordinal is either n successors of zero, `T Z n`,
-- or n successors of the limit of an Ω_k-indexed fundamental sequence,
-- `T (B^k (L z)) n`, where z : Ω_k -> Ω_r (and r > k)
--
-- In particular, n = T Z n, and ω_r = T (B^r (L liftTT)) 0,
-- where liftTT : TT r -> TT (r+1) is the identity function after
-- types have been erased.

data TL' (l r : Set) : Set where
    B : l → TL' l r
    L : r → TL' l r

interleaved mutual
    data TT (r : Nat) : Set
    data TZ (r : Nat) : Set
    TL : Nat → Nat → Set

    data _ where
        T  : TZ r → Nat → TT r

    data _ where
        Z  : TZ r
        NZ : TL r 0 → TZ r

    TL 0       _ = ⊥ -- this ensures r > k in the limit ordinal case
    TL (suc s) t = TL' (TL s (suc t)) (TT t → TT (suc (s + t)))

------------------------------------------------------------------------------
-- Increment tree ordinal

sucTT : {r : Nat} → TT r → TT r
sucTT (T z n) = T z (suc n)

------------------------------------------------------------------------------
-- Lifting... preserves the structure exactly.

interleaved mutual
    liftTT : {r : Nat} → TT r → TT (suc r)
    liftTL : {s r : Nat} → TL s r → TL (suc s) r

    liftTT (T Z      n) = T Z n
    liftTT (T (NZ l) n) = T (NZ (liftTL l)) n

    liftTL {suc _} (B x) = B (liftTL x)
    liftTL {suc _} (L z) = L (\i → liftTT (z i))

w : (r : Nat) → TT (suc r)
w r = T (NZ (iterNatD {\s t → TL (suc t) s} r B (L liftTT))) 0

-----------------------------------------------------------------------------
-- Iteration

-- {-# NON_TERMINATING #-}
iterTT : {r : Nat} → (TT r → TT r) → TT r → TT r → TT r
iterTT {r} f (T nz n) m = iterNat n f (iterNZ nz m)
  where
    iterTL : {s t : Nat} → {{r ≡ s + t}}
        → TL s t → TT r → TL s t
    iterTL {suc _} {{refl}} (B x) m = B (iterTL x m)
    iterTL {suc _} {{refl}} (L z) m = L (\i → iterTT f (z i) m)

    iterNZ : TZ r → TT r → TT r
    iterNZ Z      m = m
    iterNZ (NZ l) m = T (NZ (iterTL l m)) 0

------------------------------------------------------------------------------
-- phi (generalized fast-growing function)

-- {-# NON_TERMINATING #-}
phi : (r : Nat) → TT (suc r) → TT r → TT r
phi r (T nz n) = iterNat n (\f m → iterTT f m m) (phiNZ nz)
  where
    phiTL : {s t : Nat} → {{r ≡ s + t}}
        → (TL s t → TT r) → TL (suc s) t → TT r → TT r
    phiTL {0}     {{refl}} bs (L z) m = phi r (z m) m
    phiTL {suc _} {{refl}} bs (B x) m = phiTL (\x → bs (B x)) x m
    phiTL {suc _} {{refl}} bs (L z) m = bs (L (\i → phi r (z i) m))

    phiNZ : TZ (suc r) → TT r → TT r
    phiNZ Z      = sucTT
    phiNZ (NZ l) = phiTL (\l → T (NZ l) 0) l

------------------------------------------------------------------------------
-- tau tower

three : {r : Nat} → TT r
three = T Z 3

-- f[r] = phi[0] (... (phi[r] 3 w[r-1]) ... w[0])
f_tau : (r : Nat) → Nat → Nat
f_tau r n = nat (iterNatD {\s t → ty s} (suc r) step (\_ → three) (T Z n))
  where
    ty : (s : Nat) → Set
    ty s = TT s → TT s

    -- note: f = phi (suc s) (... (phi r three) ... (w (suc s)))
    step : {s : Nat} → ty (suc s) → ty s
    step {s} f = phi s (f (w s))

    nat : TT 0 → Nat
    nat (T Z m) = m

-- variation:
-- f[0]   = id
-- f[r+1] = phi[0] (... (phi[r] w[r] w[r-1]) ... w[0])
f_tau' : (r : Nat) → Nat → Nat
f_tau' r n = nat (iterNatD {\s t → ty s} r step id (T Z n))
  where
    ty : (s : Nat) → Set
    ty s = TT s → TT s

    step : {s : Nat} → ty (suc s) → ty s
    step {s} f = phi s (f (w s))

    nat : TT 0 → Nat
    nat (T Z m) = m
