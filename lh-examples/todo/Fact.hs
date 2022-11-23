{-@ LIQUID "--reflection" @-}
-- {-@ LIQUID "--short-names" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PackageImports #-}

module Fact where
{- HLINT ignore -}
import "liquid-base" Prelude

data PNat = Z | S PNat

{-@ reflect add @-}
add Z n = n
add (S m) n = S (add m n)

{-@ reflect mul @-}
mul Z _ = Z
mul (S m) n = add n (mul m n)

{-@ reflect factP @-}
factP Z = S Z
factP (S n) = mul (S n) (factP n)

---------------------- Arithmetic Proofs ----------------------

-- | Addition left identity.
{-@ add_lid :: n:PNat -> {add n Z = n} @-}
add_lid Z     = () -- add Z Z === Z *** QED
add_lid (S n) = add_lid n -- add (S n) Z === S (add n Z) ? add_lid n === S n *** QED

-- | Addition with right successor.
{-@ add_suc_r :: m:PNat -> n:PNat -> {S (add m n) = add m (S n)} @-}
add_suc_r :: PNat -> PNat -> ()
add_suc_r Z n = ()-- S (add Z n) === S n ? add_lid (S n) === add Z (S n) *** QED
add_suc_r (S m) n = add_suc_r m n
  -- =   S (add (S m) n)
  -- === S (S (add m n))
  --   ? add_suc_r m n
  -- === S (add m (S n))
  -- === add (S m) (S n)
  -- *** QED

-- * Commutativity of addition.
{-@ add_comm :: m:PNat -> n:PNat -> {add m n = add n m} @-}
add_comm Z n     = add_lid n -- add Z n === n ? add_lid n === add n Z *** QED
add_comm (S m) n = add_comm m n ? add_suc_r n m
  -- =   add (S m) n
  -- === S (add m n)
  -- ? add_comm m n
  -- === S (add n m)
  -- ? add_suc_r n m
  -- === add n (S m)
  -- *** QED

-- * Associativity of addition.
{-@ add_assoc :: n:PNat -> m:PNat -> p:PNat -> {add n (add m p) = add (add n m) p} @-}
add_assoc :: PNat -> PNat -> PNat -> Proof
add_assoc Z m p = ()
add_assoc (S n) m p =  add_assoc n m p

-- | Multiply with zero right.
{-@ mul_Z_r :: n:PNat -> {mul n Z = Z} @-}
mul_Z_r Z = ()
mul_Z_r (S n) = mul_Z_r n

-- | Multiply with right successor.
{-@ mul_suc_r :: m:PNat -> n:PNat -> {mul n (S m) = add n (mul n m)} @-}
mul_suc_r :: PNat -> PNat -> Proof
mul_suc_r m Z     = ()
mul_suc_r m (S n) = mul_suc_r m n
                  ? add_assoc m n (mul n m)
                  ? add_comm m n
                  ? add_assoc n m (mul n m)

-- * Commutativity of multiplication.
{-@ mul_comm :: n:PNat -> m:PNat -> {mul n m = mul m n} @-}
mul_comm :: PNat -> PNat -> Proof
mul_comm Z m = mul_Z_r m
mul_comm (S n) m = mul_comm n m ? mul_suc_r m n

---------------------- <= Proofs ----------------------
{-
{-@
data Le where
  Le_n :: n:PNat -> Prop (Le n n)
  Le_S :: n:PNat -> m:PNat -> Prop (Le n m) -> Prop (Le n (S m))
@-}


-- | 0 <= n.
{-@ le_Z :: n:PNat -> Prop (Le Z n) @-}
le_Z Z = Le_n Z
le_Z (S n) = Le_S Z n (le_Z n)

-- | n<=0 -> n=0.
{-@ le_Z_then_Z :: n:PNat -> Prop (Le n Z) -> {n = Z}  @-}
le_Z_then_Z :: PNat -> Le -> Proof
le_Z_then_Z _n (Le_n n) = ()
le_Z_then_Z _n (Le_S n _z p) = ()

-- | m<=n -> m+1 <= n+1
{-@ le_SS :: m:PNat -> n:PNat -> Prop (Le m n) -> Prop (Le (S m) (S n)) @-}
le_SS m Z le_m_n = Le_n (S Z) ? le_Z_then_Z m le_m_n
le_SS m (S n) le_m_sn@(Le_S _ _ le_m_n) = Le_S (S m) (S n) (le_SS m n le_m_n)
le_SS _ _ (Le_n n) = Le_n (S n)

-- | n <= n+m.
{-@ le_add_l :: n:PNat -> m:PNat -> Prop (Le n (add n m)) @-}
le_add_l Z m = le_Z (add Z m)
le_add_l (S n) m = le_SS n (add n m) (le_add_l n m)

-- * Transitivity of <=.
{-@ le_trans :: n:PNat -> m:PNat -> p:PNat
            -> Prop (Le n m) -> Prop (Le m p) -> Prop (Le n p) @-}
le_trans :: PNat -> PNat -> PNat -> Le -> Le -> Le
le_trans _ _ _ le_n_m (Le_n m) = le_n_m
le_trans n m (S p) le_n_m (Le_S _ _ le_m_p) = Le_S n p (le_trans n m p le_n_m le_m_p)

-- * 1 <= n -> m <= m*n
{-@ le_one_mul :: n:PNat -> m:PNat -> Prop (Le (S Z) n) -> Prop (Le m (mul m n)) @-}
le_one_mul Z _ le_one_Z = absurd (le_Z_then_Z (S Z) le_one_Z)
le_one_mul (S n) m _ = le_add_l m (mul n m) ? mul_comm m (S n)

-- | 1 <= n + 1
{-@ le_one_succ :: n:PNat -> Prop (Le (S Z) (S n)) @-}
le_one_succ n = le_SS Z n (le_Z n)

-- * 1 <= factp n
{-@ le_one_factp :: n:PNat -> Prop (Le (S Z) (factP n)) @-}
le_one_factp Z = Le_n (S Z)
le_one_factp (S n) =
  le_trans (S Z) (S n) (mul (S n) (factP n))
    (le_one_succ n) (le_one_mul (factP n) (S n) (le_one_factp n))

-- *** n <= factp n
{-@ le_n_factpn :: n:PNat -> Prop (Le n (factP n)) @-}
le_n_factpn :: PNat -> Le
le_n_factpn Z = le_Z (factP Z)
le_n_factpn (S n) = le_one_mul (factP n) (S n) (le_one_factp n)

-}
---------------------- Boolean <= ----------------------

{-@ reflect leb @-}
leb Z _ = True
leb _ Z = False
leb (S n) (S m) = leb n m

{-@ leb_refl :: n:PNat -> {leb n n} @-}
leb_refl Z = ()
leb_refl (S n) = leb_refl n

{-@ leb_add_l :: n:PNat -> m:PNat ->{leb n (add n m)} @-}
leb_add_l :: PNat -> PNat -> Proof
leb_add_l Z m = ()
leb_add_l (S n) m = leb_add_l n m

{-@ leb_one_mul :: {n:PNat| leb (S Z) n} -> m:PNat -> {leb m (mul m n)} @-}
leb_one_mul :: PNat -> PNat -> Proof
leb_one_mul (S n) m = leb_add_l m (mul n m) ? mul_comm m (S n)

{-@ leb_trans :: n:PNat -> {m:_| leb n m} -> {p:_|leb m p} -> {leb n p} @-}
leb_trans :: PNat -> PNat -> PNat -> Proof
leb_trans Z m p = ()
leb_trans (S n) (S m) (S p) = leb_trans n m p

{-@ leb_one_factp :: n:PNat -> {leb (S Z) (factP n)} @-}
leb_one_factp Z = ()
leb_one_factp (S n)
  =  leb_trans (S Z) (S n) (mul (S n) (factP n) ? leb_one_mul (factP n ? leb_one_factp n) (S n))

{-@ leb_n_factpn :: n:PNat -> {leb n (factP n)} @-}
leb_n_factpn :: PNat -> Proof
leb_n_factpn Z = ()
leb_n_factpn (S n) = leb_one_mul (factP n ? leb_one_factp n) (S n)

{-
infixl 3 =<=
{-@ (=<=) :: x:PNat -> {y:PNat| leb x y} -> {v:_| v == y && leb y v && leb x v} @-}
(=<=) :: PNat -> PNat -> PNat
x =<= y = y ? leb_refl y


data Proposition = Le PNat PNat
data Le where
  Le_n :: PNat -> Le
  Le_S :: PNat -> PNat -> Le -> Le


{-@ reflect bottom @-}
{-@ lazy bottom @-}
bottom :: a
bottom = bottom


{-@ reflect absurd @-}
{-@ absurd :: {v:_| false} -> a @-}
absurd v = bottom

{-@ measure prop :: a -> b           @-}
{-@ type Prop E = {v:_ | prop v = E} @-}
-}


type Proof = ()
x ? _ = x
