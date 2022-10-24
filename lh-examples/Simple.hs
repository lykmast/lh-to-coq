{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE PackageImports #-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--reflection" @-}
module Simple where
{- HLINT ignore -}
import "liquid-base" Prelude


-- import Language.Haskell.Liquid.ProofCombinators hiding ((=<=))

data PNat = Z | S PNat

{-@ reflect add @-}
add Z n = n
add (S m) n = S (add m n)
-- | Addition left identity.
{-@ add_lid :: n:PNat -> {add n Z = n} @-}
add_lid Z     = ()
add_lid (S n) = add_lid n