module GCD where

import Prelude hiding (gcd, mod)

{-@ gcd :: a:Nat -> b:{Nat | b < a} -> Int @-}
gcd :: Int -> Int -> Int
gcd a 0 = a
gcd a b = gcd b (a `mod` b)

{-@ mod :: a:Nat -> b:{v:Nat| 0 < v} -> {v:Nat | v < b} @-}
mod :: Int -> Int -> Int
mod a b
  | a < b = a
  | otherwise = mod (a - b) b


{-@ gcd' :: a:Nat -> b:Nat -> Int / [a,b] @-}
gcd' :: Int -> Int -> Int
gcd' a 0          = a
gcd' 0 b          = b
gcd' a b | a == b = a
         | a >  b = gcd' (a - b) b 
         | a <  b = gcd' a (b - a) 