{-# LANGUAGE NoMonomorphismRestriction #-}

module MergeSort where

-- TODO also prove sortedness

import Prelude hiding (break)

-- Haskell Type Definitions
mergeSort    :: (Ord a) => [a] -> [a]

{-@ split :: xs:[a] -> { p:([a], [a]) | len (fst p) + len (snd p) = len xs && (len xs >= 2 => len (fst p) < len xs && len (snd p) < len xs)} @-}
split          :: [a] -> ([a], [a])
split (x:y:zs) = (x:xs, y:ys)
  where
    (xs, ys)   = split zs
split xs       = (xs, [])

{-@ merge :: xs:[a] -> ys:[a] -> [a] / [len xs, len ys] @-}
merge xs []         = xs
merge [] ys         = ys
merge (x:xs) (y:ys)
  | x <= y          = x : merge xs (y:ys)
  | otherwise       = y : merge (x:xs) ys

mergeSort []  = []
mergeSort [x] = [x]
mergeSort xs  = merge (mergeSort ys) (mergeSort zs)
  where
    (ys, zs)  = split xs
