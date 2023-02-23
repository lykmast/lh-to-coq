
{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Ack0 where

{-@ reflect ack @-}
{-@ ack :: m:Nat -> n:Nat -> Nat / [m,n] @-}
ack :: Int -> Int -> Int
ack 0 n = n + 1
ack m 0 = ack (m-1) 1
ack m n = ack (m-1) (ack m (n-1))

{-@ ack_gt_snd :: m:Nat -> n:Nat -> {ack m n > n} / [m,n] @-}
ack_gt_snd :: Int -> Int -> Proof
ack_gt_snd 0 n = ()
ack_gt_snd m 0 = ack_gt_snd (m - 1) 1
  -- ack m 0 === ack (m-1) 1 ? ack_gt_snd (m - 1) 1 =>> 1 =>> 0 *** QED 
ack_gt_snd m n = ack_gt_snd (m - 1) (ack m (n-1)) ? ack_gt_snd m (n-1)
{-
      ack m n
  === ack (m-1) (ack m (n-1))
    ? ack_gt_snd (m - 1) (ack m (n-1))
  =>> ack m (n-1)
    ? ack_gt_snd m (n-1)
  =>= n
  *** QED
-}
