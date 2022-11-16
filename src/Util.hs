module Util
  ( module Data.Maybe
  , module Util
  , module Control.Applicative
  , module Data.List
  , module Data.Functor
  ) where
import Data.List(intercalate, partition)

import Data.Maybe
import Control.Applicative((<|>))
import Data.Functor((<&>))

type Id = String

addParens :: String -> String
addParens = (++ ")") . ("(" ++)

-- Get rid of module names.
showStripped :: Show a => a -> String
showStripped = strip . show

strip :: String -> String
strip = last . split '.'

split :: Char -> String -> [String]
split c s = case rest of
                []     -> [chunk]
                _:rest -> chunk : split c rest
  where (chunk, rest) = break (==c) s

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead (x:_) = Just x

setAt :: [a] -> Int -> a -> [a]
setAt xs i x = take i xs ++ [x] ++ drop (i + 1) xs

modifyAt :: [a] -> Int -> (a -> a) -> [a]
modifyAt xs i f = take i xs ++ [f $ xs !! i] ++ drop (i + 1) xs

deleteAt :: [a] -> Int -> [a]
deleteAt xs n = take n xs ++ drop (n+1) xs