module Main where

import System.Environment(getArgs)
import LHToCoq(run)

main :: IO ()
main = getArgs >>= run