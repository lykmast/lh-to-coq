module Util(showStripped) where



-- Get rid of module names.
showStripped :: Show a => a -> String
showStripped = last . split '.' . show


split :: Char -> String -> [String]
split c s = case rest of
                []     -> [chunk]
                _:rest -> chunk : split c rest
  where (chunk, rest) = break (==c) s