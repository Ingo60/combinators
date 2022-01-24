module src.Combinators where

import Data.MicroParsec as MP
import Data.Iterators as IT

mkstr = StringIterator.from 

data Comb = S | K | I | Var Char | App Comb Comb
instance Show Comb  where
    show S = "S"
    show K = "K"
    show I = "I"
    show (Var x) = ctos x
    show (App a b) = "(" ++ show a ++ show b ++ ")"

p_comb = (expect 'S' >> pure S) <|>  (expect 'K' >> pure K) <|> (expect 'I' >> pure I)
p_var  = Var <$> satisfy (\c → c >= '0' && c <= '9' || c >= 'a' && c <= 'z')
p_sub  = label "expression expected" (expect '(') >> (p_expr <* expect ')')

-- p_expr :: Parser StringIterator Char Comb
p_expr =  (foldl1  App) <$> some (p_comb <|> p_var <|> p_sub)
