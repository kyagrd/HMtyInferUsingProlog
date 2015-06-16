-- data Exp :: * -> * where
--   Lit :: a -> Exp a

data Tree c a =  Leaf a | Node (c (Tree c a))
