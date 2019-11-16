{-# Language GeneralizedNewtypeDeriving #-}
{-# Language DerivingStrategies #-}
{-# Language ViewPatterns #-}
{-# Language TupleSections #-}
module Code where

import Control.Applicative
import Data.Bifunctor
import Data.Bits
import Data.Bits.Pext
import Data.Bits.Pdep
import Data.Word

newtype N = N Word64
  deriving stock (Show, Eq)
  deriving newtype (Num, Pext, Pdep, Bits, FiniteBits)

instance Semigroup N where
  N n <> N m = N (n .|. m)

-- 0b1011 << 0b101 = 0b1001
(<<) :: N -> N -> N
(<<) = pdep

(>>) :: N -> N -> N
(>>) = pext

instance Monoid N where
  mempty = 0

act :: Int -> N -> N
act = flip unsafeShiftL

data Bd = Bd Int N
  deriving stock (Show,Eq)

instance Semigroup Bd where
  Bd i n <> Bd j m = Bd (i+j) (act j n <> m)

instance Monoid Bd where
  mempty = Bd 0 mempty

type Re = (,) N

data Expr
  = Var
  | App (Re Expr) [Re Expr]
  | Lam Bd Expr
  deriving stock Show

var :: Re Expr
var = (1, Var)

app :: Re Expr -> [Re Expr] -> Re Expr
app (unapp -> (o, f, ys)) xs = 
  (op, App (launder op o f) $ launder op o <$> ys <|> gather op <$> xs
  ) where op = o <> foldMap fst xs

launder :: N -> N -> Re a -> Re a
launder o i (j, a) = (pext o $ pdep i j, a)

unapp :: Re Expr -> (N, Re Expr, [Re Expr])
unapp (o, App f xs) = (o, scatter o f, scatter o <$> xs)
unapp (o, a)        = (o, (balance o, a), [])

-- pdep a (balance a) = a
balance :: N -> N
balance n = bit (popCount n) - 1

scatter :: N -> Re a -> Re a
scatter n (m, a) = (pdep n m, a)

gather :: N -> Re a -> Re a
gather n (m, a) = (pext n m, a)

lam :: Int -> Re Expr -> Re Expr
lam i (n, e) = (n', mkLam (Bd i m) e) where
  (n',m) = splitN i n
  mkLam b (Lam d a) = Lam (b <> d) a
  mkLam bd a = Lam bd a

splitN :: Int -> N -> (N, N)
splitN i n = (unsafeShiftR n i, n .&. (bit i - 1))

thin :: Int -> Re a -> Re a
thin i (n, a) = (act i n, a)

id_ :: Re Expr
id_ = lam 1 var

const_ :: Re Expr
const_ = lam 2 $ thin 1 var

const'_ :: Re Expr
const'_ = lam 1 $ lam 1 $ thin 1 var

-- foo f x y = f(x,y)
test :: Re Expr
test = lam 3 $ app (thin 2 var) [thin 1 var, var]

test' :: Re Expr
test' = lam 3 $ app (app (thin 2 var) [thin 1 var]) [var]

test'' :: Re Expr
test'' = lam 3 $ app1 (app1 (thin 2 var) (thin 1 var)) var

app1 :: Re Expr -> Re Expr -> Re Expr
app1 (n, f) (m, x) = (o, App (pext o n, f) [(pext o m, x)]) where
  o = n <> m

--oldapps :: Re Expr -> [Re Expr] -> Re Expr
--oldapps f xs = (o, App (gather o f) $ gather o <$> xs) where
--  o = fst f <> foldMap fst xs
