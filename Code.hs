{-# Language GeneralizedNewtypeDeriving #-}
{-# Language DerivingStrategies #-}
{-# Language ViewPatterns #-}
{-# Language TupleSections #-}
{-# Language DeriveTraversable #-}
module Code where

import Control.Applicative
import Data.Bifunctor
import Data.Bits
import Data.Bits.Pext
import Data.Bits.Pdep
import Data.Maybe
import Data.Traversable
import Data.Word

newtype N = N Word64
  deriving stock Eq
  deriving newtype (Show, Num, Pext, Pdep, Bits, FiniteBits)

instance Semigroup N where (<>) = (.|.)
instance Monoid N where mempty = 0

-- 0b1011 << 0b101 = 0b1001
-- compose thinnings
(<<) :: N -> N -> N
(<<) = pdep

-- remove an outer thinning
(>>) :: N -> N -> N
(>>) = pext

act :: Int -> N -> N
act = flip shift

data Bd = Bd Int N
  deriving stock (Show,Eq)

instance Semigroup Bd where
  Bd i n <> Bd j m = Bd (i+j) (act j n <> m)

instance Monoid Bd where
  mempty = Bd 0 mempty

data Open a = Open {-# unpack #-} !N a
  deriving stock (Eq, Show, Functor, Foldable, Traversable)

instance Applicative Open where
  pure = Open 0
  Open n f <*> Open m a = Open (n <> m) (f a)

instance Monad Open where
  Open n a >>= k = case k a of
    Open m b -> Open (n <> m) b

fvs :: Open a -> N
fvs (Open n _) = n

data Expr
  = Var
  | App {-# unpack #-} !(Open Expr) [Open Expr]
  | Lam {-# unpack #-} !Bd Expr
  deriving stock Show

var :: Open Expr
var = Open 1 Var

v :: Int -> Open Expr
v i = Open (bit i) Var

lam :: Int -> Open Expr -> Open Expr
lam i (Open n e) = Open n' $ mkLam (Bd i m) e where
  (n',m) = (unsafeShiftR n i, n .&. (bit i - 1))
  mkLam b (Lam d a) = Lam (b <> d) a
  mkLam bd a = Lam bd a

launder :: N -> N -> Open a -> Open a
launder o i (Open j a) = Open (pext o $ pdep i j) a

unapp :: Open Expr -> (N, Open Expr, [Open Expr])
unapp (Open o (App f xs)) = (o, scatter o f, scatter o <$> xs)
unapp (Open o a)        = (o, Open (balance o) a, [])

app :: Open Expr -> [Open Expr] -> Open Expr
app (unapp -> (o, f, ys)) xs = Open op $
  App (launder op o f) $ launder op o <$> ys <|> gather op <$> xs
  where op = o <> foldMap fvs xs

-- pdep a (balance a) = a
balance :: N -> N
balance n = bit (popCount n) - 1

scatter :: N -> Open a -> Open a
scatter n (Open m a) = Open (pdep n m) a

gather :: N -> Open a -> Open a
gather n (Open m a) = Open (pext n m) a

thin :: Int -> Open a -> Open a
thin i (Open n a) = Open (act i n) a

s,k,i :: Expr
s = Lam (Bd 3 7) $ App (v 2) [v 0,Open 3 $ App (v 1) [v 0]]
k = closed $ lam 2 $ v 1
i = closed $ lam 1 $ v 0

k' :: Expr
k' = closed $ lam 1 $ lam 1 $ v 1

closed :: Show a => Open a -> a
closed (Open 0 xs) = xs
closed (Open i xs) = error $
  "Not a closed term : (" ++ show i ++ ") " ++ show xs

-- foo f x y = f x y
test :: Expr
test = closed $ lam 3 $ app (thin 2 var) [thin 1 var, var]

test' :: Expr
test' = closed $ lam 3 $ app (app (thin 2 var) [thin 1 var]) [var]

test'' :: Expr
test'' = closed $ lam 3 $ app1 (app1 (thin 2 var) (thin 1 var)) var

app1 :: Open Expr -> Open Expr -> Open Expr
app1 f x = Open o $ App (gather o f) [gather o x] where
  o = fvs f <> fvs x

--oldapps :: Open Expr -> [Open Expr] -> Open Expr
--oldapps f xs = (o, App (gather o f) $ gather o <$> xs) where
--  o = fst f <> foldMap fst xs
