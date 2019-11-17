{-# Language GeneralizedNewtypeDeriving #-}
{-# Language DerivingStrategies #-}
{-# Language ViewPatterns #-}
{-# Language TupleSections #-}
{-# Language DeriveTraversable #-}
{-# Language PatternSynonyms #-}
module Code where

import Control.Applicative
import Control.Monad (guard)
import Data.Bifunctor
import Data.Bits
import Data.Bits.Pext
import Data.Bits.Pdep
import Data.Maybe
import Data.Traversable
import Data.Word
import Prelude hiding ((>>))

newtype N = N Word64
  deriving stock Eq
  deriving newtype (Show, Num, Pext, Pdep, Bits, FiniteBits)

instance Semigroup N where (<>) = (.|.)
instance Monoid N where mempty = 0

isBit :: (FiniteBits a, Num a) => a -> Maybe Int
isBit x = countTrailingZeros x <$ guard (x .&. (x - 1) == 0)

pattern Bit :: Int -> N
pattern Bit i <- (isBit -> Just i) where
  Bit i = bit i

isMask :: (FiniteBits a, Num a) => a -> Maybe Int
isMask x = isBit (x + 1)

pattern Mask :: Int -> N
pattern Mask i <- (isMask -> Just i) where
  Mask i = bit i - 1

-- @
-- pdep (pext a m) m = a .&. m
-- pext m (pdep m a) = a .&. mask (popCount m)
-- @
mask :: Int -> N
mask i = bit i - 1

-- 0b0101001001010 m
-- 0b1001001001010 a
------------------
--         0b01111 result = pext m a
-- pdep m result = a .&. m
--


-- 0b1011 << 0b101 = 0b1001
-- compose thinnings
(<<) :: N -> N -> N
(<<) = flip pdep

-- remove an outer thinning
(>>) :: N -> N -> N
(>>) = flip pext

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

pattern Closed :: a -> Open a
pattern Closed a <- Open 0 a where
  Closed a = Open 0 a

{-# Complete Closed, Open #-}

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

pattern V :: Int -> Open Expr
pattern V i = Open (Bit i) Var

pattern L :: Int -> Open Expr -> Open Expr
pattern L i b <- (unlam -> Just (i, b)) where
  L i b = lam i b

pattern A :: Open Expr -> [Open Expr] -> Open Expr
pattern A f xs <- (unapp -> (_,f,xs@(_:_))) where
  A f xs = app f xs

{-# Complete V, L, A #-}

lam :: Int -> Open Expr -> Open Expr
lam 0 e = e
lam i (Open n e) = Open n' $ mkLam (Bd i m) e where
  (n',m) = (unsafeShiftR n i, n .&. mask i)
  mkLam b (Lam d a) = Lam (b<>d) a
  mkLam bd a = Lam bd a -- couldn't resist

unlam :: Open Expr -> Maybe (Int, Open Expr)
unlam (Open o (Lam (Bd i n) b)) = Just (i, Open (unsafeShiftL o i .|. n) b)
unlam _ = Nothing

unapp :: Open Expr -> (N, Open Expr, [Open Expr])
unapp (Open o (App f xs)) = (o, scatter o f, scatter o <$> xs)
unapp (Open o a)        = (o, Open (balance o) a, [])

app :: Open Expr -> [Open Expr] -> Open Expr
app (unapp -> (o, f, ys)) xs = Open op $
  App (launder op o f) $ launder op o <$> ys <|> gather op <$> xs
  where op = o <> foldMap fvs xs

launder :: N -> N -> Open a -> Open a
launder o i (Open j a) = Open (pext (pdep j i) o) a

-- pdep a (balance a) = a
balance :: N -> N
balance n = bit (popCount n) - 1

scatter :: N -> Open a -> Open a
scatter n (Open m a) = Open (n << m) a

gather :: N -> Open a -> Open a
gather n (Open m a) = Open (n >> m) a

thin :: Int -> Open a -> Open a
thin i (Open n a) = Open (act i n) a

s,k,i :: Expr
s = closed $ L 3 $ A (V 2) [V 0,A (V 1) [V 0]]
k = closed $ L 2 $ V 1
i = closed $ L 1 $ V 0

k' :: Expr
k' = closed $ L 1 $ L 1 $ V 1

closed :: Show a => Open a -> a
closed (Open 0 xs) = xs
closed (Open i xs) = error $
  "Not a closed term : (" ++ show i ++ ") " ++ show xs

test :: Expr
test = closed $ L 3 $ A (V 2) [V 1, V 0]

