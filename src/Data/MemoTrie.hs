{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wall -fenable-rewrite-rules #-}

-- ScopedTypeVariables works around a 6.10 bug.  The forall keyword is
-- supposed to be recognized in a RULES pragma.

----------------------------------------------------------------------

----------------------------------------------------------------------

-- |
-- Module      :  Data.MemoTrie
-- Copyright   :  (c) Conal Elliott 2008-2016
-- License     :  BSD3
--
-- Maintainer  :  conal@conal.net
-- Stability   :  experimental
--
-- Trie-based memoizer
--
-- Adapted from sjanssen's paste: <http://hpaste.org/3839 \"a lazy trie\">,
-- which I think is based on Ralf Hinze's paper "Memo Functions,
-- Polytypically!".
--
-- You can automatically derive generic instances. for example:
--
-- @
-- {-# LANGUAGE <https://ocharles.org.uk/blog/posts/2014-12-16-derive-generic.html DeriveGeneric>, DerivingVia, TypeOperators, TypeFamilies, UndecidableInstances #-}
-- import Data.MemoTrie
-- import GHC.Generics (Generic)
--
-- data Color = RGB Int Int Int
--            | NamedColor String
--  deriving stock ('Generic')
--  deriving (HasTrie) via GenericMemoTrie Color
-- @
--
-- see @examples/Generic.hs@, which can be run with:
--
-- @
-- cabal configure -fexamples && cabal run generic
-- @
module Data.MemoTrie
  ( HasTrie (..),
    GenericMemoTrie (..),
    domain,
    trie2,
    trie3,
    untrie2,
    untrie3,
    memo,
    memo2,
    memo3,
    mup,
    inTrie,
    inTrie2,
    inTrie3,
    Reg,
    memoFix,
  )
where

-- Export the parts of HasTrie separately in order to get the associated data
-- type constructors, so I can define instances of other classes on them.

import Control.Arrow (first, (&&&))
import Data.Bits
import Data.Function (fix)
import Data.Int
import Data.Void (Void, absurd)
import Data.Word
import GHC.Generics

infixr 0 /->/

-- | Mapping from all elements of @a@ to the results of some function
class HasTrie a where
  -- | Representation of trie with domain type @a@
  type (/->/) a b :: *

  -- | Create the trie for the entire domain of a function
  trie :: (a -> b) -> (a /->/ b)

  -- | Convert a trie to a function, i.e., access a field of the trie
  untrie :: (a /->/ b) -> (a -> b)

  -- | List the trie elements.  Order of keys (@:: a@) is always the same.
  enumerate :: (a /->/ b) -> [(a, b)]

-- | Domain elements of a trie
domain :: forall a. HasTrie a => [a]
domain = map fst (enumerate (trie (const oops :: a -> ())) :: [(a, ())])
  where
    oops = error "Data.MemoTrie.domain: range element evaluated."

-- Hm: domain :: [Bool] doesn't produce any output.

trie2 ::
  (HasTrie a, HasTrie b) =>
  (a -> b -> c) ->
  (a /->/ b /->/ c)
-- trie2 h = trie $ \ a -> trie $ \ b -> h a b
-- trie2 h = trie $ \ a -> trie (h a)
trie2 h = trie (trie . h)

-- trie2 h = trie (fmap trie h)
-- trie2 = (fmap.fmap) trie trie

trie3 ::
  (HasTrie a, HasTrie b, HasTrie c) =>
  (a -> b -> c -> d) ->
  (a /->/ b /->/ c /->/ d)
trie3 h = trie (trie2 . h)

untrie2 ::
  (HasTrie a, HasTrie b) =>
  (a /->/ b /->/ c) ->
  (a -> b -> c)
untrie2 tt = untrie . untrie tt

untrie3 ::
  (HasTrie a, HasTrie b, HasTrie c) =>
  (a /->/ b /->/ c /->/ d) ->
  (a -> b -> c -> d)
untrie3 tt = untrie2 . untrie tt

-- | Trie-based function memoizer
memo :: HasTrie t => (t -> a) -> (t -> a)
memo = untrie . trie

-- | Memoize a binary function, on its first argument and then on its
-- second.  Take care to exploit any partial evaluation.
memo2 :: (HasTrie s, HasTrie t) => (s -> t -> a) -> (s -> t -> a)

-- | Memoize a ternary function on successive arguments.  Take care to
-- exploit any partial evaluation.
memo3 :: (HasTrie r, HasTrie s, HasTrie t) => (r -> s -> t -> a) -> (r -> s -> t -> a)

-- | Lift a memoizer to work with one more argument.
mup :: HasTrie t => (b -> c) -> (t -> b) -> (t -> c)
mup mem f = memo (mem . f)

memo2 = mup memo

memo3 = mup memo2

-- | Memoizing recursion. Use like `fix`.
memoFix :: HasTrie a => ((a -> b) -> (a -> b)) -> (a -> b)
memoFix h = fix (memo . h)

-- | Apply a unary function inside of a trie
inTrie ::
  (HasTrie a, HasTrie c) =>
  ((a -> b) -> (c -> d)) ->
  ((a /->/ b) -> (c /->/ d))
inTrie = untrie ~> trie

-- | Apply a binary function inside of a trie
inTrie2 ::
  (HasTrie a, HasTrie c, HasTrie e) =>
  ((a -> b) -> (c -> d) -> (e -> f)) ->
  ((a /->/ b) -> (c /->/ d) -> (e /->/ f))
inTrie2 = untrie ~> inTrie

-- | Apply a ternary function inside of a trie
inTrie3 ::
  (HasTrie a, HasTrie c, HasTrie e, HasTrie g) =>
  ((a -> b) -> (c -> d) -> (e -> f) -> (g -> h)) ->
  ((a /->/ b) -> (c /->/ d) -> (e /->/ f) -> (g /->/ h))
inTrie3 = untrie ~> inTrie2

---- Instances

instance HasTrie Void where
  -- As suggested by Audun Skaugen
  type Void /->/ a = ()
  trie _ = ()
  untrie () = absurd
  enumerate () = []

instance HasTrie () where
  type () /->/ a = a
  trie f = f ()
  untrie a = \() -> a
  enumerate a = [((), a)]

-- Proofs of inverse properties:

{-
    untrie (trie f)
      == { trie def }
    untrie (UnitTrie (f ()))
      == { untrie def }
    \ () -> (f ())
      == { const-unit }
    f

    trie (untrie (UnitTrie a))
      == { untrie def }
    trie (\ () -> a)
      == { trie def }
    UnitTrie ((\ () -> a) ())
      == { beta-reduction }
    UnitTrie a

Oops -- the last step of the first direction is bogus when f is non-strict.
Can be fixed by using @const a@ in place of @\ () -> a@, but I can't do
the same for other types, like integers or sums.

All of these proofs have this same bug, unless we restrict ourselves to
memoizing hyper-strict functions.

-}

instance HasTrie Bool where
  type Bool /->/ x = (x, x)
  trie f = (f False, f True)
  untrie (f, t) = if' f t
  enumerate (f, t) = [(False, f), (True, t)]

-- | Conditional with boolean last.
-- Spec: @if' (f False) (f True) == f@
if' :: x -> x -> Bool -> x
if' t _ False = t
if' _ e True = e

{-
    untrie (trie f)
      == { trie def }
    untrie (BoolTrie (f False) (f True))
      == { untrie def }
    if' (f False) (f True)
      == { if' spec }
    f

    trie (untrie (BoolTrie f t))
      == { untrie def }
    trie (if' f t)
      == { trie def }
    BoolTrie (if' f t False) (if' f t True)
      == { if' spec }
    BoolTrie f t
-}

instance HasTrie a => HasTrie (Maybe a) where
  type (/->/) (Maybe a) b = (b, a /->/ b)
  trie f = (f Nothing, trie (f . Just))
  untrie (nothing_val, a_trie) = maybe nothing_val (untrie a_trie)
  enumerate (nothing_val, a_trie) = (Nothing, nothing_val) : enum' Just a_trie

instance (HasTrie a, HasTrie b) => HasTrie (Either a b) where
  type (Either a b) /->/ x = (a /->/ x, b /->/ x)
  trie f = (trie (f . Left), trie (f . Right))
  untrie (s, t) = either (untrie s) (untrie t)
  enumerate (s, t) = enum' Left s `weave` enum' Right t

enum' :: (HasTrie a) => (a -> a') -> (a /->/ b) -> [(a', b)]
enum' f = (fmap . first) f . enumerate

weave :: [a] -> [a] -> [a]
[] `weave` as = as
as `weave` [] = as
(a : as) `weave` bs = a : (bs `weave` as)

{-
    untrie (trie f)
       == { trie def }
    untrie (EitherTrie (trie (f . Left)) (trie (f . Right)))
       == { untrie def }
    either (untrie (trie (f . Left))) (untrie (trie (f . Right)))
       == { untrie . trie }
    either (f . Left) (f . Right)
       == { either }
    f

    trie (untrie (EitherTrie s t))
       == { untrie def }
    trie (either (untrie s) (untrie t))
       == { trie def }
    EitherTrie (trie (either (untrie s) (untrie t) . Left))
               (trie (either (untrie s) (untrie t) . Right))
       == { either }
    EitherTrie (trie (untrie s)) (trie (untrie t))
       == { trie . untrie }
    EitherTrie s t
-}

instance (HasTrie a, HasTrie b) => HasTrie (a, b) where
  type (a, b) /->/ x = a /->/ (b /->/ x)
  trie f = trie (trie . curry f)
  untrie t = uncurry (untrie . untrie t)
  enumerate tt =
    [((a, b), x) | (a, t) <- enumerate tt, (b, x) <- enumerate t]

{-
    untrie (trie f)
      == { trie def }
    untrie (PairTrie (trie (trie . curry f)))
      == { untrie def }
    uncurry (untrie . untrie (trie (trie . curry f)))
      == { untrie . trie }
    uncurry (untrie . trie . curry f)
      == { untrie . untrie }
    uncurry (curry f)
      == { uncurry . curry }
    f

    trie (untrie (PairTrie t))
      == { untrie def }
    trie (uncurry (untrie .  untrie t))
      == { trie def }
    PairTrie (trie (trie . curry (uncurry (untrie .  untrie t))))
      == { curry . uncurry }
    PairTrie (trie (trie . untrie .  untrie t))
      == { trie . untrie }
    PairTrie (trie (untrie t))
      == { trie . untrie }
    PairTrie t
-}

instance (HasTrie a, HasTrie b, HasTrie c) => HasTrie (a, b, c) where
  type (a, b, c) /->/ x = ((a, b), c) /->/ x
  trie f = trie (f . trip)
  untrie t = untrie t . detrip
  enumerate t = enum' trip t

trip :: ((a, b), c) -> (a, b, c)
trip ((a, b), c) = (a, b, c)

detrip :: (a, b, c) -> ((a, b), c)
detrip (a, b, c) = ((a, b), c)

newtype ListTrie x a = ListTrie (Either () (x, [x]) /->/ a)

instance HasTrie x => HasTrie [x] where
  type [x] /->/ a = ListTrie x a
  trie f = ListTrie (trie (f . list))
  untrie (ListTrie t) = untrie t . delist
  enumerate (ListTrie t) = enum' list t

list :: Either () (x, [x]) -> [x]
list = either (const []) (uncurry (:))

delist :: [x] -> Either () (x, [x])
delist [] = Left ()
delist (x : xs) = Right (x, xs)

instance HasTrie Word where type Word /->/ a = ([Bool] /->/ a); trie f = trie (f . unbits); untrie t = untrie t . bits; enumerate t = enum' unbits t

instance HasTrie Word8 where type Word8 /->/ a = [Bool] /->/ a; trie f = trie (f . unbits); untrie t = untrie t . bits; enumerate t = enum' unbits t

instance HasTrie Word16 where type Word16 /->/ a = [Bool] /->/ a; trie f = trie (f . unbits); untrie t = untrie t . bits; enumerate t = enum' unbits t

instance HasTrie Word32 where type Word32 /->/ a = [Bool] /->/ a; trie f = trie (f . unbits); untrie t = untrie t . bits; enumerate t = enum' unbits t

instance HasTrie Word64 where type Word64 /->/ a = [Bool] /->/ a; trie f = trie (f . unbits); untrie t = untrie t . bits; enumerate t = enum' unbits t

-- instance HasTrie Word where
--   type Word /->/ a = [Bool] /->/ a
--   trie f = trie (f . unbits)
--   untrie t = untrie t . bits
--   enumerate t = enum' unbits t

-- | Extract bits in little-endian order
bits :: (Num t, Bits t) => t -> [Bool]
bits 0 = []
bits x = testBit x 0 : bits (shiftR x 1)

-- | Convert boolean to 0 (False) or 1 (True)
unbit :: Num t => Bool -> t
unbit False = 0
unbit True = 1

-- | Bit list to value
unbits :: (Num t, Bits t) => [Bool] -> t
unbits [] = 0
unbits (x : xs) = unbit x .|. shiftL (unbits xs) 1

instance HasTrie Char where
  type Char /->/ a = Int /->/ a
  untrie t n = untrie t (fromEnum n)
  trie f = trie (f . toEnum)
  enumerate t = enum' toEnum t

-- Although Int is a Bits instance, we can't use bits directly for
-- memoizing, because the "bits" function gives an infinite result, since
-- shiftR (-1) 1 == -1.  Instead, convert between Int and Word, and use
-- a Word trie.  Any Integral type can be handled similarly.

instance HasTrie Int where type Int /->/ a = Word /->/ a; untrie t n = untrie t (fromIntegral n :: Word); trie f = trie (f . fromIntegral @Word); enumerate t = enum' (fromIntegral @Word) t

instance HasTrie Int8 where type Int8 /->/ a = Word8 /->/ a; untrie t n = untrie t (fromIntegral n :: Word8); trie f = trie (f . fromIntegral @Word8); enumerate t = enum' (fromIntegral @Word8) t

instance HasTrie Int16 where type Int16 /->/ a = Word16 /->/ a; untrie t n = untrie t (fromIntegral n :: Word16); trie f = trie (f . fromIntegral @Word16); enumerate t = enum' (fromIntegral @Word16) t

instance HasTrie Int32 where type Int32 /->/ a = Word32 /->/ a; untrie t n = untrie t (fromIntegral n :: Word32); trie f = trie (f . fromIntegral @Word32); enumerate t = enum' (fromIntegral @Word32) t

instance HasTrie Int64 where type Int64 /->/ a = Word64 /->/ a; untrie t n = untrie t (fromIntegral n :: Word64); trie f = trie (f . fromIntegral @Word64); enumerate t = enum' (fromIntegral @Word64) t

-- For unbounded integers, we don't have a corresponding Word type, so
-- extract the sign bit.

instance HasTrie Integer where
  type Integer /->/ a = (Bool, [Bool]) /->/ a
  trie f = trie (f . unbitsZ)
  untrie t = untrie t . bitsZ
  enumerate t = enum' unbitsZ t

unbitsZ :: (Num n, Bits n) => (Bool, [Bool]) -> n
unbitsZ (positive, bs) = sig (unbits bs)
  where
    sig
      | positive = id
      | otherwise = negate

bitsZ :: (Num n, Ord n, Bits n) => n -> (Bool, [Bool])
bitsZ = (>= 0) &&& (bits . abs)

-- TODO: make these definitions more systematic.

---- To go elsewhere

-- Matt Hellige's notation for @argument f . result g@.
-- <http://matt.immute.net/content/pointless-fun>

(~>) :: (a' -> a) -> (b -> b') -> ((a -> b) -> (a' -> b'))
g ~> f = (f .) . (. g)

{-
-- Examples
f1,f1' :: Int -> Int
f1 n = n + n

f1' = memo f1
-}

-- | just like @void@
instance HasTrie (V1 x) where
  type V1 x /->/ b = ()
  trie _ = ()
  untrie () = \case
  enumerate () = []

-- | just like @()@
instance HasTrie (U1 x) where
  type U1 x /->/ b = b
  trie f = f U1
  untrie b = \U1 -> b
  enumerate b = [(U1, b)]

-- | wraps @Either (f x) (g x)@
instance (HasTrie (f x), HasTrie (g x)) => HasTrie ((f :+: g) x) where
  type (f :+: g) x /->/ b = Either (f x) (g x) /->/ b
  trie f = trie (f . liftSum)
  untrie t = untrie t . dropSum
  enumerate t = enum' liftSum t

-- | wraps @(f x, g x)@
instance (HasTrie (f x), HasTrie (g x)) => HasTrie ((f :*: g) x) where
  type (f :*: g) x /->/ b = (f x, g x) /->/ b
  trie f = trie (f . liftProduct)
  untrie t = untrie t . dropProduct
  enumerate t = enum' liftProduct t

-- | wraps @a@
instance (HasTrie a) => HasTrie (K1 i a x) where
  type K1 i a x /->/ b = a /->/ b
  trie f = trie (f . K1)
  untrie t = \(K1 a) -> untrie t a
  enumerate t = enum' K1 t

-- | wraps @f x@
instance (HasTrie (f x)) => HasTrie (M1 i t f x) where
  type M1 i t f x /->/ b = f x /->/ b
  trie f = trie (f . M1)
  untrie t = \(M1 a) -> untrie t a
  enumerate t = enum' M1 t

-- | the data type in a __reg__ular form.
-- "unlifted" generic representation. (i.e. is a unary type constructor).
type Reg a = Rep a ()

newtype GenericMemoTrie a = GenericMemoTrie {getGenericMemoTrie :: a}
  deriving newtype (Generic)

instance (Generic a, HasTrie (Reg a)) => HasTrie (GenericMemoTrie a) where
  type GenericMemoTrie a /->/ b = Reg a /->/ b
  trie f = trie (f . GenericMemoTrie . (to :: Reg a -> a))
  untrie t = untrie t . (from :: a -> Reg a) . getGenericMemoTrie
  enumerate t = enum' (GenericMemoTrie . (to :: Reg a -> a)) t

dropProduct :: (f :*: g) a -> (f a, g a)
dropProduct (a :*: b) = (a, b)
{-# INLINEABLE dropProduct #-}

liftProduct :: (f a, g a) -> (f :*: g) a
liftProduct (a, b) = a :*: b
{-# INLINEABLE liftProduct #-}

dropSum :: (f :+: g) a -> Either (f a) (g a)
dropSum s = case s of
  L1 x -> Left x
  R1 x -> Right x
{-# INLINEABLE dropSum #-}

liftSum :: Either (f a) (g a) -> (f :+: g) a
liftSum = either L1 R1
{-# INLINEABLE liftSum #-}
