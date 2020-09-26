{-# LANGUAGE DataKinds                  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies               #-}
-- | Utility module for dealing with mutable & immutable variants of a type.
module Capnp.Mutability
    ( Mutability(..)
    , MaybeMutable(..)
    , Phantom(..)
    ) where

import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Kind (Type)

-- | An indication of mutability; this is intended to be used with the
--
-- @DataKinds@ language extension and types of kind @f :: 'Mutability' -> *@,
-- where @f 'Const@ is an immutable version of the type, and @f ('Mut s)@ is
-- a mutable version of the type which can be mutated in an instance of
-- 'PrimMonad' with state token @s@.
data Mutability = Mut Type | Const

-- | An instance of 'MaybeMutable' allows conversion between mutabale
-- and immutable forms of a type.
class MaybeMutable (f :: Mutability -> *) where
    -- | Convert an immutable value to a mutable one.
    thaw :: (PrimMonad m, PrimState m ~ s) => f 'Const -> m (f ('Mut s))

    -- | Convert a mutable value to an immutable one.
    freeze :: (PrimMonad m, PrimState m ~ s) => f ('Mut s)  -> m (f 'Const)

    -- | Like 'thaw', except that the caller is responsible for ensuring that
    -- the original value is not subsequently used; doing so may violate
    -- referential transparency.
    --
    -- The default implementation of this is just the same as 'thaw', but
    -- typically an instance will override this with a trivial (unsafe) cast,
    -- hence the obligation described above.
    unsafeThaw :: (PrimMonad m, PrimState m ~ s) => f 'Const -> m (f ('Mut s))
    unsafeThaw = thaw

    -- | Unsafe version of 'freeze' analagous to 'unsafeThaw'. The caller must
    -- ensure that the original value is not used after this call.
    unsafeFreeze :: (PrimMonad m, PrimState m ~ s) => f ('Mut s) -> m (f 'Const)
    unsafeFreeze = freeze

-- | A phantom affords using a type without separate mutable & immutable
-- variants in a place where somthing of kind @'Mutability' -> *@ is
-- expected; @'Phantom' a mut@ is a trivial wrapper around 'a'.
--
-- It has an instance of 'MaybeMutable' whose thaw & freeze operations are
-- no-ops.
newtype Phantom a (mut :: Mutability)
    = Phantom { unPhantom :: a }
    deriving(Num)

instance MaybeMutable (Phantom a) where
    thaw   (Phantom v) = pure (Phantom v)
    freeze (Phantom v) = pure (Phantom v)
