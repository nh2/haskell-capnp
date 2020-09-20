{-# LANGUAGE DataKinds    #-}
{-# LANGUAGE TypeFamilies #-}
module Capnp.Mutability
    ( Mutability(..)
    , MaybeMutable(..)
    ) where

import Control.Monad.Primitive (PrimMonad(PrimState))

import Data.Kind (Type)

data Mutability = Mut Type | Const

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
