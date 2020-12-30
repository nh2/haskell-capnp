{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeFamilies           #-}
module Capnp.Repr
    ( HasRepr
    , Repr(..)
    , PtrRepr(..)
    , ListRepr(..)
    , NormalListRepr(..)
    , DataSz(..)
    , ElemRepr
    , ListReprFor
    ) where

import Data.Int
import Data.Word

-- | A 'Repr' describes a wire representation for a value. This is
-- mostly used at the type level (using DataKinds); types are
-- parametrized over representations.
data Repr
    = Ptr (Maybe PtrRepr)
    -- ^ Pointer type
    | Data DataSz
    -- ^ Non-pointer type.

data PtrRepr
    = Cap
    | List (Maybe ListRepr)
    | Struct

data ListRepr where
    ListNormal :: NormalListRepr -> ListRepr
    ListComposite :: ListRepr

data NormalListRepr where
    ListData :: DataSz -> NormalListRepr
    ListPtr :: NormalListRepr

-- | @ElemRepr r@ is the representation of elements of lists with
-- representation @r@.
type family ElemRepr (rl :: ListRepr) :: Repr where
    ElemRepr 'ListComposite = 'Ptr ('Just 'Struct)
    ElemRepr ('ListNormal 'ListPtr) = 'Ptr 'Nothing
    ElemRepr ('ListNormal ('ListData sz)) = 'Data sz

-- | @ListReprFor e@ is the representation of lists with elements
-- whose representation is @e@.
type family ListReprFor (e :: Repr) :: ListRepr where
    ListReprFor ('Data sz) = 'ListNormal ('ListData sz)
    ListReprFor ('Ptr ('Just 'Struct)) = 'ListComposite
    ListReprFor ('Ptr a) = 'ListNormal 'ListPtr

-- | The size of a non-pointer type.
data DataSz = Sz0 | Sz1 | Sz8 | Sz16 | Sz32 | Sz64

class HasRepr a (r :: Repr) | a -> r

instance HasRepr () ('Data 'Sz0)
instance HasRepr Bool ('Data 'Sz1)
instance HasRepr Word8 ('Data 'Sz8)
instance HasRepr Word16 ('Data 'Sz16)
instance HasRepr Word32 ('Data 'Sz32)
instance HasRepr Word64 ('Data 'Sz64)
instance HasRepr Int8 ('Data 'Sz8)
instance HasRepr Int16 ('Data 'Sz16)
instance HasRepr Int32 ('Data 'Sz32)
instance HasRepr Int64 ('Data 'Sz64)
instance HasRepr Float ('Data 'Sz32)
instance HasRepr Double ('Data 'Sz64)
