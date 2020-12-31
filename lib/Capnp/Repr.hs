{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
module Capnp.Repr
    ( Repr(..)
    , PtrRepr(..)
    , ListRepr(..)
    , NormalListRepr(..)
    , DataSz(..)
    , ElemRepr
    , ListReprFor
    , ReprFor

    , Raw(..)

    , List
    , length
    , index
    ) where

import Prelude hiding (length)

import Control.Monad.Catch (MonadThrow (..))
import Data.Int
import Data.Kind           (Type)
import Data.Proxy          (Proxy (..))
import Data.Word

import qualified Capnp.Classes as C
import qualified Capnp.Errors  as E
import           Capnp.Message (Mutability (..))
import qualified Capnp.Message as M
import qualified Capnp.Untyped as U

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

type family ReprFor (a :: Type) :: Repr

type instance ReprFor () = 'Data 'Sz0
type instance ReprFor Bool = 'Data 'Sz1
type instance ReprFor Word8 = 'Data 'Sz8
type instance ReprFor Word16 = 'Data 'Sz16
type instance ReprFor Word32 = 'Data 'Sz32
type instance ReprFor Word64 = 'Data 'Sz64
type instance ReprFor Int8 = 'Data 'Sz8
type instance ReprFor Int16 = 'Data 'Sz16
type instance ReprFor Int32 = 'Data 'Sz32
type instance ReprFor Int64 = 'Data 'Sz64
type instance ReprFor Float = 'Data 'Sz32
type instance ReprFor Double = 'Data 'Sz64

-- | @Untyped mut r@ is an untyped value with representation @r@ stored in
-- a message with mutability @mut@.
type family Untyped (mut :: Mutability) (r :: Repr) :: Type where
    Untyped mut ('Data sz) = UntypedData sz
    Untyped mut ('Ptr ptr) = UntypedPtr mut ptr

type family UntypedData (sz :: DataSz) :: Type where
    UntypedData 'Sz0 = ()
    UntypedData 'Sz1 = Bool
    UntypedData 'Sz8 = Word8
    UntypedData 'Sz16 = Word16
    UntypedData 'Sz32 = Word32
    UntypedData 'Sz64 = Word64

type family UntypedPtr (mut :: Mutability) (r :: Maybe PtrRepr) :: Type where
    UntypedPtr mut 'Nothing = Maybe (U.Ptr mut)
    UntypedPtr mut ('Just r) = UntypedSomePtr mut r

type family UntypedSomePtr (mut :: Mutability) (r :: PtrRepr) :: Type where
    UntypedSomePtr mut 'Struct = U.Struct mut
    UntypedSomePtr mut 'Cap = U.Cap mut
    UntypedSomePtr mut ('List r) = UntypedList mut r

type family UntypedList (mut :: Mutability) (r :: Maybe ListRepr) :: Type where
    UntypedList mut 'Nothing = U.List mut
    UntypedList mut ('Just r) = UntypedSomeList mut r

type family UntypedSomeList (mut :: Mutability) (r :: ListRepr) :: Type where
    UntypedSomeList mut ('ListNormal r) = UntypedNormalList mut r
    UntypedSomeList mut 'ListComposite = U.ListOf mut (U.Struct mut)

type family UntypedNormalList (mut :: Mutability) (r :: NormalListRepr) :: Type where
    UntypedNormalList mut 'ListPtr = U.ListOf mut (U.Ptr mut)
    UntypedNormalList mut ('ListData sz) = U.ListOf mut (UntypedData sz)

newtype Raw (mut :: Mutability) (a :: Type)
    = Raw (Untyped mut (ReprFor a))

data List a

type instance ReprFor (List a) = 'Ptr ('Just ('List ('Just (ListReprFor (ReprFor a)))))

length :: (Untyped mut (ReprFor (List a)) ~ U.ListOf mut b) => Raw mut (List a) -> Int
length (Raw l) = U.length l

index ::
    ( U.ReadCtx m mut
    , Untyped mut (ReprFor (List a)) ~ U.ListOf mut (Untyped mut (ReprFor a))
    ) => Int -> Raw mut (List a) -> m (Raw mut a)
index i (Raw l) = Raw <$> U.index i l

instance (ReprFor a ~ 'Ptr ('Just 'Struct)) => C.ToStruct mut (Raw mut a) where
    toStruct (Raw s) = s
instance (ReprFor a ~ 'Ptr ('Just 'Struct)) => C.FromStruct mut (Raw mut a) where
    fromStruct = pure . Raw

instance U.HasMessage (Untyped mut (ReprFor a)) mut => U.HasMessage (Raw mut a) mut where
    message (Raw r) = U.message r
instance U.MessageDefault (Untyped mut (ReprFor a)) mut => U.MessageDefault (Raw mut a) mut where
    messageDefault msg = Raw <$> U.messageDefault msg

class IsPtrRepr (r :: Maybe PtrRepr) where
    rToPtr :: Proxy r -> M.Message mut -> (Untyped mut ('Ptr r)) -> Maybe (U.Ptr mut)
    rFromPtr :: U.ReadCtx m mut => Proxy r -> M.Message mut -> Maybe (U.Ptr mut) -> m (Untyped mut ('Ptr r))

instance IsPtrRepr 'Nothing where
    rToPtr _ _ p = p
    rFromPtr _ _ p = pure p

instance IsPtrRepr ('Just 'Struct) where
    rToPtr _ _ s = Just (U.PtrStruct s)
    rFromPtr _ msg Nothing              = U.messageDefault msg
    rFromPtr _ _ (Just (U.PtrStruct s)) = pure s
    rFromPtr _ _ _                      = expected "pointer to struct"

instance (IsPtrRepr r, ReprFor a ~ 'Ptr r) => C.ToPtr s (Raw ('Mut s) a) where
    toPtr msg (Raw p) = pure $ rToPtr (Proxy @r) msg p
instance (IsPtrRepr r, ReprFor a ~ 'Ptr r) => C.FromPtr mut (Raw mut a) where
    fromPtr msg p = Raw <$> rFromPtr (Proxy @r) msg p

-- helper function for throwing SchemaViolationError "expected ..."
expected :: MonadThrow m => String -> m a
expected msg = throwM $ E.SchemaViolationError $ "expected " ++ msg
