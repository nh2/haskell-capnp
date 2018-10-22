{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{- |
Module: Capnp.Classes
Description: Misc. type classes

This module defines several type classes concerning encoding and decoding
values in the capnproto wire format (as well as instances for some basic
types).

Note that much of this is unlikely to be used directly by developers.
Typically these are either used internally by generated code, or
transitively via higher level functions in the API. It is recommended
to look elsewhere in the library for what you need, and refer to this
module only when trying to understand what the class constraints on a
function mean.
-}
module Capnp.Classes
    ( IsWord(..)
    , ListElem(..)
    , MutListElem(..)
    , IsPtr(..)
    , FromStruct(..)
    , ToStruct(..)
    , Allocate(..)
    , Marshal(..)
    , Cerialize(..)
    , Decerialize(..)
    ) where

import Data.Bits
import Data.Int
import Data.ReinterpretCast
import Data.Word

import Control.Monad.Catch (MonadThrow(throwM))

import Capnp.Bits    (Word1(..))
import Capnp.Errors  (Error(SchemaViolationError))
import Capnp.Untyped (Cap, ListOf, Ptr(..), ReadCtx, Struct, messageDefault)

import qualified Capnp.Message as M
import qualified Capnp.Untyped as U

-- | Types that can be converted to and from a 64-bit word.
--
-- Anything that goes in the data section of a struct will have
-- an instance of this.
class IsWord a where
    -- | Convert from a 64-bit words Truncates the word if the
    -- type has less than 64 bits.
    fromWord :: Word64 -> a

    -- | Convert to a 64-bit word.
    toWord :: a -> Word64

-- | Types which may be stored as an element of a capnproto list.
class ListElem msg e where
    -- | The type of lists of @e@ stored in messages of type @msg@
    data List msg e

    -- | Get the length of a list.
    length :: List msg e -> Int

    -- | @'index' i list@ gets the @i@th element of a list.
    index :: U.ReadCtx m msg => Int -> List msg e -> m e

-- | Types which may be stored as an element of a *mutable* capnproto list.
class (ListElem (M.MutMsg s) e) => MutListElem s e where
    -- | @'setIndex' value i list@ sets the @i@th index in @list@ to @value
    setIndex :: U.RWCtx m s => e -> Int -> List (M.MutMsg s) e -> m ()

    -- | @'newList' msg size@ allocates and returns a new list of length
    -- @size@ inside @msg@.
    newList :: M.WriteCtx m s => M.MutMsg s -> Int -> m (List (M.MutMsg s) e)

-- | Types which may be stored in a capnproto message, and have a fixed size.
--
-- This applies to typed structs, but not e.g. lists, because the length
-- must be known to allocate a list.
class Allocate s e where
    -- @'new' msg@ allocates a new value of type @e@ inside @msg@.
    new :: M.WriteCtx m s => M.MutMsg s -> m e

-- | Types which may be extracted from a message.
--
-- typically, instances of 'Decerialize' will be the algebraic data types
-- defined in generated code for the high-level API.
class Decerialize a where
    -- | A variation on @a@ which is encoded in the message.
    --
    -- For the case of instances in generated high-level API code, this will
    -- be the low-level API analouge of the type.
    type Cerial msg a

    -- | Extract the value from the message.
    decerialize :: U.ReadCtx m M.ConstMsg => Cerial M.ConstMsg a -> m a

-- | Types which may be marshaled into a pre-allocated object in a message.
class Decerialize a => Marshal a where

    -- | Marshal a value into the pre-allocated object inside the message.
    --
    -- Note that caller must arrange for the object to be of the correct size.
    -- This is is not necessarily guaranteed; for example, list types must
    -- coordinate the length of the list.
    marshalInto :: U.RWCtx m s => Cerial (M.MutMsg s) a -> a -> m ()

-- | Types which may be inserted into a message.
class Decerialize a => Cerialize s a where

    -- | Cerialize a value into the supplied message, returning the result.
    cerialize :: U.RWCtx m s => M.MutMsg s -> a -> m (Cerial (M.MutMsg s) a)

    default cerialize :: (U.RWCtx m s, Marshal a, Allocate s (Cerial (M.MutMsg s) a))
        => M.MutMsg s -> a -> m (Cerial (M.MutMsg s) a)
    cerialize msg value = do
        raw <- new msg
        marshalInto raw value
        pure raw

-- | Types that can be converted to and from an untyped pointer.
--
-- Note that encoding and decoding do not have to succeed, if the
-- pointer is the wrong type.
--
-- TODO: split this into FromPtr and ToPtr, for symmetry with FromStruct
-- and ToStruct?
class IsPtr msg a where
    -- | Convert an untyped pointer to an @a@.
    fromPtr :: ReadCtx m msg => msg -> Maybe (Ptr msg) -> m a

    -- | Convert an @a@ to an untyped pointer.
    toPtr :: M.WriteCtx m s => msg -> a -> m (Maybe (Ptr msg))

-- | Types that can be extracted from a struct.
class FromStruct msg a where
    -- | Extract a value from a struct.
    fromStruct :: ReadCtx m msg => Struct msg -> m a

-- | Types that can be converted to a struct.
class ToStruct msg a where
    -- | Convert a value to a struct.
    toStruct :: a -> Struct msg

------- instances -------

instance IsWord Bool where
    fromWord n = (n .&. 1) == 1
    toWord True  = 1
    toWord False = 0

instance IsWord Word1 where
    fromWord = Word1 . fromWord
    toWord = toWord . word1ToBool

-- IsWord instances for integral types; they're all the same.
instance IsWord Int8 where
    fromWord = fromIntegral
    toWord = fromIntegral
instance IsWord Int16 where
    fromWord = fromIntegral
    toWord = fromIntegral
instance IsWord Int32 where
    fromWord = fromIntegral
    toWord = fromIntegral
instance IsWord Int64 where
    fromWord = fromIntegral
    toWord = fromIntegral
instance IsWord Word8 where
    fromWord = fromIntegral
    toWord = fromIntegral
instance IsWord Word16 where
    fromWord = fromIntegral
    toWord = fromIntegral
instance IsWord Word32 where
    fromWord = fromIntegral
    toWord = fromIntegral
instance IsWord Word64 where
    fromWord = fromIntegral
    toWord = fromIntegral

instance IsWord Float where
    fromWord = wordToFloat . fromIntegral
    toWord = fromIntegral . floatToWord
instance IsWord Double where
    fromWord = wordToDouble
    toWord = doubleToWord

-- helper function for throwing SchemaViolationError "expected ..."
expected :: MonadThrow m => String -> m a
expected msg = throwM $ SchemaViolationError $ "expected " ++ msg

-- IsPtr instance for lists of Void/().
instance IsPtr msg (ListOf msg ()) where
    fromPtr msg Nothing                         = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.List0 list))) = pure list
    fromPtr _ _ = expected "pointer to list with element size 0"
    toPtr _ = pure . Just . PtrList . U.List0

-- IsPtr instances for lists of unsigned integers.
instance IsPtr msg (ListOf msg Word8) where
    fromPtr msg Nothing                       = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.List8 list))) = pure list
    fromPtr _ _ = expected "pointer to list with element size 8"
    toPtr _ = pure . Just . PtrList . U.List8
instance IsPtr msg (ListOf msg Word16) where
    fromPtr msg Nothing                       = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.List16 list))) = pure list
    fromPtr _ _ = expected "pointer to list with element size 16"
    toPtr _ = pure . Just . PtrList . U.List16
instance IsPtr msg (ListOf msg Word32) where
    fromPtr msg Nothing                       = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.List32 list))) = pure list
    fromPtr _ _ = expected "pointer to list with element size 32"
    toPtr _ = pure . Just . PtrList . U.List32
instance IsPtr msg (ListOf msg Word64) where
    fromPtr msg Nothing                       = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.List64 list))) = pure list
    fromPtr _ _ = expected "pointer to list with element size 64"
    toPtr _ = pure . Just . PtrList . U.List64


instance IsPtr msg (ListOf msg Bool) where
    fromPtr msg Nothing = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.List1 list))) = pure list
    fromPtr _ _ = expected "pointer to list with element size 1."
    toPtr _ = pure . Just . PtrList . U.List1

-- | IsPtr instance for pointers -- this is just the identity.
instance IsPtr msg (Maybe (Ptr msg)) where
    fromPtr _ = pure
    toPtr _ = pure

-- IsPtr instance for composite lists.
instance IsPtr msg (ListOf msg (Struct msg)) where
    fromPtr msg Nothing                            = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.ListStruct list))) = pure list
    fromPtr _ _ = expected "pointer to list of structs"
    toPtr _ = pure. Just . PtrList . U.ListStruct

-- FromStruct instance for Struct; just the identity.
instance FromStruct msg (Struct msg) where
    fromStruct = pure

instance ToStruct msg (Struct msg) where
    toStruct = id

instance IsPtr msg (Struct msg) where
    fromPtr msg Nothing              = fromStruct (go msg) where
        -- the type checker needs a bit of help inferring the type here.
        go :: msg -> Struct msg
        go = messageDefault
    fromPtr msg (Just (PtrStruct s)) = fromStruct s
    fromPtr _ _                      = expected "pointer to struct"
    toPtr _ = pure . Just . PtrStruct

instance IsPtr msg (Maybe (Cap msg)) where
    fromPtr msg Nothing             = pure Nothing
    fromPtr msg (Just (PtrCap cap)) = pure (Just cap)
    fromPtr _ _                     = expected "pointer to capability"
    toPtr _ = pure . fmap PtrCap