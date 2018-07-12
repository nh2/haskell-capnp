{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
module Codec.Capnp.Generic
    ( IsWord(..)
    , ListElem(..)
    , MutListElem(..)
    , IsPtr(..)
    , IsStruct(..)
    , Decerialize(..)
    , getWordField
    , expected
    ) where

import Data.Bits
import Data.Int
import Data.ReinterpretCast
import Data.Word

import Control.Monad.Catch        (MonadThrow(throwM))
import Data.Capnp.Errors          (Error(SchemaViolationError))
import Data.Capnp.Untyped.Generic
    (ListOf, Ptr(..), ReadCtx, Struct, getData, messageDefault)

import qualified Data.Capnp.Message         as M
import qualified Data.Capnp.Message.Mutable as MM
import qualified Data.Capnp.Untyped.Generic as U

-- | Types that can be converted to and from a 64-bit word.
--
-- This is mostly a helper for generated code, which uses it to interact
-- with the data sections of structs.
class IsWord a where
    fromWord :: Word64 -> a
    toWord :: a -> Word64

class ListElem msg e where
    data List msg e
    length :: List msg e -> Int
    index :: U.ReadCtx m msg => Int -> List msg e -> m e

class MutListElem s e where
    setIndex :: (U.ReadCtx m (MM.Message s), MM.WriteCtx m s) => e -> Int -> List (MM.Message s) e -> m ()

class Decerialize from to where
    decerialize :: U.ReadCtx m M.Message => from -> m to


-- | Types that can be extracted from an untyped pointer.
--
-- Similarly to 'IsWord', this is mostly used in generated code, to interact
-- with the pointer section of structs.
class IsPtr msg a where
    fromPtr :: ReadCtx m msg => msg -> Maybe (Ptr msg) -> m a

-- | Types that can be extracted from a struct.
class IsStruct msg a where
    fromStruct :: ReadCtx m msg => Struct msg -> m a

expected :: MonadThrow m => String -> m a
expected msg = throwM $ SchemaViolationError $ "expected " ++ msg

-- | @'getWordField' struct index offset def@ fetches a field from the
-- struct's data section. @index@ is the index of the 64-bit word in the data
-- section in which the field resides. @offset@ is the offset in bits from the
-- start of that word to the field. @def@ is the default value for this field.
getWordField :: (ReadCtx m msg, IsWord a) => Struct msg -> Int -> Int -> Word64 -> m a
getWordField struct idx offset def = fmap
    ( fromWord
    . xor def
    . (`shiftR` offset)
    )
    (getData idx struct)

instance Decerialize () () where
    decerialize = pure
instance Decerialize Bool Bool where
    decerialize = pure
instance Decerialize Word8 Word8 where
    decerialize = pure
instance Decerialize Word16 Word16 where
    decerialize = pure
instance Decerialize Word32 Word32 where
    decerialize = pure
instance Decerialize Word64 Word64 where
    decerialize = pure
instance Decerialize Int8 Int8 where
    decerialize = pure
instance Decerialize Int16 Int16 where
    decerialize = pure
instance Decerialize Int32 Int32 where
    decerialize = pure
instance Decerialize Int64 Int64 where
    decerialize = pure
instance Decerialize Float Float where
    decerialize = pure
instance Decerialize Double Double where
    decerialize = pure

instance IsWord Bool where
    fromWord n = (n .&. 1) == 1
    toWord True  = 1
    toWord False = 0

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

-- IsPtr instance for lists of Void/().
instance IsPtr msg (ListOf msg ()) where
    fromPtr msg Nothing                       = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.List0 list))) = pure list
    fromPtr _ _ = expected "pointer to list with element size 0"

-- IsPtr instances for lists of unsigned integers.
instance IsPtr msg (ListOf msg Word8) where
    fromPtr msg Nothing                       = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.List8 list))) = pure list
    fromPtr _ _ = expected "pointer to list with element size 8"
instance IsPtr msg (ListOf msg Word16) where
    fromPtr msg Nothing                       = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.List16 list))) = pure list
    fromPtr _ _ = expected "pointer to list with element size 16"
instance IsPtr msg (ListOf msg Word32) where
    fromPtr msg Nothing                       = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.List32 list))) = pure list
    fromPtr _ _ = expected "pointer to list with element size 32"
instance IsPtr msg (ListOf msg Word64) where
    fromPtr msg Nothing                       = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.List64 list))) = pure list
    fromPtr _ _ = expected "pointer to list with element size 64"

-- | IsPtr instance for pointers -- this is just the identity.
instance IsPtr msg (Maybe (Ptr msg)) where
    fromPtr _ = pure

-- IsPtr instance for composite lists.
instance IsPtr msg (ListOf msg (Struct msg)) where
    fromPtr msg Nothing                            = pure $ messageDefault msg
    fromPtr msg (Just (PtrList (U.ListStruct list))) = pure list
    fromPtr _ _ = expected "pointer to list of structs"

-- IsStruct instance for Struct; just the identity.
instance IsStruct msg (Struct msg) where
    fromStruct = pure

instance IsPtr msg (Struct msg) where
    fromPtr msg Nothing              = fromStruct (go msg) where
        -- the type checker needs a bit of help inferring the type here.
        go :: msg -> Struct msg
        go = messageDefault
    fromPtr msg (Just (PtrStruct s)) = fromStruct s
    fromPtr _ _                      = expected "pointer to struct"