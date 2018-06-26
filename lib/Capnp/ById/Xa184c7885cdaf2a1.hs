{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Capnp.ById.Xa184c7885cdaf2a1 where

-- Code generated by capnpc-haskell. DO NOT EDIT.
-- Generated from schema file: capnp/rpc-twoparty.capnp

import Data.Int
import Data.Word
import qualified Data.Bits
import qualified Data.Maybe
import qualified Codec.Capnp
import qualified Data.Capnp.BuiltinTypes
import qualified Data.Capnp.TraversalLimit
import qualified Data.Capnp.Untyped

import qualified Capnp.ById.Xbdf87d7bb8304e81

newtype JoinKeyPart msg = JoinKeyPart Data.Capnp.Untyped.Struct

instance Codec.Capnp.IsStruct (JoinKeyPart msg) where
    fromStruct = pure . JoinKeyPart
instance Codec.Capnp.IsPtr (JoinKeyPart msg) where
    fromPtr = Codec.Capnp.structPtr

instance Codec.Capnp.IsPtr (Data.Capnp.Untyped.ListOf (JoinKeyPart msg)) where
    fromPtr = Codec.Capnp.structListPtr
get_JoinKeyPart'joinId :: Data.Capnp.Untyped.ReadCtx m => JoinKeyPart msg -> m Word32
get_JoinKeyPart'joinId (JoinKeyPart struct) = Codec.Capnp.getWordField struct 0 0 0

has_JoinKeyPart'joinId :: Data.Capnp.Untyped.ReadCtx m => JoinKeyPart msg -> m Bool
has_JoinKeyPart'joinId(JoinKeyPart struct) = pure $ 0 < Data.Capnp.Untyped.length (Data.Capnp.Untyped.dataSection struct)
get_JoinKeyPart'partCount :: Data.Capnp.Untyped.ReadCtx m => JoinKeyPart msg -> m Word16
get_JoinKeyPart'partCount (JoinKeyPart struct) = Codec.Capnp.getWordField struct 0 32 0

has_JoinKeyPart'partCount :: Data.Capnp.Untyped.ReadCtx m => JoinKeyPart msg -> m Bool
has_JoinKeyPart'partCount(JoinKeyPart struct) = pure $ 0 < Data.Capnp.Untyped.length (Data.Capnp.Untyped.dataSection struct)
get_JoinKeyPart'partNum :: Data.Capnp.Untyped.ReadCtx m => JoinKeyPart msg -> m Word16
get_JoinKeyPart'partNum (JoinKeyPart struct) = Codec.Capnp.getWordField struct 0 48 0

has_JoinKeyPart'partNum :: Data.Capnp.Untyped.ReadCtx m => JoinKeyPart msg -> m Bool
has_JoinKeyPart'partNum(JoinKeyPart struct) = pure $ 0 < Data.Capnp.Untyped.length (Data.Capnp.Untyped.dataSection struct)
newtype JoinResult msg = JoinResult Data.Capnp.Untyped.Struct

instance Codec.Capnp.IsStruct (JoinResult msg) where
    fromStruct = pure . JoinResult
instance Codec.Capnp.IsPtr (JoinResult msg) where
    fromPtr = Codec.Capnp.structPtr

instance Codec.Capnp.IsPtr (Data.Capnp.Untyped.ListOf (JoinResult msg)) where
    fromPtr = Codec.Capnp.structListPtr
get_JoinResult'joinId :: Data.Capnp.Untyped.ReadCtx m => JoinResult msg -> m Word32
get_JoinResult'joinId (JoinResult struct) = Codec.Capnp.getWordField struct 0 0 0

has_JoinResult'joinId :: Data.Capnp.Untyped.ReadCtx m => JoinResult msg -> m Bool
has_JoinResult'joinId(JoinResult struct) = pure $ 0 < Data.Capnp.Untyped.length (Data.Capnp.Untyped.dataSection struct)
get_JoinResult'succeeded :: Data.Capnp.Untyped.ReadCtx m => JoinResult msg -> m Bool
get_JoinResult'succeeded (JoinResult struct) = Codec.Capnp.getWordField struct 0 32 0

has_JoinResult'succeeded :: Data.Capnp.Untyped.ReadCtx m => JoinResult msg -> m Bool
has_JoinResult'succeeded(JoinResult struct) = pure $ 0 < Data.Capnp.Untyped.length (Data.Capnp.Untyped.dataSection struct)
get_JoinResult'cap :: Data.Capnp.Untyped.ReadCtx m => JoinResult msg -> m (Maybe Data.Capnp.Untyped.Ptr)
get_JoinResult'cap (JoinResult struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)


has_JoinResult'cap :: Data.Capnp.Untyped.ReadCtx m => JoinResult msg -> m Bool
has_JoinResult'cap(JoinResult struct) = Data.Maybe.isJust <$> Data.Capnp.Untyped.getPtr 0 struct
data Side
    = Side'server
    | Side'client
    | Side'unknown' Word16
instance Enum Side where
    toEnum = Codec.Capnp.fromWord . fromIntegral
    fromEnum = fromIntegral . Codec.Capnp.toWord


instance Codec.Capnp.IsWord Side where
    fromWord n = go (fromIntegral n :: Word16)
      where
        go 1 = Side'client
        go 0 = Side'server
        go tag = Side'unknown' (fromIntegral tag)
    toWord Side'client = 1
    toWord Side'server = 0
    toWord (Side'unknown' tag) = fromIntegral tag
instance Codec.Capnp.IsPtr (Data.Capnp.Untyped.ListOf Side) where
    fromPtr msg ptr = fmap
       (fmap (toEnum . (fromIntegral :: Word16 -> Int)))
       (Codec.Capnp.fromPtr msg ptr)

newtype ProvisionId msg = ProvisionId Data.Capnp.Untyped.Struct

instance Codec.Capnp.IsStruct (ProvisionId msg) where
    fromStruct = pure . ProvisionId
instance Codec.Capnp.IsPtr (ProvisionId msg) where
    fromPtr = Codec.Capnp.structPtr

instance Codec.Capnp.IsPtr (Data.Capnp.Untyped.ListOf (ProvisionId msg)) where
    fromPtr = Codec.Capnp.structListPtr
get_ProvisionId'joinId :: Data.Capnp.Untyped.ReadCtx m => ProvisionId msg -> m Word32
get_ProvisionId'joinId (ProvisionId struct) = Codec.Capnp.getWordField struct 0 0 0

has_ProvisionId'joinId :: Data.Capnp.Untyped.ReadCtx m => ProvisionId msg -> m Bool
has_ProvisionId'joinId(ProvisionId struct) = pure $ 0 < Data.Capnp.Untyped.length (Data.Capnp.Untyped.dataSection struct)
newtype VatId msg = VatId Data.Capnp.Untyped.Struct

instance Codec.Capnp.IsStruct (VatId msg) where
    fromStruct = pure . VatId
instance Codec.Capnp.IsPtr (VatId msg) where
    fromPtr = Codec.Capnp.structPtr

instance Codec.Capnp.IsPtr (Data.Capnp.Untyped.ListOf (VatId msg)) where
    fromPtr = Codec.Capnp.structListPtr
get_VatId'side :: Data.Capnp.Untyped.ReadCtx m => VatId msg -> m Side
get_VatId'side (VatId struct) = Codec.Capnp.getWordField struct 0 0 0

has_VatId'side :: Data.Capnp.Untyped.ReadCtx m => VatId msg -> m Bool
has_VatId'side(VatId struct) = pure $ 0 < Data.Capnp.Untyped.length (Data.Capnp.Untyped.dataSection struct)