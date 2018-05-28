{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE KindSignatures #-}
module Data.Capnp.ById.Xa184c7885cdaf2a1 where

-- Code generated by capnpc-haskell. DO NOT EDIT.
-- Generated from schema file: /usr/include/capnp/rpc-twoparty.capnp

import Data.Int
import Data.Word
import qualified Data.Bits

import qualified Codec.Capnp
import qualified Data.Capnp.BuiltinTypes
import qualified Data.Capnp.TraversalLimit
import qualified Data.Capnp.Untyped

import qualified Data.Capnp.ById.Xbdf87d7bb8304e81

newtype JoinKeyPart (m :: * -> *) b = JoinKeyPart (Data.Capnp.Untyped.Struct m b)

get_JoinKeyPart'joinId :: Data.Capnp.Untyped.ReadCtx m b => JoinKeyPart m b -> m Word32
get_JoinKeyPart'joinId (JoinKeyPart struct) = Codec.Capnp.getWordField struct 0 0 0
get_JoinKeyPart'partCount :: Data.Capnp.Untyped.ReadCtx m b => JoinKeyPart m b -> m Word16
get_JoinKeyPart'partCount (JoinKeyPart struct) = Codec.Capnp.getWordField struct 0 32 0
get_JoinKeyPart'partNum :: Data.Capnp.Untyped.ReadCtx m b => JoinKeyPart m b -> m Word16
get_JoinKeyPart'partNum (JoinKeyPart struct) = Codec.Capnp.getWordField struct 0 48 0
instance Data.Capnp.Untyped.ReadCtx m b => Codec.Capnp.IsPtr m (JoinKeyPart m b) b where
    fromPtr msg ptr = fmap JoinKeyPart (Codec.Capnp.fromPtr msg ptr)

newtype JoinResult (m :: * -> *) b = JoinResult (Data.Capnp.Untyped.Struct m b)

get_JoinResult'joinId :: Data.Capnp.Untyped.ReadCtx m b => JoinResult m b -> m Word32
get_JoinResult'joinId (JoinResult struct) = Codec.Capnp.getWordField struct 0 0 0
get_JoinResult'succeeded :: Data.Capnp.Untyped.ReadCtx m b => JoinResult m b -> m Bool
get_JoinResult'succeeded (JoinResult struct) = Codec.Capnp.getWordField struct 0 32 0
get_JoinResult'cap :: Data.Capnp.Untyped.ReadCtx m b => JoinResult m b -> m (Maybe (Data.Capnp.Untyped.Ptr m b))
get_JoinResult'cap (JoinResult struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

instance Data.Capnp.Untyped.ReadCtx m b => Codec.Capnp.IsPtr m (JoinResult m b) b where
    fromPtr msg ptr = fmap JoinResult (Codec.Capnp.fromPtr msg ptr)

data Side (m :: * -> *) b
    = Side'server
    | Side'client
    | Side'unknown' Word16
instance Enum (Side m b) where
    toEnum = Codec.Capnp.fromWord . fromIntegral
    fromEnum = fromIntegral . Codec.Capnp.toWord


instance Codec.Capnp.IsWord (Side m b) where
    fromWord 1 = Side'client
    fromWord 0 = Side'server
    fromWord tag = Side'unknown' (fromIntegral tag)
    toWord Side'client = 1
    toWord Side'server = 0
    toWord (Side'unknown' tag) = fromIntegral tag
instance Data.Capnp.Untyped.ReadCtx m b => Codec.Capnp.IsPtr m (Data.Capnp.Untyped.ListOf m b (Side m b)) b where
    fromPtr msg ptr = fmap
       (fmap (toEnum . (fromIntegral :: Word16 -> Int)))
       (Codec.Capnp.fromPtr msg ptr)

newtype ProvisionId (m :: * -> *) b = ProvisionId (Data.Capnp.Untyped.Struct m b)

get_ProvisionId'joinId :: Data.Capnp.Untyped.ReadCtx m b => ProvisionId m b -> m Word32
get_ProvisionId'joinId (ProvisionId struct) = Codec.Capnp.getWordField struct 0 0 0
instance Data.Capnp.Untyped.ReadCtx m b => Codec.Capnp.IsPtr m (ProvisionId m b) b where
    fromPtr msg ptr = fmap ProvisionId (Codec.Capnp.fromPtr msg ptr)

newtype VatId (m :: * -> *) b = VatId (Data.Capnp.Untyped.Struct m b)

get_VatId'side :: Data.Capnp.Untyped.ReadCtx m b => VatId m b -> m (Side m b)
get_VatId'side (VatId struct) = Codec.Capnp.getWordField struct 0 0 0
instance Data.Capnp.Untyped.ReadCtx m b => Codec.Capnp.IsPtr m (VatId m b) b where
    fromPtr msg ptr = fmap VatId (Codec.Capnp.fromPtr msg ptr)
