{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
module Capnp.Capnp.RpcTwoparty where

-- Code generated by capnpc-haskell. DO NOT EDIT.
-- Generated from schema file: capnp/rpc-twoparty.capnp

import Data.Int
import Data.Word

import Data.Capnp.Bits (Word1)

import qualified Data.Bits
import qualified Data.Maybe
import qualified Codec.Capnp as C'
import qualified Data.Capnp.Basics as B'
import qualified Data.Capnp.TraversalLimit as TL'
import qualified Data.Capnp.Untyped as U'
import qualified Data.Capnp.Message as M'

import qualified Capnp.ById.Xbdf87d7bb8304e81

newtype JoinKeyPart msg = JoinKeyPart (U'.Struct msg)

instance C'.IsStruct msg (JoinKeyPart msg) where
    fromStruct = pure . JoinKeyPart
instance C'.IsPtr msg (JoinKeyPart msg) where
    fromPtr msg ptr = JoinKeyPart <$> C'.fromPtr msg ptr
instance B'.ListElem msg (JoinKeyPart msg) where
    newtype List msg (JoinKeyPart msg) = List_JoinKeyPart (U'.ListOf msg (U'.Struct msg))
    length (List_JoinKeyPart l) = U'.length l
    index i (List_JoinKeyPart l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (JoinKeyPart msg); go = C'.fromStruct} in go)
instance B'.MutListElem s (JoinKeyPart (M'.MutMessage s)) where
    setIndex (JoinKeyPart elt) i (List_JoinKeyPart l) = U'.setIndex elt i l

instance C'.IsPtr msg (B'.List msg (JoinKeyPart msg)) where
    fromPtr msg ptr = List_JoinKeyPart <$> C'.fromPtr msg ptr
get_JoinKeyPart'joinId :: U'.ReadCtx m msg => JoinKeyPart msg -> m Word32
get_JoinKeyPart'joinId (JoinKeyPart struct) = C'.getWordField struct 0 0 0

has_JoinKeyPart'joinId :: U'.ReadCtx m msg => JoinKeyPart msg -> m Bool
has_JoinKeyPart'joinId(JoinKeyPart struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_JoinKeyPart'joinId :: (U'.ReadCtx m (M'.MutMessage s), M'.WriteCtx m s) => JoinKeyPart (M'.MutMessage s) -> Word32 -> m ()
set_JoinKeyPart'joinId (JoinKeyPart struct) value =  C'.setWordField struct (fromIntegral (C'.toWord value) :: Word32) 0 0 0

get_JoinKeyPart'partCount :: U'.ReadCtx m msg => JoinKeyPart msg -> m Word16
get_JoinKeyPart'partCount (JoinKeyPart struct) = C'.getWordField struct 0 32 0

has_JoinKeyPart'partCount :: U'.ReadCtx m msg => JoinKeyPart msg -> m Bool
has_JoinKeyPart'partCount(JoinKeyPart struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_JoinKeyPart'partCount :: (U'.ReadCtx m (M'.MutMessage s), M'.WriteCtx m s) => JoinKeyPart (M'.MutMessage s) -> Word16 -> m ()
set_JoinKeyPart'partCount (JoinKeyPart struct) value =  C'.setWordField struct (fromIntegral (C'.toWord value) :: Word16) 0 32 0

get_JoinKeyPart'partNum :: U'.ReadCtx m msg => JoinKeyPart msg -> m Word16
get_JoinKeyPart'partNum (JoinKeyPart struct) = C'.getWordField struct 0 48 0

has_JoinKeyPart'partNum :: U'.ReadCtx m msg => JoinKeyPart msg -> m Bool
has_JoinKeyPart'partNum(JoinKeyPart struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_JoinKeyPart'partNum :: (U'.ReadCtx m (M'.MutMessage s), M'.WriteCtx m s) => JoinKeyPart (M'.MutMessage s) -> Word16 -> m ()
set_JoinKeyPart'partNum (JoinKeyPart struct) value =  C'.setWordField struct (fromIntegral (C'.toWord value) :: Word16) 0 48 0

newtype JoinResult msg = JoinResult (U'.Struct msg)

instance C'.IsStruct msg (JoinResult msg) where
    fromStruct = pure . JoinResult
instance C'.IsPtr msg (JoinResult msg) where
    fromPtr msg ptr = JoinResult <$> C'.fromPtr msg ptr
instance B'.ListElem msg (JoinResult msg) where
    newtype List msg (JoinResult msg) = List_JoinResult (U'.ListOf msg (U'.Struct msg))
    length (List_JoinResult l) = U'.length l
    index i (List_JoinResult l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (JoinResult msg); go = C'.fromStruct} in go)
instance B'.MutListElem s (JoinResult (M'.MutMessage s)) where
    setIndex (JoinResult elt) i (List_JoinResult l) = U'.setIndex elt i l

instance C'.IsPtr msg (B'.List msg (JoinResult msg)) where
    fromPtr msg ptr = List_JoinResult <$> C'.fromPtr msg ptr
get_JoinResult'joinId :: U'.ReadCtx m msg => JoinResult msg -> m Word32
get_JoinResult'joinId (JoinResult struct) = C'.getWordField struct 0 0 0

has_JoinResult'joinId :: U'.ReadCtx m msg => JoinResult msg -> m Bool
has_JoinResult'joinId(JoinResult struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_JoinResult'joinId :: (U'.ReadCtx m (M'.MutMessage s), M'.WriteCtx m s) => JoinResult (M'.MutMessage s) -> Word32 -> m ()
set_JoinResult'joinId (JoinResult struct) value =  C'.setWordField struct (fromIntegral (C'.toWord value) :: Word32) 0 0 0

get_JoinResult'succeeded :: U'.ReadCtx m msg => JoinResult msg -> m Bool
get_JoinResult'succeeded (JoinResult struct) = C'.getWordField struct 0 32 0

has_JoinResult'succeeded :: U'.ReadCtx m msg => JoinResult msg -> m Bool
has_JoinResult'succeeded(JoinResult struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_JoinResult'succeeded :: (U'.ReadCtx m (M'.MutMessage s), M'.WriteCtx m s) => JoinResult (M'.MutMessage s) -> Bool -> m ()
set_JoinResult'succeeded (JoinResult struct) value =  C'.setWordField struct (fromIntegral (C'.toWord value) :: Word1) 0 32 0

get_JoinResult'cap :: U'.ReadCtx m msg => JoinResult msg -> m (Maybe (U'.Ptr msg))
get_JoinResult'cap (JoinResult struct) =
    U'.getPtr 0 struct
    >>= C'.fromPtr (U'.message struct)


has_JoinResult'cap :: U'.ReadCtx m msg => JoinResult msg -> m Bool
has_JoinResult'cap(JoinResult struct) = Data.Maybe.isJust <$> U'.getPtr 0 struct
set_JoinResult'cap :: (U'.ReadCtx m (M'.MutMessage s), M'.WriteCtx m s) => JoinResult (M'.MutMessage s) -> (Maybe (U'.Ptr (M'.MutMessage s))) -> m ()
set_JoinResult'cap _ = error "TODO: generate more setters."

data Side
    = Side'server
    | Side'client
    | Side'unknown' Word16
instance Enum Side where
    toEnum = C'.fromWord . fromIntegral
    fromEnum = fromIntegral . C'.toWord


instance C'.IsWord Side where
    fromWord n = go (fromIntegral n :: Word16)
      where
        go 1 = Side'client
        go 0 = Side'server
        go tag = Side'unknown' (fromIntegral tag)
    toWord Side'client = 1
    toWord Side'server = 0
    toWord (Side'unknown' tag) = fromIntegral tag
instance B'.ListElem msg Side where
    newtype List msg Side = List_Side (U'.ListOf msg Word16)
    length (List_Side l) = U'.length l
    index i (List_Side l) = (C'.fromWord . fromIntegral) <$> U'.index i l
instance B'.MutListElem s Side where
    setIndex elt i (List_Side l) = error "TODO: generate code for setIndex"
instance C'.IsPtr msg (B'.List msg Side) where
    fromPtr msg ptr = List_Side <$> C'.fromPtr msg ptr

newtype ProvisionId msg = ProvisionId (U'.Struct msg)

instance C'.IsStruct msg (ProvisionId msg) where
    fromStruct = pure . ProvisionId
instance C'.IsPtr msg (ProvisionId msg) where
    fromPtr msg ptr = ProvisionId <$> C'.fromPtr msg ptr
instance B'.ListElem msg (ProvisionId msg) where
    newtype List msg (ProvisionId msg) = List_ProvisionId (U'.ListOf msg (U'.Struct msg))
    length (List_ProvisionId l) = U'.length l
    index i (List_ProvisionId l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (ProvisionId msg); go = C'.fromStruct} in go)
instance B'.MutListElem s (ProvisionId (M'.MutMessage s)) where
    setIndex (ProvisionId elt) i (List_ProvisionId l) = U'.setIndex elt i l

instance C'.IsPtr msg (B'.List msg (ProvisionId msg)) where
    fromPtr msg ptr = List_ProvisionId <$> C'.fromPtr msg ptr
get_ProvisionId'joinId :: U'.ReadCtx m msg => ProvisionId msg -> m Word32
get_ProvisionId'joinId (ProvisionId struct) = C'.getWordField struct 0 0 0

has_ProvisionId'joinId :: U'.ReadCtx m msg => ProvisionId msg -> m Bool
has_ProvisionId'joinId(ProvisionId struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_ProvisionId'joinId :: (U'.ReadCtx m (M'.MutMessage s), M'.WriteCtx m s) => ProvisionId (M'.MutMessage s) -> Word32 -> m ()
set_ProvisionId'joinId (ProvisionId struct) value =  C'.setWordField struct (fromIntegral (C'.toWord value) :: Word32) 0 0 0

newtype VatId msg = VatId (U'.Struct msg)

instance C'.IsStruct msg (VatId msg) where
    fromStruct = pure . VatId
instance C'.IsPtr msg (VatId msg) where
    fromPtr msg ptr = VatId <$> C'.fromPtr msg ptr
instance B'.ListElem msg (VatId msg) where
    newtype List msg (VatId msg) = List_VatId (U'.ListOf msg (U'.Struct msg))
    length (List_VatId l) = U'.length l
    index i (List_VatId l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (VatId msg); go = C'.fromStruct} in go)
instance B'.MutListElem s (VatId (M'.MutMessage s)) where
    setIndex (VatId elt) i (List_VatId l) = U'.setIndex elt i l

instance C'.IsPtr msg (B'.List msg (VatId msg)) where
    fromPtr msg ptr = List_VatId <$> C'.fromPtr msg ptr
get_VatId'side :: U'.ReadCtx m msg => VatId msg -> m Side
get_VatId'side (VatId struct) = C'.getWordField struct 0 0 0

has_VatId'side :: U'.ReadCtx m msg => VatId msg -> m Bool
has_VatId'side(VatId struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_VatId'side :: (U'.ReadCtx m (M'.MutMessage s), M'.WriteCtx m s) => VatId (M'.MutMessage s) -> Side -> m ()
set_VatId'side (VatId struct) value =  C'.setWordField struct (fromIntegral (C'.toWord value) :: Word16) 0 0 0
