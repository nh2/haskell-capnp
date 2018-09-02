{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{- |
Module: Capnp.Capnp.RpcTwoparty
Description: Low-level generated module for capnp/rpc-twoparty.capnp
This module is the generated code for capnp/rpc-twoparty.capnp, for the
low-level api.
-}
module Capnp.Capnp.RpcTwoparty where
-- Code generated by capnpc-haskell. DO NOT EDIT.
-- Generated from schema file: capnp/rpc-twoparty.capnp
import Data.Int
import Data.Word
import GHC.Generics (Generic)
import Data.Capnp.Bits (Word1)
import qualified Data.Bits
import qualified Data.Maybe
import qualified Data.Capnp.Classes as C'
import qualified Data.Capnp.Basics as B'
import qualified Data.Capnp.GenHelpers as H'
import qualified Data.Capnp.TraversalLimit as TL'
import qualified Data.Capnp.Untyped as U'
import qualified Data.Capnp.Message as M'
import qualified Capnp.ById.Xbdf87d7bb8304e81
newtype JoinKeyPart msg = JoinKeyPart_newtype_ (U'.Struct msg)
instance C'.FromStruct msg (JoinKeyPart msg) where
    fromStruct = pure . JoinKeyPart_newtype_
instance C'.ToStruct msg (JoinKeyPart msg) where
    toStruct (JoinKeyPart_newtype_ struct) = struct
instance U'.HasMessage (JoinKeyPart msg) msg where
    message (JoinKeyPart_newtype_ struct) = U'.message struct
instance U'.MessageDefault (JoinKeyPart msg) msg where
    messageDefault = JoinKeyPart_newtype_ . U'.messageDefault
instance B'.ListElem msg (JoinKeyPart msg) where
    newtype List msg (JoinKeyPart msg) = List_JoinKeyPart (U'.ListOf msg (U'.Struct msg))
    length (List_JoinKeyPart l) = U'.length l
    index i (List_JoinKeyPart l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (JoinKeyPart msg); go = C'.fromStruct} in go)
instance C'.IsPtr msg (JoinKeyPart msg) where
    fromPtr msg ptr = JoinKeyPart_newtype_ <$> C'.fromPtr msg ptr
    toPtr (JoinKeyPart_newtype_ struct) = C'.toPtr struct
instance B'.MutListElem s (JoinKeyPart (M'.MutMsg s)) where
    setIndex (JoinKeyPart_newtype_ elt) i (List_JoinKeyPart l) = U'.setIndex elt i l
    newList msg len = List_JoinKeyPart <$> U'.allocCompositeList msg 1 0 len
instance C'.Allocate s (JoinKeyPart (M'.MutMsg s)) where
    new msg = JoinKeyPart_newtype_ <$> U'.allocStruct msg 1 0
instance C'.IsPtr msg (B'.List msg (JoinKeyPart msg)) where
    fromPtr msg ptr = List_JoinKeyPart <$> C'.fromPtr msg ptr
    toPtr (List_JoinKeyPart l) = C'.toPtr l
get_JoinKeyPart'joinId :: U'.ReadCtx m msg => JoinKeyPart msg -> m Word32
get_JoinKeyPart'joinId (JoinKeyPart_newtype_ struct) = H'.getWordField struct 0 0 0
has_JoinKeyPart'joinId :: U'.ReadCtx m msg => JoinKeyPart msg -> m Bool
has_JoinKeyPart'joinId(JoinKeyPart_newtype_ struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_JoinKeyPart'joinId :: U'.RWCtx m s => JoinKeyPart (M'.MutMsg s) -> Word32 -> m ()
set_JoinKeyPart'joinId (JoinKeyPart_newtype_ struct) value = H'.setWordField struct (fromIntegral (C'.toWord value) :: Word32) 0 0 0
get_JoinKeyPart'partCount :: U'.ReadCtx m msg => JoinKeyPart msg -> m Word16
get_JoinKeyPart'partCount (JoinKeyPart_newtype_ struct) = H'.getWordField struct 0 32 0
has_JoinKeyPart'partCount :: U'.ReadCtx m msg => JoinKeyPart msg -> m Bool
has_JoinKeyPart'partCount(JoinKeyPart_newtype_ struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_JoinKeyPart'partCount :: U'.RWCtx m s => JoinKeyPart (M'.MutMsg s) -> Word16 -> m ()
set_JoinKeyPart'partCount (JoinKeyPart_newtype_ struct) value = H'.setWordField struct (fromIntegral (C'.toWord value) :: Word16) 0 32 0
get_JoinKeyPart'partNum :: U'.ReadCtx m msg => JoinKeyPart msg -> m Word16
get_JoinKeyPart'partNum (JoinKeyPart_newtype_ struct) = H'.getWordField struct 0 48 0
has_JoinKeyPart'partNum :: U'.ReadCtx m msg => JoinKeyPart msg -> m Bool
has_JoinKeyPart'partNum(JoinKeyPart_newtype_ struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_JoinKeyPart'partNum :: U'.RWCtx m s => JoinKeyPart (M'.MutMsg s) -> Word16 -> m ()
set_JoinKeyPart'partNum (JoinKeyPart_newtype_ struct) value = H'.setWordField struct (fromIntegral (C'.toWord value) :: Word16) 0 48 0
newtype JoinResult msg = JoinResult_newtype_ (U'.Struct msg)
instance C'.FromStruct msg (JoinResult msg) where
    fromStruct = pure . JoinResult_newtype_
instance C'.ToStruct msg (JoinResult msg) where
    toStruct (JoinResult_newtype_ struct) = struct
instance U'.HasMessage (JoinResult msg) msg where
    message (JoinResult_newtype_ struct) = U'.message struct
instance U'.MessageDefault (JoinResult msg) msg where
    messageDefault = JoinResult_newtype_ . U'.messageDefault
instance B'.ListElem msg (JoinResult msg) where
    newtype List msg (JoinResult msg) = List_JoinResult (U'.ListOf msg (U'.Struct msg))
    length (List_JoinResult l) = U'.length l
    index i (List_JoinResult l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (JoinResult msg); go = C'.fromStruct} in go)
instance C'.IsPtr msg (JoinResult msg) where
    fromPtr msg ptr = JoinResult_newtype_ <$> C'.fromPtr msg ptr
    toPtr (JoinResult_newtype_ struct) = C'.toPtr struct
instance B'.MutListElem s (JoinResult (M'.MutMsg s)) where
    setIndex (JoinResult_newtype_ elt) i (List_JoinResult l) = U'.setIndex elt i l
    newList msg len = List_JoinResult <$> U'.allocCompositeList msg 1 1 len
instance C'.Allocate s (JoinResult (M'.MutMsg s)) where
    new msg = JoinResult_newtype_ <$> U'.allocStruct msg 1 1
instance C'.IsPtr msg (B'.List msg (JoinResult msg)) where
    fromPtr msg ptr = List_JoinResult <$> C'.fromPtr msg ptr
    toPtr (List_JoinResult l) = C'.toPtr l
get_JoinResult'joinId :: U'.ReadCtx m msg => JoinResult msg -> m Word32
get_JoinResult'joinId (JoinResult_newtype_ struct) = H'.getWordField struct 0 0 0
has_JoinResult'joinId :: U'.ReadCtx m msg => JoinResult msg -> m Bool
has_JoinResult'joinId(JoinResult_newtype_ struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_JoinResult'joinId :: U'.RWCtx m s => JoinResult (M'.MutMsg s) -> Word32 -> m ()
set_JoinResult'joinId (JoinResult_newtype_ struct) value = H'.setWordField struct (fromIntegral (C'.toWord value) :: Word32) 0 0 0
get_JoinResult'succeeded :: U'.ReadCtx m msg => JoinResult msg -> m Bool
get_JoinResult'succeeded (JoinResult_newtype_ struct) = H'.getWordField struct 0 32 0
has_JoinResult'succeeded :: U'.ReadCtx m msg => JoinResult msg -> m Bool
has_JoinResult'succeeded(JoinResult_newtype_ struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_JoinResult'succeeded :: U'.RWCtx m s => JoinResult (M'.MutMsg s) -> Bool -> m ()
set_JoinResult'succeeded (JoinResult_newtype_ struct) value = H'.setWordField struct (fromIntegral (C'.toWord value) :: Word1) 0 32 0
get_JoinResult'cap :: U'.ReadCtx m msg => JoinResult msg -> m (Maybe (U'.Ptr msg))
get_JoinResult'cap (JoinResult_newtype_ struct) =
    U'.getPtr 0 struct
    >>= C'.fromPtr (U'.message struct)
has_JoinResult'cap :: U'.ReadCtx m msg => JoinResult msg -> m Bool
has_JoinResult'cap(JoinResult_newtype_ struct) = Data.Maybe.isJust <$> U'.getPtr 0 struct
set_JoinResult'cap :: U'.RWCtx m s => JoinResult (M'.MutMsg s) -> (Maybe (U'.Ptr (M'.MutMsg s))) -> m ()
set_JoinResult'cap (JoinResult_newtype_ struct) value = U'.setPtr (C'.toPtr value) 0 struct
newtype ProvisionId msg = ProvisionId_newtype_ (U'.Struct msg)
instance C'.FromStruct msg (ProvisionId msg) where
    fromStruct = pure . ProvisionId_newtype_
instance C'.ToStruct msg (ProvisionId msg) where
    toStruct (ProvisionId_newtype_ struct) = struct
instance U'.HasMessage (ProvisionId msg) msg where
    message (ProvisionId_newtype_ struct) = U'.message struct
instance U'.MessageDefault (ProvisionId msg) msg where
    messageDefault = ProvisionId_newtype_ . U'.messageDefault
instance B'.ListElem msg (ProvisionId msg) where
    newtype List msg (ProvisionId msg) = List_ProvisionId (U'.ListOf msg (U'.Struct msg))
    length (List_ProvisionId l) = U'.length l
    index i (List_ProvisionId l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (ProvisionId msg); go = C'.fromStruct} in go)
instance C'.IsPtr msg (ProvisionId msg) where
    fromPtr msg ptr = ProvisionId_newtype_ <$> C'.fromPtr msg ptr
    toPtr (ProvisionId_newtype_ struct) = C'.toPtr struct
instance B'.MutListElem s (ProvisionId (M'.MutMsg s)) where
    setIndex (ProvisionId_newtype_ elt) i (List_ProvisionId l) = U'.setIndex elt i l
    newList msg len = List_ProvisionId <$> U'.allocCompositeList msg 1 0 len
instance C'.Allocate s (ProvisionId (M'.MutMsg s)) where
    new msg = ProvisionId_newtype_ <$> U'.allocStruct msg 1 0
instance C'.IsPtr msg (B'.List msg (ProvisionId msg)) where
    fromPtr msg ptr = List_ProvisionId <$> C'.fromPtr msg ptr
    toPtr (List_ProvisionId l) = C'.toPtr l
get_ProvisionId'joinId :: U'.ReadCtx m msg => ProvisionId msg -> m Word32
get_ProvisionId'joinId (ProvisionId_newtype_ struct) = H'.getWordField struct 0 0 0
has_ProvisionId'joinId :: U'.ReadCtx m msg => ProvisionId msg -> m Bool
has_ProvisionId'joinId(ProvisionId_newtype_ struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_ProvisionId'joinId :: U'.RWCtx m s => ProvisionId (M'.MutMsg s) -> Word32 -> m ()
set_ProvisionId'joinId (ProvisionId_newtype_ struct) value = H'.setWordField struct (fromIntegral (C'.toWord value) :: Word32) 0 0 0
data Side
    = Side'server
    | Side'client
    | Side'unknown' Word16
    deriving(Show,Read,Eq,Generic)
instance Enum Side where
    toEnum = C'.fromWord . fromIntegral
    fromEnum = fromIntegral . C'.toWord
instance C'.IsWord Side where
    fromWord n = go (fromIntegral n :: Word16) where
        go 0 = Side'server
        go 1 = Side'client
        go tag = Side'unknown' (fromIntegral tag)
    toWord Side'server = 0
    toWord Side'client = 1
    toWord (Side'unknown' tag) = fromIntegral tag
instance B'.ListElem msg Side where
    newtype List msg Side = List_Side (U'.ListOf msg Word16)
    length (List_Side l) = U'.length l
    index i (List_Side l) = (C'.fromWord . fromIntegral) <$> U'.index i l
instance B'.MutListElem s Side where
    setIndex elt i (List_Side l) = U'.setIndex (fromIntegral $ C'.toWord elt) i l
    newList msg size = List_Side <$> U'.allocList16 msg size
instance C'.IsPtr msg (B'.List msg Side) where
    fromPtr msg ptr = List_Side <$> C'.fromPtr msg ptr
    toPtr (List_Side l) = C'.toPtr l
newtype VatId msg = VatId_newtype_ (U'.Struct msg)
instance C'.FromStruct msg (VatId msg) where
    fromStruct = pure . VatId_newtype_
instance C'.ToStruct msg (VatId msg) where
    toStruct (VatId_newtype_ struct) = struct
instance U'.HasMessage (VatId msg) msg where
    message (VatId_newtype_ struct) = U'.message struct
instance U'.MessageDefault (VatId msg) msg where
    messageDefault = VatId_newtype_ . U'.messageDefault
instance B'.ListElem msg (VatId msg) where
    newtype List msg (VatId msg) = List_VatId (U'.ListOf msg (U'.Struct msg))
    length (List_VatId l) = U'.length l
    index i (List_VatId l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (VatId msg); go = C'.fromStruct} in go)
instance C'.IsPtr msg (VatId msg) where
    fromPtr msg ptr = VatId_newtype_ <$> C'.fromPtr msg ptr
    toPtr (VatId_newtype_ struct) = C'.toPtr struct
instance B'.MutListElem s (VatId (M'.MutMsg s)) where
    setIndex (VatId_newtype_ elt) i (List_VatId l) = U'.setIndex elt i l
    newList msg len = List_VatId <$> U'.allocCompositeList msg 1 0 len
instance C'.Allocate s (VatId (M'.MutMsg s)) where
    new msg = VatId_newtype_ <$> U'.allocStruct msg 1 0
instance C'.IsPtr msg (B'.List msg (VatId msg)) where
    fromPtr msg ptr = List_VatId <$> C'.fromPtr msg ptr
    toPtr (List_VatId l) = C'.toPtr l
get_VatId'side :: U'.ReadCtx m msg => VatId msg -> m Side
get_VatId'side (VatId_newtype_ struct) = H'.getWordField struct 0 0 0
has_VatId'side :: U'.ReadCtx m msg => VatId msg -> m Bool
has_VatId'side(VatId_newtype_ struct) = pure $ 0 < U'.length (U'.dataSection struct)
set_VatId'side :: U'.RWCtx m s => VatId (M'.MutMsg s) -> Side -> m ()
set_VatId'side (VatId_newtype_ struct) value = H'.setWordField struct (fromIntegral (C'.toWord value) :: Word16) 0 0 0