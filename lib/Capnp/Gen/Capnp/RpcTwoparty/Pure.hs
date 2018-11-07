{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-orphans #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{- |
Module: Capnp.Gen.Capnp.RpcTwoparty.Pure
Description: High-level generated module for capnp/rpc-twoparty.capnp
This module is the generated code for capnp/rpc-twoparty.capnp,
for the high-level api.
-}
module Capnp.Gen.Capnp.RpcTwoparty.Pure (JoinKeyPart(..), JoinResult(..), ProvisionId(..), RecipientId(..), Capnp.Gen.ById.Xa184c7885cdaf2a1.Side(..), ThirdPartyCapId(..), VatId(..)
) where
-- Code generated by capnpc-haskell. DO NOT EDIT.
-- Generated from schema file: capnp/rpc-twoparty.capnp
import Data.Int
import Data.Word
import Data.Default (Default(def))
import GHC.Generics (Generic)
import Capnp.Basics.Pure (Data, Text)
import Control.Monad.Catch (MonadThrow(throwM))
import Control.Concurrent.STM (atomically)
import Control.Monad.IO.Class (liftIO)
import Capnp.TraversalLimit (MonadLimit, evalLimitT)
import Control.Monad (forM_)
import qualified Capnp.Convert as Convert
import qualified Capnp.Message as M'
import qualified Capnp.Untyped as U'
import qualified Capnp.Untyped.Pure as PU'
import qualified Capnp.GenHelpers.Pure as PH'
import qualified Capnp.Classes as C'
import qualified Data.Vector as V
import qualified Data.ByteString as BS
import qualified Capnp.Gen.ById.Xa184c7885cdaf2a1
import qualified Capnp.Gen.ById.Xbdf87d7bb8304e81.Pure
import qualified Capnp.Gen.ById.Xbdf87d7bb8304e81
data JoinKeyPart
    = JoinKeyPart
        {joinId :: Word32,
        partCount :: Word16,
        partNum :: Word16}
    deriving(Show,Read,Eq,Generic)
instance C'.Decerialize JoinKeyPart where
    type Cerial msg JoinKeyPart = Capnp.Gen.ById.Xa184c7885cdaf2a1.JoinKeyPart msg
    decerialize raw = do
        JoinKeyPart <$>
            (Capnp.Gen.ById.Xa184c7885cdaf2a1.get_JoinKeyPart'joinId raw) <*>
            (Capnp.Gen.ById.Xa184c7885cdaf2a1.get_JoinKeyPart'partCount raw) <*>
            (Capnp.Gen.ById.Xa184c7885cdaf2a1.get_JoinKeyPart'partNum raw)
instance C'.Marshal JoinKeyPart where
    marshalInto raw value = do
        case value of
            JoinKeyPart{..} -> do
                Capnp.Gen.ById.Xa184c7885cdaf2a1.set_JoinKeyPart'joinId raw joinId
                Capnp.Gen.ById.Xa184c7885cdaf2a1.set_JoinKeyPart'partCount raw partCount
                Capnp.Gen.ById.Xa184c7885cdaf2a1.set_JoinKeyPart'partNum raw partNum
instance C'.Cerialize s JoinKeyPart
instance C'.FromStruct M'.ConstMsg JoinKeyPart where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.Gen.ById.Xa184c7885cdaf2a1.JoinKeyPart M'.ConstMsg)
instance Default JoinKeyPart where
    def = PH'.defaultStruct
data JoinResult
    = JoinResult
        {joinId :: Word32,
        succeeded :: Bool,
        cap :: Maybe (PU'.PtrType)}
    deriving(Show,Read,Eq,Generic)
instance C'.Decerialize JoinResult where
    type Cerial msg JoinResult = Capnp.Gen.ById.Xa184c7885cdaf2a1.JoinResult msg
    decerialize raw = do
        JoinResult <$>
            (Capnp.Gen.ById.Xa184c7885cdaf2a1.get_JoinResult'joinId raw) <*>
            (Capnp.Gen.ById.Xa184c7885cdaf2a1.get_JoinResult'succeeded raw) <*>
            (Capnp.Gen.ById.Xa184c7885cdaf2a1.get_JoinResult'cap raw >>= C'.decerialize)
instance C'.Marshal JoinResult where
    marshalInto raw value = do
        case value of
            JoinResult{..} -> do
                Capnp.Gen.ById.Xa184c7885cdaf2a1.set_JoinResult'joinId raw joinId
                Capnp.Gen.ById.Xa184c7885cdaf2a1.set_JoinResult'succeeded raw succeeded
                field_ <- C'.cerialize (U'.message raw) cap
                Capnp.Gen.ById.Xa184c7885cdaf2a1.set_JoinResult'cap raw field_
instance C'.Cerialize s JoinResult
instance C'.FromStruct M'.ConstMsg JoinResult where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.Gen.ById.Xa184c7885cdaf2a1.JoinResult M'.ConstMsg)
instance Default JoinResult where
    def = PH'.defaultStruct
data ProvisionId
    = ProvisionId
        {joinId :: Word32}
    deriving(Show,Read,Eq,Generic)
instance C'.Decerialize ProvisionId where
    type Cerial msg ProvisionId = Capnp.Gen.ById.Xa184c7885cdaf2a1.ProvisionId msg
    decerialize raw = do
        ProvisionId <$>
            (Capnp.Gen.ById.Xa184c7885cdaf2a1.get_ProvisionId'joinId raw)
instance C'.Marshal ProvisionId where
    marshalInto raw value = do
        case value of
            ProvisionId{..} -> do
                Capnp.Gen.ById.Xa184c7885cdaf2a1.set_ProvisionId'joinId raw joinId
instance C'.Cerialize s ProvisionId
instance C'.FromStruct M'.ConstMsg ProvisionId where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.Gen.ById.Xa184c7885cdaf2a1.ProvisionId M'.ConstMsg)
instance Default ProvisionId where
    def = PH'.defaultStruct
data RecipientId
    = RecipientId
    deriving(Show,Read,Eq,Generic)
instance C'.Decerialize RecipientId where
    type Cerial msg RecipientId = Capnp.Gen.ById.Xa184c7885cdaf2a1.RecipientId msg
    decerialize raw = do
        pure $ RecipientId
instance C'.Marshal RecipientId where
    marshalInto raw value = do
        case value of
            RecipientId -> pure ()
instance C'.Cerialize s RecipientId
instance C'.FromStruct M'.ConstMsg RecipientId where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.Gen.ById.Xa184c7885cdaf2a1.RecipientId M'.ConstMsg)
instance Default RecipientId where
    def = PH'.defaultStruct
instance C'.Decerialize Capnp.Gen.ById.Xa184c7885cdaf2a1.Side where
    type Cerial msg Capnp.Gen.ById.Xa184c7885cdaf2a1.Side = Capnp.Gen.ById.Xa184c7885cdaf2a1.Side
    decerialize = pure
data ThirdPartyCapId
    = ThirdPartyCapId
    deriving(Show,Read,Eq,Generic)
instance C'.Decerialize ThirdPartyCapId where
    type Cerial msg ThirdPartyCapId = Capnp.Gen.ById.Xa184c7885cdaf2a1.ThirdPartyCapId msg
    decerialize raw = do
        pure $ ThirdPartyCapId
instance C'.Marshal ThirdPartyCapId where
    marshalInto raw value = do
        case value of
            ThirdPartyCapId -> pure ()
instance C'.Cerialize s ThirdPartyCapId
instance C'.FromStruct M'.ConstMsg ThirdPartyCapId where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.Gen.ById.Xa184c7885cdaf2a1.ThirdPartyCapId M'.ConstMsg)
instance Default ThirdPartyCapId where
    def = PH'.defaultStruct
data VatId
    = VatId
        {side :: Capnp.Gen.ById.Xa184c7885cdaf2a1.Side}
    deriving(Show,Read,Eq,Generic)
instance C'.Decerialize VatId where
    type Cerial msg VatId = Capnp.Gen.ById.Xa184c7885cdaf2a1.VatId msg
    decerialize raw = do
        VatId <$>
            (Capnp.Gen.ById.Xa184c7885cdaf2a1.get_VatId'side raw)
instance C'.Marshal VatId where
    marshalInto raw value = do
        case value of
            VatId{..} -> do
                Capnp.Gen.ById.Xa184c7885cdaf2a1.set_VatId'side raw side
instance C'.Cerialize s VatId
instance C'.FromStruct M'.ConstMsg VatId where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.Gen.ById.Xa184c7885cdaf2a1.VatId M'.ConstMsg)
instance Default VatId where
    def = PH'.defaultStruct