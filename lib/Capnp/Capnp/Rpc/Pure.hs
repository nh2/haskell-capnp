{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{- |
Module: Capnp.Capnp.Rpc.Pure
Description: High-level generated module for capnp/rpc.capnp
This module is the generated code for capnp/rpc.capnp,
for the high-level api.
-}
module Capnp.Capnp.Rpc.Pure (Accept(..), Bootstrap(..), Call(..), CapDescriptor(..), Disembargo(..), Exception(..), Finish(..), Join(..), Message(..), MessageTarget(..), Payload(..), PromisedAnswer(..), Provide(..), Release(..), Resolve(..), Return(..), ThirdPartyCapDescriptor(..), Call'sendResultsTo(..), Disembargo'context(..), Capnp.ById.Xb312981b2552a250.Exception'Type(..), PromisedAnswer'Op(..), Resolve'(..), Return'(..)
) where
-- Code generated by capnpc-haskell. DO NOT EDIT.
-- Generated from schema file: capnp/rpc.capnp
import Data.Int
import Data.Word
import Data.Capnp.Untyped.Pure (List)
import Data.Capnp.Basics.Pure (Data, Text)
import Control.Monad.Catch (MonadThrow)
import Data.Capnp.TraversalLimit (MonadLimit)
import Control.Monad (forM_)
import qualified Data.Capnp.Message as M'
import qualified Data.Capnp.Untyped as U'
import qualified Data.Capnp.Untyped.Pure as PU'
import qualified Codec.Capnp as C'
import qualified Data.Capnp.GenHelpers.Pure as PH'
import qualified Data.Vector as V
import qualified Data.ByteString as BS
import qualified Capnp.ById.Xb312981b2552a250
import qualified Capnp.ById.Xbdf87d7bb8304e81.Pure
import qualified Capnp.ById.Xbdf87d7bb8304e81
data Accept
     = Accept
        {questionId :: Word32,
        provision :: Maybe (PU'.PtrType),
        embargo :: Bool}
    deriving(Show, Read, Eq)
instance C'.Decerialize Accept where
    type Cerial msg Accept = Capnp.ById.Xb312981b2552a250.Accept msg
    decerialize raw = do
        Accept <$>
            (Capnp.ById.Xb312981b2552a250.get_Accept'questionId raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Accept'provision raw >>= C'.decerialize) <*>
            (Capnp.ById.Xb312981b2552a250.get_Accept'embargo raw)
instance C'.FromStruct M'.ConstMsg Accept where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Accept M'.ConstMsg)
instance C'.Marshal Accept where
    marshalInto raw value = do
        case value of
            Accept{..} -> do
                Capnp.ById.Xb312981b2552a250.set_Accept'questionId raw questionId
                field_ <- C'.cerialize (U'.message raw) provision
                Capnp.ById.Xb312981b2552a250.set_Accept'provision raw field_
                Capnp.ById.Xb312981b2552a250.set_Accept'embargo raw embargo
instance C'.Cerialize s Accept
data Bootstrap
     = Bootstrap
        {questionId :: Word32,
        deprecatedObjectId :: Maybe (PU'.PtrType)}
    deriving(Show, Read, Eq)
instance C'.Decerialize Bootstrap where
    type Cerial msg Bootstrap = Capnp.ById.Xb312981b2552a250.Bootstrap msg
    decerialize raw = do
        Bootstrap <$>
            (Capnp.ById.Xb312981b2552a250.get_Bootstrap'questionId raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Bootstrap'deprecatedObjectId raw >>= C'.decerialize)
instance C'.FromStruct M'.ConstMsg Bootstrap where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Bootstrap M'.ConstMsg)
instance C'.Marshal Bootstrap where
    marshalInto raw value = do
        case value of
            Bootstrap{..} -> do
                Capnp.ById.Xb312981b2552a250.set_Bootstrap'questionId raw questionId
                field_ <- C'.cerialize (U'.message raw) deprecatedObjectId
                Capnp.ById.Xb312981b2552a250.set_Bootstrap'deprecatedObjectId raw field_
instance C'.Cerialize s Bootstrap
data Call
     = Call
        {questionId :: Word32,
        target :: MessageTarget,
        interfaceId :: Word64,
        methodId :: Word16,
        params :: Payload,
        sendResultsTo :: Call'sendResultsTo,
        allowThirdPartyTailCall :: Bool}
    deriving(Show, Read, Eq)
instance C'.Decerialize Call where
    type Cerial msg Call = Capnp.ById.Xb312981b2552a250.Call msg
    decerialize raw = do
        Call <$>
            (Capnp.ById.Xb312981b2552a250.get_Call'questionId raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Call'target raw >>= C'.decerialize) <*>
            (Capnp.ById.Xb312981b2552a250.get_Call'interfaceId raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Call'methodId raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Call'params raw >>= C'.decerialize) <*>
            (Capnp.ById.Xb312981b2552a250.get_Call'sendResultsTo raw >>= C'.decerialize) <*>
            (Capnp.ById.Xb312981b2552a250.get_Call'allowThirdPartyTailCall raw)
instance C'.FromStruct M'.ConstMsg Call where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Call M'.ConstMsg)
instance C'.Marshal Call where
    marshalInto raw value = do
        case value of
            Call{..} -> do
                Capnp.ById.Xb312981b2552a250.set_Call'questionId raw questionId
                field_ <- Capnp.ById.Xb312981b2552a250.new_Call'target raw
                C'.marshalInto field_ target
                Capnp.ById.Xb312981b2552a250.set_Call'interfaceId raw interfaceId
                Capnp.ById.Xb312981b2552a250.set_Call'methodId raw methodId
                field_ <- Capnp.ById.Xb312981b2552a250.new_Call'params raw
                C'.marshalInto field_ params
                field_ <- Capnp.ById.Xb312981b2552a250.get_Call'sendResultsTo raw
                C'.marshalInto field_ sendResultsTo
                Capnp.ById.Xb312981b2552a250.set_Call'allowThirdPartyTailCall raw allowThirdPartyTailCall
instance C'.Cerialize s Call
data CapDescriptor
     = CapDescriptor'none |
    CapDescriptor'senderHosted (Word32) |
    CapDescriptor'senderPromise (Word32) |
    CapDescriptor'receiverHosted (Word32) |
    CapDescriptor'receiverAnswer (PromisedAnswer) |
    CapDescriptor'thirdPartyHosted (ThirdPartyCapDescriptor) |
    CapDescriptor'unknown' (Word16)
    deriving(Show, Read, Eq)
instance C'.Decerialize CapDescriptor where
    type Cerial msg CapDescriptor = Capnp.ById.Xb312981b2552a250.CapDescriptor msg
    decerialize raw = do
        raw <- Capnp.ById.Xb312981b2552a250.get_CapDescriptor' raw
        case raw of
            Capnp.ById.Xb312981b2552a250.CapDescriptor'none -> pure CapDescriptor'none
            Capnp.ById.Xb312981b2552a250.CapDescriptor'senderHosted val -> pure (CapDescriptor'senderHosted val)
            Capnp.ById.Xb312981b2552a250.CapDescriptor'senderPromise val -> pure (CapDescriptor'senderPromise val)
            Capnp.ById.Xb312981b2552a250.CapDescriptor'receiverHosted val -> pure (CapDescriptor'receiverHosted val)
            Capnp.ById.Xb312981b2552a250.CapDescriptor'receiverAnswer val -> CapDescriptor'receiverAnswer <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.CapDescriptor'thirdPartyHosted val -> CapDescriptor'thirdPartyHosted <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.CapDescriptor'unknown' val -> pure (CapDescriptor'unknown' val)
instance C'.FromStruct M'.ConstMsg CapDescriptor where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.CapDescriptor M'.ConstMsg)
instance C'.Marshal CapDescriptor where
    marshalInto raw value = do
        case value of
            CapDescriptor'none -> Capnp.ById.Xb312981b2552a250.set_CapDescriptor'none raw
            CapDescriptor'senderHosted arg_ -> Capnp.ById.Xb312981b2552a250.set_CapDescriptor'senderHosted raw arg_
            CapDescriptor'senderPromise arg_ -> Capnp.ById.Xb312981b2552a250.set_CapDescriptor'senderPromise raw arg_
            CapDescriptor'receiverHosted arg_ -> Capnp.ById.Xb312981b2552a250.set_CapDescriptor'receiverHosted raw arg_
            CapDescriptor'receiverAnswer arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_CapDescriptor'receiverAnswer raw
                C'.marshalInto field_ arg_
            CapDescriptor'thirdPartyHosted arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_CapDescriptor'thirdPartyHosted raw
                C'.marshalInto field_ arg_
            CapDescriptor'unknown' arg_ -> Capnp.ById.Xb312981b2552a250.set_CapDescriptor'unknown' raw arg_
instance C'.Cerialize s CapDescriptor
data Disembargo
     = Disembargo
        {target :: MessageTarget,
        context :: Disembargo'context}
    deriving(Show, Read, Eq)
instance C'.Decerialize Disembargo where
    type Cerial msg Disembargo = Capnp.ById.Xb312981b2552a250.Disembargo msg
    decerialize raw = do
        Disembargo <$>
            (Capnp.ById.Xb312981b2552a250.get_Disembargo'target raw >>= C'.decerialize) <*>
            (Capnp.ById.Xb312981b2552a250.get_Disembargo'context raw >>= C'.decerialize)
instance C'.FromStruct M'.ConstMsg Disembargo where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Disembargo M'.ConstMsg)
instance C'.Marshal Disembargo where
    marshalInto raw value = do
        case value of
            Disembargo{..} -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Disembargo'target raw
                C'.marshalInto field_ target
                field_ <- Capnp.ById.Xb312981b2552a250.get_Disembargo'context raw
                C'.marshalInto field_ context
instance C'.Cerialize s Disembargo
data Exception
     = Exception
        {reason :: Text,
        obsoleteIsCallersFault :: Bool,
        obsoleteDurability :: Word16,
        type_ :: Capnp.ById.Xb312981b2552a250.Exception'Type}
    deriving(Show, Read, Eq)
instance C'.Decerialize Exception where
    type Cerial msg Exception = Capnp.ById.Xb312981b2552a250.Exception msg
    decerialize raw = do
        Exception <$>
            (Capnp.ById.Xb312981b2552a250.get_Exception'reason raw >>= C'.decerialize) <*>
            (Capnp.ById.Xb312981b2552a250.get_Exception'obsoleteIsCallersFault raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Exception'obsoleteDurability raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Exception'type_ raw)
instance C'.FromStruct M'.ConstMsg Exception where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Exception M'.ConstMsg)
instance C'.Marshal Exception where
    marshalInto raw value = do
        case value of
            Exception{..} -> do
                field_ <- PH'.marshalText raw reason
                Capnp.ById.Xb312981b2552a250.set_Exception'reason raw field_
                Capnp.ById.Xb312981b2552a250.set_Exception'obsoleteIsCallersFault raw obsoleteIsCallersFault
                Capnp.ById.Xb312981b2552a250.set_Exception'obsoleteDurability raw obsoleteDurability
                Capnp.ById.Xb312981b2552a250.set_Exception'type_ raw type_
instance C'.Cerialize s Exception
data Finish
     = Finish
        {questionId :: Word32,
        releaseResultCaps :: Bool}
    deriving(Show, Read, Eq)
instance C'.Decerialize Finish where
    type Cerial msg Finish = Capnp.ById.Xb312981b2552a250.Finish msg
    decerialize raw = do
        Finish <$>
            (Capnp.ById.Xb312981b2552a250.get_Finish'questionId raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Finish'releaseResultCaps raw)
instance C'.FromStruct M'.ConstMsg Finish where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Finish M'.ConstMsg)
instance C'.Marshal Finish where
    marshalInto raw value = do
        case value of
            Finish{..} -> do
                Capnp.ById.Xb312981b2552a250.set_Finish'questionId raw questionId
                Capnp.ById.Xb312981b2552a250.set_Finish'releaseResultCaps raw releaseResultCaps
instance C'.Cerialize s Finish
data Join
     = Join
        {questionId :: Word32,
        target :: MessageTarget,
        keyPart :: Maybe (PU'.PtrType)}
    deriving(Show, Read, Eq)
instance C'.Decerialize Join where
    type Cerial msg Join = Capnp.ById.Xb312981b2552a250.Join msg
    decerialize raw = do
        Join <$>
            (Capnp.ById.Xb312981b2552a250.get_Join'questionId raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Join'target raw >>= C'.decerialize) <*>
            (Capnp.ById.Xb312981b2552a250.get_Join'keyPart raw >>= C'.decerialize)
instance C'.FromStruct M'.ConstMsg Join where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Join M'.ConstMsg)
instance C'.Marshal Join where
    marshalInto raw value = do
        case value of
            Join{..} -> do
                Capnp.ById.Xb312981b2552a250.set_Join'questionId raw questionId
                field_ <- Capnp.ById.Xb312981b2552a250.new_Join'target raw
                C'.marshalInto field_ target
                field_ <- C'.cerialize (U'.message raw) keyPart
                Capnp.ById.Xb312981b2552a250.set_Join'keyPart raw field_
instance C'.Cerialize s Join
data Message
     = Message'unimplemented (Message) |
    Message'abort (Exception) |
    Message'call (Call) |
    Message'return (Return) |
    Message'finish (Finish) |
    Message'resolve (Resolve) |
    Message'release (Release) |
    Message'obsoleteSave (Maybe (PU'.PtrType)) |
    Message'bootstrap (Bootstrap) |
    Message'obsoleteDelete (Maybe (PU'.PtrType)) |
    Message'provide (Provide) |
    Message'accept (Accept) |
    Message'join (Join) |
    Message'disembargo (Disembargo) |
    Message'unknown' (Word16)
    deriving(Show, Read, Eq)
instance C'.Decerialize Message where
    type Cerial msg Message = Capnp.ById.Xb312981b2552a250.Message msg
    decerialize raw = do
        raw <- Capnp.ById.Xb312981b2552a250.get_Message' raw
        case raw of
            Capnp.ById.Xb312981b2552a250.Message'unimplemented val -> Message'unimplemented <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'abort val -> Message'abort <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'call val -> Message'call <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'return val -> Message'return <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'finish val -> Message'finish <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'resolve val -> Message'resolve <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'release val -> Message'release <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'obsoleteSave val -> Message'obsoleteSave <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'bootstrap val -> Message'bootstrap <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'obsoleteDelete val -> Message'obsoleteDelete <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'provide val -> Message'provide <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'accept val -> Message'accept <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'join val -> Message'join <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'disembargo val -> Message'disembargo <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Message'unknown' val -> pure (Message'unknown' val)
instance C'.FromStruct M'.ConstMsg Message where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Message M'.ConstMsg)
instance C'.Marshal Message where
    marshalInto raw value = do
        case value of
            Message'unimplemented arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'unimplemented raw
                C'.marshalInto field_ arg_
            Message'abort arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'abort raw
                C'.marshalInto field_ arg_
            Message'call arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'call raw
                C'.marshalInto field_ arg_
            Message'return arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'return raw
                C'.marshalInto field_ arg_
            Message'finish arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'finish raw
                C'.marshalInto field_ arg_
            Message'resolve arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'resolve raw
                C'.marshalInto field_ arg_
            Message'release arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'release raw
                C'.marshalInto field_ arg_
            Message'obsoleteSave arg_ -> do
                field_ <- C'.cerialize (U'.message raw) arg_
                Capnp.ById.Xb312981b2552a250.set_Message'obsoleteSave raw field_
            Message'bootstrap arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'bootstrap raw
                C'.marshalInto field_ arg_
            Message'obsoleteDelete arg_ -> do
                field_ <- C'.cerialize (U'.message raw) arg_
                Capnp.ById.Xb312981b2552a250.set_Message'obsoleteDelete raw field_
            Message'provide arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'provide raw
                C'.marshalInto field_ arg_
            Message'accept arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'accept raw
                C'.marshalInto field_ arg_
            Message'join arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'join raw
                C'.marshalInto field_ arg_
            Message'disembargo arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Message'disembargo raw
                C'.marshalInto field_ arg_
            Message'unknown' arg_ -> Capnp.ById.Xb312981b2552a250.set_Message'unknown' raw arg_
instance C'.Cerialize s Message
data MessageTarget
     = MessageTarget'importedCap (Word32) |
    MessageTarget'promisedAnswer (PromisedAnswer) |
    MessageTarget'unknown' (Word16)
    deriving(Show, Read, Eq)
instance C'.Decerialize MessageTarget where
    type Cerial msg MessageTarget = Capnp.ById.Xb312981b2552a250.MessageTarget msg
    decerialize raw = do
        raw <- Capnp.ById.Xb312981b2552a250.get_MessageTarget' raw
        case raw of
            Capnp.ById.Xb312981b2552a250.MessageTarget'importedCap val -> pure (MessageTarget'importedCap val)
            Capnp.ById.Xb312981b2552a250.MessageTarget'promisedAnswer val -> MessageTarget'promisedAnswer <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.MessageTarget'unknown' val -> pure (MessageTarget'unknown' val)
instance C'.FromStruct M'.ConstMsg MessageTarget where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.MessageTarget M'.ConstMsg)
instance C'.Marshal MessageTarget where
    marshalInto raw value = do
        case value of
            MessageTarget'importedCap arg_ -> Capnp.ById.Xb312981b2552a250.set_MessageTarget'importedCap raw arg_
            MessageTarget'promisedAnswer arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_MessageTarget'promisedAnswer raw
                C'.marshalInto field_ arg_
            MessageTarget'unknown' arg_ -> Capnp.ById.Xb312981b2552a250.set_MessageTarget'unknown' raw arg_
instance C'.Cerialize s MessageTarget
data Payload
     = Payload
        {content :: Maybe (PU'.PtrType),
        capTable :: List (CapDescriptor)}
    deriving(Show, Read, Eq)
instance C'.Decerialize Payload where
    type Cerial msg Payload = Capnp.ById.Xb312981b2552a250.Payload msg
    decerialize raw = do
        Payload <$>
            (Capnp.ById.Xb312981b2552a250.get_Payload'content raw >>= C'.decerialize) <*>
            (Capnp.ById.Xb312981b2552a250.get_Payload'capTable raw >>= C'.decerialize)
instance C'.FromStruct M'.ConstMsg Payload where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Payload M'.ConstMsg)
instance C'.Marshal Payload where
    marshalInto raw value = do
        case value of
            Payload{..} -> do
                field_ <- C'.cerialize (U'.message raw) content
                Capnp.ById.Xb312981b2552a250.set_Payload'content raw field_
                let len_ = V.length capTable
                field_ <- Capnp.ById.Xb312981b2552a250.new_Payload'capTable len_ raw
                forM_ [0..len_ - 1] $ \i -> do
                    elt <- C'.index i field_
                    C'.marshalInto elt (capTable V.! i)
instance C'.Cerialize s Payload
data PromisedAnswer
     = PromisedAnswer
        {questionId :: Word32,
        transform :: List (PromisedAnswer'Op)}
    deriving(Show, Read, Eq)
instance C'.Decerialize PromisedAnswer where
    type Cerial msg PromisedAnswer = Capnp.ById.Xb312981b2552a250.PromisedAnswer msg
    decerialize raw = do
        PromisedAnswer <$>
            (Capnp.ById.Xb312981b2552a250.get_PromisedAnswer'questionId raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_PromisedAnswer'transform raw >>= C'.decerialize)
instance C'.FromStruct M'.ConstMsg PromisedAnswer where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.PromisedAnswer M'.ConstMsg)
instance C'.Marshal PromisedAnswer where
    marshalInto raw value = do
        case value of
            PromisedAnswer{..} -> do
                Capnp.ById.Xb312981b2552a250.set_PromisedAnswer'questionId raw questionId
                let len_ = V.length transform
                field_ <- Capnp.ById.Xb312981b2552a250.new_PromisedAnswer'transform len_ raw
                forM_ [0..len_ - 1] $ \i -> do
                    elt <- C'.index i field_
                    C'.marshalInto elt (transform V.! i)
instance C'.Cerialize s PromisedAnswer
data Provide
     = Provide
        {questionId :: Word32,
        target :: MessageTarget,
        recipient :: Maybe (PU'.PtrType)}
    deriving(Show, Read, Eq)
instance C'.Decerialize Provide where
    type Cerial msg Provide = Capnp.ById.Xb312981b2552a250.Provide msg
    decerialize raw = do
        Provide <$>
            (Capnp.ById.Xb312981b2552a250.get_Provide'questionId raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Provide'target raw >>= C'.decerialize) <*>
            (Capnp.ById.Xb312981b2552a250.get_Provide'recipient raw >>= C'.decerialize)
instance C'.FromStruct M'.ConstMsg Provide where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Provide M'.ConstMsg)
instance C'.Marshal Provide where
    marshalInto raw value = do
        case value of
            Provide{..} -> do
                Capnp.ById.Xb312981b2552a250.set_Provide'questionId raw questionId
                field_ <- Capnp.ById.Xb312981b2552a250.new_Provide'target raw
                C'.marshalInto field_ target
                field_ <- C'.cerialize (U'.message raw) recipient
                Capnp.ById.Xb312981b2552a250.set_Provide'recipient raw field_
instance C'.Cerialize s Provide
data Release
     = Release
        {id :: Word32,
        referenceCount :: Word32}
    deriving(Show, Read, Eq)
instance C'.Decerialize Release where
    type Cerial msg Release = Capnp.ById.Xb312981b2552a250.Release msg
    decerialize raw = do
        Release <$>
            (Capnp.ById.Xb312981b2552a250.get_Release'id raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Release'referenceCount raw)
instance C'.FromStruct M'.ConstMsg Release where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Release M'.ConstMsg)
instance C'.Marshal Release where
    marshalInto raw value = do
        case value of
            Release{..} -> do
                Capnp.ById.Xb312981b2552a250.set_Release'id raw id
                Capnp.ById.Xb312981b2552a250.set_Release'referenceCount raw referenceCount
instance C'.Cerialize s Release
data Resolve
     = Resolve
        {promiseId :: Word32,
        union' :: Resolve'}
    deriving(Show, Read, Eq)
instance C'.Decerialize Resolve where
    type Cerial msg Resolve = Capnp.ById.Xb312981b2552a250.Resolve msg
    decerialize raw = do
        Resolve <$>
            (Capnp.ById.Xb312981b2552a250.get_Resolve'promiseId raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Resolve'union' raw >>= C'.decerialize)
instance C'.FromStruct M'.ConstMsg Resolve where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Resolve M'.ConstMsg)
instance C'.Marshal Resolve where
    marshalInto raw value = do
        case value of
            Resolve{..} -> do
                Capnp.ById.Xb312981b2552a250.set_Resolve'promiseId raw promiseId
                field_ <- Capnp.ById.Xb312981b2552a250.get_Resolve'union' raw
                C'.marshalInto field_ union'
instance C'.Cerialize s Resolve
data Return
     = Return
        {answerId :: Word32,
        releaseParamCaps :: Bool,
        union' :: Return'}
    deriving(Show, Read, Eq)
instance C'.Decerialize Return where
    type Cerial msg Return = Capnp.ById.Xb312981b2552a250.Return msg
    decerialize raw = do
        Return <$>
            (Capnp.ById.Xb312981b2552a250.get_Return'answerId raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Return'releaseParamCaps raw) <*>
            (Capnp.ById.Xb312981b2552a250.get_Return'union' raw >>= C'.decerialize)
instance C'.FromStruct M'.ConstMsg Return where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Return M'.ConstMsg)
instance C'.Marshal Return where
    marshalInto raw value = do
        case value of
            Return{..} -> do
                Capnp.ById.Xb312981b2552a250.set_Return'answerId raw answerId
                Capnp.ById.Xb312981b2552a250.set_Return'releaseParamCaps raw releaseParamCaps
                field_ <- Capnp.ById.Xb312981b2552a250.get_Return'union' raw
                C'.marshalInto field_ union'
instance C'.Cerialize s Return
data ThirdPartyCapDescriptor
     = ThirdPartyCapDescriptor
        {id :: Maybe (PU'.PtrType),
        vineId :: Word32}
    deriving(Show, Read, Eq)
instance C'.Decerialize ThirdPartyCapDescriptor where
    type Cerial msg ThirdPartyCapDescriptor = Capnp.ById.Xb312981b2552a250.ThirdPartyCapDescriptor msg
    decerialize raw = do
        ThirdPartyCapDescriptor <$>
            (Capnp.ById.Xb312981b2552a250.get_ThirdPartyCapDescriptor'id raw >>= C'.decerialize) <*>
            (Capnp.ById.Xb312981b2552a250.get_ThirdPartyCapDescriptor'vineId raw)
instance C'.FromStruct M'.ConstMsg ThirdPartyCapDescriptor where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.ThirdPartyCapDescriptor M'.ConstMsg)
instance C'.Marshal ThirdPartyCapDescriptor where
    marshalInto raw value = do
        case value of
            ThirdPartyCapDescriptor{..} -> do
                field_ <- C'.cerialize (U'.message raw) id
                Capnp.ById.Xb312981b2552a250.set_ThirdPartyCapDescriptor'id raw field_
                Capnp.ById.Xb312981b2552a250.set_ThirdPartyCapDescriptor'vineId raw vineId
instance C'.Cerialize s ThirdPartyCapDescriptor
data Call'sendResultsTo
     = Call'sendResultsTo'caller |
    Call'sendResultsTo'yourself |
    Call'sendResultsTo'thirdParty (Maybe (PU'.PtrType)) |
    Call'sendResultsTo'unknown' (Word16)
    deriving(Show, Read, Eq)
instance C'.Decerialize Call'sendResultsTo where
    type Cerial msg Call'sendResultsTo = Capnp.ById.Xb312981b2552a250.Call'sendResultsTo msg
    decerialize raw = do
        raw <- Capnp.ById.Xb312981b2552a250.get_Call'sendResultsTo' raw
        case raw of
            Capnp.ById.Xb312981b2552a250.Call'sendResultsTo'caller -> pure Call'sendResultsTo'caller
            Capnp.ById.Xb312981b2552a250.Call'sendResultsTo'yourself -> pure Call'sendResultsTo'yourself
            Capnp.ById.Xb312981b2552a250.Call'sendResultsTo'thirdParty val -> Call'sendResultsTo'thirdParty <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Call'sendResultsTo'unknown' val -> pure (Call'sendResultsTo'unknown' val)
instance C'.FromStruct M'.ConstMsg Call'sendResultsTo where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Call'sendResultsTo M'.ConstMsg)
instance C'.Marshal Call'sendResultsTo where
    marshalInto raw value = do
        case value of
            Call'sendResultsTo'caller -> Capnp.ById.Xb312981b2552a250.set_Call'sendResultsTo'caller raw
            Call'sendResultsTo'yourself -> Capnp.ById.Xb312981b2552a250.set_Call'sendResultsTo'yourself raw
            Call'sendResultsTo'thirdParty arg_ -> do
                field_ <- C'.cerialize (U'.message raw) arg_
                Capnp.ById.Xb312981b2552a250.set_Call'sendResultsTo'thirdParty raw field_
            Call'sendResultsTo'unknown' arg_ -> Capnp.ById.Xb312981b2552a250.set_Call'sendResultsTo'unknown' raw arg_
instance C'.Cerialize s Call'sendResultsTo
data Disembargo'context
     = Disembargo'context'senderLoopback (Word32) |
    Disembargo'context'receiverLoopback (Word32) |
    Disembargo'context'accept |
    Disembargo'context'provide (Word32) |
    Disembargo'context'unknown' (Word16)
    deriving(Show, Read, Eq)
instance C'.Decerialize Disembargo'context where
    type Cerial msg Disembargo'context = Capnp.ById.Xb312981b2552a250.Disembargo'context msg
    decerialize raw = do
        raw <- Capnp.ById.Xb312981b2552a250.get_Disembargo'context' raw
        case raw of
            Capnp.ById.Xb312981b2552a250.Disembargo'context'senderLoopback val -> pure (Disembargo'context'senderLoopback val)
            Capnp.ById.Xb312981b2552a250.Disembargo'context'receiverLoopback val -> pure (Disembargo'context'receiverLoopback val)
            Capnp.ById.Xb312981b2552a250.Disembargo'context'accept -> pure Disembargo'context'accept
            Capnp.ById.Xb312981b2552a250.Disembargo'context'provide val -> pure (Disembargo'context'provide val)
            Capnp.ById.Xb312981b2552a250.Disembargo'context'unknown' val -> pure (Disembargo'context'unknown' val)
instance C'.FromStruct M'.ConstMsg Disembargo'context where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Disembargo'context M'.ConstMsg)
instance C'.Marshal Disembargo'context where
    marshalInto raw value = do
        case value of
            Disembargo'context'senderLoopback arg_ -> Capnp.ById.Xb312981b2552a250.set_Disembargo'context'senderLoopback raw arg_
            Disembargo'context'receiverLoopback arg_ -> Capnp.ById.Xb312981b2552a250.set_Disembargo'context'receiverLoopback raw arg_
            Disembargo'context'accept -> Capnp.ById.Xb312981b2552a250.set_Disembargo'context'accept raw
            Disembargo'context'provide arg_ -> Capnp.ById.Xb312981b2552a250.set_Disembargo'context'provide raw arg_
            Disembargo'context'unknown' arg_ -> Capnp.ById.Xb312981b2552a250.set_Disembargo'context'unknown' raw arg_
instance C'.Cerialize s Disembargo'context
data PromisedAnswer'Op
     = PromisedAnswer'Op'noop |
    PromisedAnswer'Op'getPointerField (Word16) |
    PromisedAnswer'Op'unknown' (Word16)
    deriving(Show, Read, Eq)
instance C'.Decerialize PromisedAnswer'Op where
    type Cerial msg PromisedAnswer'Op = Capnp.ById.Xb312981b2552a250.PromisedAnswer'Op msg
    decerialize raw = do
        raw <- Capnp.ById.Xb312981b2552a250.get_PromisedAnswer'Op' raw
        case raw of
            Capnp.ById.Xb312981b2552a250.PromisedAnswer'Op'noop -> pure PromisedAnswer'Op'noop
            Capnp.ById.Xb312981b2552a250.PromisedAnswer'Op'getPointerField val -> pure (PromisedAnswer'Op'getPointerField val)
            Capnp.ById.Xb312981b2552a250.PromisedAnswer'Op'unknown' val -> pure (PromisedAnswer'Op'unknown' val)
instance C'.FromStruct M'.ConstMsg PromisedAnswer'Op where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.PromisedAnswer'Op M'.ConstMsg)
instance C'.Marshal PromisedAnswer'Op where
    marshalInto raw value = do
        case value of
            PromisedAnswer'Op'noop -> Capnp.ById.Xb312981b2552a250.set_PromisedAnswer'Op'noop raw
            PromisedAnswer'Op'getPointerField arg_ -> Capnp.ById.Xb312981b2552a250.set_PromisedAnswer'Op'getPointerField raw arg_
            PromisedAnswer'Op'unknown' arg_ -> Capnp.ById.Xb312981b2552a250.set_PromisedAnswer'Op'unknown' raw arg_
instance C'.Cerialize s PromisedAnswer'Op
data Resolve'
     = Resolve'cap (CapDescriptor) |
    Resolve'exception (Exception) |
    Resolve'unknown' (Word16)
    deriving(Show, Read, Eq)
instance C'.Decerialize Resolve' where
    type Cerial msg Resolve' = Capnp.ById.Xb312981b2552a250.Resolve' msg
    decerialize raw = do
        raw <- Capnp.ById.Xb312981b2552a250.get_Resolve'' raw
        case raw of
            Capnp.ById.Xb312981b2552a250.Resolve'cap val -> Resolve'cap <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Resolve'exception val -> Resolve'exception <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Resolve'unknown' val -> pure (Resolve'unknown' val)
instance C'.FromStruct M'.ConstMsg Resolve' where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Resolve' M'.ConstMsg)
instance C'.Marshal Resolve' where
    marshalInto raw value = do
        case value of
            Resolve'cap arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Resolve'cap raw
                C'.marshalInto field_ arg_
            Resolve'exception arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Resolve'exception raw
                C'.marshalInto field_ arg_
            Resolve'unknown' arg_ -> Capnp.ById.Xb312981b2552a250.set_Resolve'unknown' raw arg_
instance C'.Cerialize s Resolve'
data Return'
     = Return'results (Payload) |
    Return'exception (Exception) |
    Return'canceled |
    Return'resultsSentElsewhere |
    Return'takeFromOtherQuestion (Word32) |
    Return'acceptFromThirdParty (Maybe (PU'.PtrType)) |
    Return'unknown' (Word16)
    deriving(Show, Read, Eq)
instance C'.Decerialize Return' where
    type Cerial msg Return' = Capnp.ById.Xb312981b2552a250.Return' msg
    decerialize raw = do
        raw <- Capnp.ById.Xb312981b2552a250.get_Return'' raw
        case raw of
            Capnp.ById.Xb312981b2552a250.Return'results val -> Return'results <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Return'exception val -> Return'exception <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Return'canceled -> pure Return'canceled
            Capnp.ById.Xb312981b2552a250.Return'resultsSentElsewhere -> pure Return'resultsSentElsewhere
            Capnp.ById.Xb312981b2552a250.Return'takeFromOtherQuestion val -> pure (Return'takeFromOtherQuestion val)
            Capnp.ById.Xb312981b2552a250.Return'acceptFromThirdParty val -> Return'acceptFromThirdParty <$> C'.decerialize val
            Capnp.ById.Xb312981b2552a250.Return'unknown' val -> pure (Return'unknown' val)
instance C'.FromStruct M'.ConstMsg Return' where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Return' M'.ConstMsg)
instance C'.Marshal Return' where
    marshalInto raw value = do
        case value of
            Return'results arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Return'results raw
                C'.marshalInto field_ arg_
            Return'exception arg_ -> do
                field_ <- Capnp.ById.Xb312981b2552a250.new_Return'exception raw
                C'.marshalInto field_ arg_
            Return'canceled -> Capnp.ById.Xb312981b2552a250.set_Return'canceled raw
            Return'resultsSentElsewhere -> Capnp.ById.Xb312981b2552a250.set_Return'resultsSentElsewhere raw
            Return'takeFromOtherQuestion arg_ -> Capnp.ById.Xb312981b2552a250.set_Return'takeFromOtherQuestion raw arg_
            Return'acceptFromThirdParty arg_ -> do
                field_ <- C'.cerialize (U'.message raw) arg_
                Capnp.ById.Xb312981b2552a250.set_Return'acceptFromThirdParty raw field_
            Return'unknown' arg_ -> Capnp.ById.Xb312981b2552a250.set_Return'unknown' raw arg_
instance C'.Cerialize s Return'