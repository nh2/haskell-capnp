{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Capnp.Capnp.Rpc where

-- Code generated by capnpc-haskell. DO NOT EDIT.
-- Generated from schema file: capnp/rpc.capnp

import Data.Int
import Data.Word

import Data.Capnp.Untyped.Pure (List)
import Data.Capnp.BuiltinTypes.Pure (Data, Text)
import Control.Monad.Catch (MonadThrow)
import Data.Capnp.TraversalLimit (MonadLimit)

import qualified Data.Capnp.Message
import qualified Data.Capnp.Untyped.Pure
import qualified Data.Capnp.Untyped
import qualified Codec.Capnp

import qualified Capnp.ById.Xb312981b2552a250
import qualified Capnp.ById.Xbdf87d7bb8304e81.Pure
import qualified Capnp.ById.Xbdf87d7bb8304e81

data Call
    = Call
        { questionId :: Word32
        , target :: MessageTarget
        , interfaceId :: Word64
        , methodId :: Word16
        , params :: Payload
        , sendResultsTo :: Call'sendResultsTo
        , allowThirdPartyTailCall :: Bool
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Call msg) Call where
    decerialize raw = Call
            <$> (Capnp.ById.Xb312981b2552a250.get_Call'questionId raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Call'target raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Call'interfaceId raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Call'methodId raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Call'params raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Call'sendResultsTo raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Call'allowThirdPartyTailCall raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Call where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Call Data.Capnp.Message.Message)

data CapDescriptor
    = CapDescriptor'none
    | CapDescriptor'senderHosted (Word32)
    | CapDescriptor'senderPromise (Word32)
    | CapDescriptor'receiverHosted (Word32)
    | CapDescriptor'receiverAnswer (PromisedAnswer)
    | CapDescriptor'thirdPartyHosted (ThirdPartyCapDescriptor)
    | CapDescriptor'unknown' (Word16)
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.CapDescriptor msg) CapDescriptor where
    decerialize raw = case raw of

        Capnp.ById.Xb312981b2552a250.CapDescriptor'none -> pure CapDescriptor'none
        Capnp.ById.Xb312981b2552a250.CapDescriptor'senderHosted val -> CapDescriptor'senderHosted <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.CapDescriptor'senderPromise val -> CapDescriptor'senderPromise <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.CapDescriptor'receiverHosted val -> CapDescriptor'receiverHosted <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.CapDescriptor'receiverAnswer val -> CapDescriptor'receiverAnswer <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.CapDescriptor'thirdPartyHosted val -> CapDescriptor'thirdPartyHosted <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.CapDescriptor'unknown' val -> CapDescriptor'unknown' <$> Codec.Capnp.decerialize val

instance Codec.Capnp.IsStruct CapDescriptor where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.CapDescriptor Data.Capnp.Message.Message)

data Message
    = Message'unimplemented (Message)
    | Message'abort (Exception)
    | Message'call (Call)
    | Message'return (Return)
    | Message'finish (Finish)
    | Message'resolve (Resolve)
    | Message'release (Release)
    | Message'obsoleteSave (Maybe (Data.Capnp.Untyped.Pure.PtrType))
    | Message'bootstrap (Bootstrap)
    | Message'obsoleteDelete (Maybe (Data.Capnp.Untyped.Pure.PtrType))
    | Message'provide (Provide)
    | Message'accept (Accept)
    | Message'join (Join)
    | Message'disembargo (Disembargo)
    | Message'unknown' (Word16)
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Message msg) Message where
    decerialize raw = case raw of

        Capnp.ById.Xb312981b2552a250.Message'unimplemented val -> Message'unimplemented <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'abort val -> Message'abort <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'call val -> Message'call <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'return val -> Message'return <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'finish val -> Message'finish <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'resolve val -> Message'resolve <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'release val -> Message'release <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'obsoleteSave val -> Message'obsoleteSave <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'bootstrap val -> Message'bootstrap <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'obsoleteDelete val -> Message'obsoleteDelete <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'provide val -> Message'provide <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'accept val -> Message'accept <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'join val -> Message'join <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'disembargo val -> Message'disembargo <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Message'unknown' val -> Message'unknown' <$> Codec.Capnp.decerialize val

instance Codec.Capnp.IsStruct Message where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Message Data.Capnp.Message.Message)

data MessageTarget
    = MessageTarget'importedCap (Word32)
    | MessageTarget'promisedAnswer (PromisedAnswer)
    | MessageTarget'unknown' (Word16)
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.MessageTarget msg) MessageTarget where
    decerialize raw = case raw of

        Capnp.ById.Xb312981b2552a250.MessageTarget'importedCap val -> MessageTarget'importedCap <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.MessageTarget'promisedAnswer val -> MessageTarget'promisedAnswer <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.MessageTarget'unknown' val -> MessageTarget'unknown' <$> Codec.Capnp.decerialize val

instance Codec.Capnp.IsStruct MessageTarget where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.MessageTarget Data.Capnp.Message.Message)

data Payload
    = Payload
        { content :: Maybe (Data.Capnp.Untyped.Pure.PtrType)
        , capTable :: List (CapDescriptor)
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Payload msg) Payload where
    decerialize raw = Payload
            <$> (Capnp.ById.Xb312981b2552a250.get_Payload'content raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Payload'capTable raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Payload where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Payload Data.Capnp.Message.Message)

data Provide
    = Provide
        { questionId :: Word32
        , target :: MessageTarget
        , recipient :: Maybe (Data.Capnp.Untyped.Pure.PtrType)
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Provide msg) Provide where
    decerialize raw = Provide
            <$> (Capnp.ById.Xb312981b2552a250.get_Provide'questionId raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Provide'target raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Provide'recipient raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Provide where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Provide Data.Capnp.Message.Message)

data Return
    = Return'
        { answerId :: Word32
        , releaseParamCaps :: Bool
        , union' :: Return'
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Return msg) Return where
    decerialize raw = Return'
            <$> (Capnp.ById.Xb312981b2552a250.get_Return''answerId raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Return''releaseParamCaps raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Return''union' raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Return where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Return Data.Capnp.Message.Message)

data Return'
    = Return'results (Payload)
    | Return'exception (Exception)
    | Return'canceled
    | Return'resultsSentElsewhere
    | Return'takeFromOtherQuestion (Word32)
    | Return'acceptFromThirdParty (Maybe (Data.Capnp.Untyped.Pure.PtrType))
    | Return'unknown' (Word16)
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Return' msg) Return' where
    decerialize raw = case raw of

        Capnp.ById.Xb312981b2552a250.Return'results val -> Return'results <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Return'exception val -> Return'exception <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Return'canceled -> pure Return'canceled
        Capnp.ById.Xb312981b2552a250.Return'resultsSentElsewhere -> pure Return'resultsSentElsewhere
        Capnp.ById.Xb312981b2552a250.Return'takeFromOtherQuestion val -> Return'takeFromOtherQuestion <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Return'acceptFromThirdParty val -> Return'acceptFromThirdParty <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Return'unknown' val -> Return'unknown' <$> Codec.Capnp.decerialize val

instance Codec.Capnp.IsStruct Return' where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Return' Data.Capnp.Message.Message)

data Release
    = Release
        { id :: Word32
        , referenceCount :: Word32
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Release msg) Release where
    decerialize raw = Release
            <$> (Capnp.ById.Xb312981b2552a250.get_Release'id raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Release'referenceCount raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Release where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Release Data.Capnp.Message.Message)

data Exception'Type
    = Exception'Type'failed
    | Exception'Type'overloaded
    | Exception'Type'disconnected
    | Exception'Type'unimplemented
    | Exception'Type'unknown' (Word16)
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize Capnp.ById.Xb312981b2552a250.Exception'Type Exception'Type where
    decerialize raw = case raw of

        Capnp.ById.Xb312981b2552a250.Exception'Type'failed -> pure Exception'Type'failed
        Capnp.ById.Xb312981b2552a250.Exception'Type'overloaded -> pure Exception'Type'overloaded
        Capnp.ById.Xb312981b2552a250.Exception'Type'disconnected -> pure Exception'Type'disconnected
        Capnp.ById.Xb312981b2552a250.Exception'Type'unimplemented -> pure Exception'Type'unimplemented
        Capnp.ById.Xb312981b2552a250.Exception'Type'unknown' val -> Exception'Type'unknown' <$> Codec.Capnp.decerialize val

data Resolve
    = Resolve'
        { promiseId :: Word32
        , union' :: Resolve'
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Resolve msg) Resolve where
    decerialize raw = Resolve'
            <$> (Capnp.ById.Xb312981b2552a250.get_Resolve''promiseId raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Resolve''union' raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Resolve where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Resolve Data.Capnp.Message.Message)

data Resolve'
    = Resolve'cap (CapDescriptor)
    | Resolve'exception (Exception)
    | Resolve'unknown' (Word16)
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Resolve' msg) Resolve' where
    decerialize raw = case raw of

        Capnp.ById.Xb312981b2552a250.Resolve'cap val -> Resolve'cap <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Resolve'exception val -> Resolve'exception <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Resolve'unknown' val -> Resolve'unknown' <$> Codec.Capnp.decerialize val

instance Codec.Capnp.IsStruct Resolve' where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Resolve' Data.Capnp.Message.Message)

data ThirdPartyCapDescriptor
    = ThirdPartyCapDescriptor
        { id :: Maybe (Data.Capnp.Untyped.Pure.PtrType)
        , vineId :: Word32
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.ThirdPartyCapDescriptor msg) ThirdPartyCapDescriptor where
    decerialize raw = ThirdPartyCapDescriptor
            <$> (Capnp.ById.Xb312981b2552a250.get_ThirdPartyCapDescriptor'id raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_ThirdPartyCapDescriptor'vineId raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct ThirdPartyCapDescriptor where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.ThirdPartyCapDescriptor Data.Capnp.Message.Message)

data Finish
    = Finish
        { questionId :: Word32
        , releaseResultCaps :: Bool
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Finish msg) Finish where
    decerialize raw = Finish
            <$> (Capnp.ById.Xb312981b2552a250.get_Finish'questionId raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Finish'releaseResultCaps raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Finish where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Finish Data.Capnp.Message.Message)

data Accept
    = Accept
        { questionId :: Word32
        , provision :: Maybe (Data.Capnp.Untyped.Pure.PtrType)
        , embargo :: Bool
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Accept msg) Accept where
    decerialize raw = Accept
            <$> (Capnp.ById.Xb312981b2552a250.get_Accept'questionId raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Accept'provision raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Accept'embargo raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Accept where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Accept Data.Capnp.Message.Message)

data Disembargo'context
    = Disembargo'context'senderLoopback (Word32)
    | Disembargo'context'receiverLoopback (Word32)
    | Disembargo'context'accept
    | Disembargo'context'provide (Word32)
    | Disembargo'context'unknown' (Word16)
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Disembargo'context msg) Disembargo'context where
    decerialize raw = case raw of

        Capnp.ById.Xb312981b2552a250.Disembargo'context'senderLoopback val -> Disembargo'context'senderLoopback <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Disembargo'context'receiverLoopback val -> Disembargo'context'receiverLoopback <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Disembargo'context'accept -> pure Disembargo'context'accept
        Capnp.ById.Xb312981b2552a250.Disembargo'context'provide val -> Disembargo'context'provide <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Disembargo'context'unknown' val -> Disembargo'context'unknown' <$> Codec.Capnp.decerialize val

instance Codec.Capnp.IsStruct Disembargo'context where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Disembargo'context Data.Capnp.Message.Message)

data Exception
    = Exception
        { reason :: Text
        , obsoleteIsCallersFault :: Bool
        , obsoleteDurability :: Word16
        , type_ :: Exception'Type
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Exception msg) Exception where
    decerialize raw = Exception
            <$> (Capnp.ById.Xb312981b2552a250.get_Exception'reason raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Exception'obsoleteIsCallersFault raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Exception'obsoleteDurability raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Exception'type_ raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Exception where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Exception Data.Capnp.Message.Message)

data PromisedAnswer
    = PromisedAnswer
        { questionId :: Word32
        , transform :: List (PromisedAnswer'Op)
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.PromisedAnswer msg) PromisedAnswer where
    decerialize raw = PromisedAnswer
            <$> (Capnp.ById.Xb312981b2552a250.get_PromisedAnswer'questionId raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_PromisedAnswer'transform raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct PromisedAnswer where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.PromisedAnswer Data.Capnp.Message.Message)

data Call'sendResultsTo
    = Call'sendResultsTo'caller
    | Call'sendResultsTo'yourself
    | Call'sendResultsTo'thirdParty (Maybe (Data.Capnp.Untyped.Pure.PtrType))
    | Call'sendResultsTo'unknown' (Word16)
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Call'sendResultsTo msg) Call'sendResultsTo where
    decerialize raw = case raw of

        Capnp.ById.Xb312981b2552a250.Call'sendResultsTo'caller -> pure Call'sendResultsTo'caller
        Capnp.ById.Xb312981b2552a250.Call'sendResultsTo'yourself -> pure Call'sendResultsTo'yourself
        Capnp.ById.Xb312981b2552a250.Call'sendResultsTo'thirdParty val -> Call'sendResultsTo'thirdParty <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.Call'sendResultsTo'unknown' val -> Call'sendResultsTo'unknown' <$> Codec.Capnp.decerialize val

instance Codec.Capnp.IsStruct Call'sendResultsTo where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Call'sendResultsTo Data.Capnp.Message.Message)

data Bootstrap
    = Bootstrap
        { questionId :: Word32
        , deprecatedObjectId :: Maybe (Data.Capnp.Untyped.Pure.PtrType)
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Bootstrap msg) Bootstrap where
    decerialize raw = Bootstrap
            <$> (Capnp.ById.Xb312981b2552a250.get_Bootstrap'questionId raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Bootstrap'deprecatedObjectId raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Bootstrap where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Bootstrap Data.Capnp.Message.Message)

data PromisedAnswer'Op
    = PromisedAnswer'Op'noop
    | PromisedAnswer'Op'getPointerField (Word16)
    | PromisedAnswer'Op'unknown' (Word16)
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.PromisedAnswer'Op msg) PromisedAnswer'Op where
    decerialize raw = case raw of

        Capnp.ById.Xb312981b2552a250.PromisedAnswer'Op'noop -> pure PromisedAnswer'Op'noop
        Capnp.ById.Xb312981b2552a250.PromisedAnswer'Op'getPointerField val -> PromisedAnswer'Op'getPointerField <$> Codec.Capnp.decerialize val
        Capnp.ById.Xb312981b2552a250.PromisedAnswer'Op'unknown' val -> PromisedAnswer'Op'unknown' <$> Codec.Capnp.decerialize val

instance Codec.Capnp.IsStruct PromisedAnswer'Op where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.PromisedAnswer'Op Data.Capnp.Message.Message)

data Disembargo
    = Disembargo
        { target :: MessageTarget
        , context :: Disembargo'context
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Disembargo msg) Disembargo where
    decerialize raw = Disembargo
            <$> (Capnp.ById.Xb312981b2552a250.get_Disembargo'target raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Disembargo'context raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Disembargo where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Disembargo Data.Capnp.Message.Message)

data Join
    = Join
        { questionId :: Word32
        , target :: MessageTarget
        , keyPart :: Maybe (Data.Capnp.Untyped.Pure.PtrType)
        }
    deriving(Show, Read, Eq)

instance Codec.Capnp.Decerialize (Capnp.ById.Xb312981b2552a250.Join msg) Join where
    decerialize raw = Join
            <$> (Capnp.ById.Xb312981b2552a250.get_Join'questionId raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Join'target raw >>= Codec.Capnp.decerialize)
            <*> (Capnp.ById.Xb312981b2552a250.get_Join'keyPart raw >>= Codec.Capnp.decerialize)

instance Codec.Capnp.IsStruct Join where
    fromStruct struct = do
        raw <- Codec.Capnp.fromStruct struct
        Codec.Capnp.decerialize (raw :: Capnp.ById.Xb312981b2552a250.Join Data.Capnp.Message.Message)

