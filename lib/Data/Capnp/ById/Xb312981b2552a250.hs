{-# OPTIONS_GHC -Wno-unused-imports #-}
module Data.Capnp.ById.Xb312981b2552a250 where

-- Code generated by capnpc-haskell. DO NOT EDIT.
-- Generated from schema file: /usr/include/capnp/rpc.capnp

import Data.Int
import Data.Word
import qualified Data.Bits

import qualified Codec.Capnp
import qualified Data.Capnp.BuiltinTypes
import qualified Data.Capnp.TraversalLimit
import qualified Data.Capnp.Untyped

import qualified Data.Capnp.ById.Xbdf87d7bb8304e81

newtype Call b = Call (Data.Capnp.Untyped.Struct b)

get_Call'questionId :: Data.Capnp.Untyped.ReadCtx m b => Call b -> m Word32
get_Call'questionId (Call struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Call'target :: Data.Capnp.Untyped.ReadCtx m b => Call b -> m (MessageTarget b)
get_Call'target (Call struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

get_Call'interfaceId :: Data.Capnp.Untyped.ReadCtx m b => Call b -> m Word64
get_Call'interfaceId (Call struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 1 struct)

get_Call'methodId :: Data.Capnp.Untyped.ReadCtx m b => Call b -> m Word16
get_Call'methodId (Call struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 32)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Call'params :: Data.Capnp.Untyped.ReadCtx m b => Call b -> m (Payload b)
get_Call'params (Call struct) =
    Data.Capnp.Untyped.getPtr 1 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

get_Call'sendResultsTo :: Data.Capnp.Untyped.ReadCtx m b => Call b -> m (Call'sendResultsTo b)
get_Call'sendResultsTo (Call struct) = undefined -- TODO: handle groups/anonymous union fields
get_Call'allowThirdPartyTailCall :: Data.Capnp.Untyped.ReadCtx m b => Call b -> m Bool
get_Call'allowThirdPartyTailCall (Call struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 2 struct)

data CapDescriptor b
    = CapDescriptor'none
    | CapDescriptor'senderHosted Word32
    | CapDescriptor'senderPromise Word32
    | CapDescriptor'receiverHosted Word32
    | CapDescriptor'receiverAnswer (PromisedAnswer b)
    | CapDescriptor'thirdPartyHosted (ThirdPartyCapDescriptor b)
    | CapDescriptor'unknown' Word16







data Message b
    = Message'unimplemented (Message b)
    | Message'abort (Exception b)
    | Message'call (Call b)
    | Message'return (Return b)
    | Message'finish (Finish b)
    | Message'resolve (Resolve b)
    | Message'release (Release b)
    | Message'obsoleteSave (Maybe (Data.Capnp.Untyped.Ptr b))
    | Message'bootstrap (Bootstrap b)
    | Message'obsoleteDelete (Maybe (Data.Capnp.Untyped.Ptr b))
    | Message'provide (Provide b)
    | Message'accept (Accept b)
    | Message'join (Join b)
    | Message'disembargo (Disembargo b)
    | Message'unknown' Word16















data MessageTarget b
    = MessageTarget'importedCap Word32
    | MessageTarget'promisedAnswer (PromisedAnswer b)
    | MessageTarget'unknown' Word16



newtype Payload b = Payload (Data.Capnp.Untyped.Struct b)

get_Payload'content :: Data.Capnp.Untyped.ReadCtx m b => Payload b -> m (Maybe (Data.Capnp.Untyped.Ptr b))
get_Payload'content (Payload struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

get_Payload'capTable :: Data.Capnp.Untyped.ReadCtx m b => Payload b -> m (Data.Capnp.Untyped.ListOf b (CapDescriptor b))
get_Payload'capTable (Payload struct) =
    Data.Capnp.Untyped.getPtr 1 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

newtype Provide b = Provide (Data.Capnp.Untyped.Struct b)

get_Provide'questionId :: Data.Capnp.Untyped.ReadCtx m b => Provide b -> m Word32
get_Provide'questionId (Provide struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Provide'target :: Data.Capnp.Untyped.ReadCtx m b => Provide b -> m (MessageTarget b)
get_Provide'target (Provide struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

get_Provide'recipient :: Data.Capnp.Untyped.ReadCtx m b => Provide b -> m (Maybe (Data.Capnp.Untyped.Ptr b))
get_Provide'recipient (Provide struct) =
    Data.Capnp.Untyped.getPtr 1 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

newtype Return b = Return (Data.Capnp.Untyped.Struct b)

get_Return''answerId :: Data.Capnp.Untyped.ReadCtx m b => Return b -> m Word32
get_Return''answerId (Return struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Return''releaseParamCaps :: Data.Capnp.Untyped.ReadCtx m b => Return b -> m Bool
get_Return''releaseParamCaps (Return struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 1
    . (`Data.Bits.shiftR` 32)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Return''union' :: Data.Capnp.Untyped.ReadCtx m b => Return b -> m (Return' b)
get_Return''union' (Return struct) = undefined -- TODO: handle groups/anonymous union fields
data Return' b
    = Return'results (Payload b)
    | Return'exception (Exception b)
    | Return'canceled
    | Return'resultsSentElsewhere
    | Return'takeFromOtherQuestion Word32
    | Return'acceptFromThirdParty (Maybe (Data.Capnp.Untyped.Ptr b))
    | Return'unknown' Word16







newtype Release b = Release (Data.Capnp.Untyped.Struct b)

get_Release'id :: Data.Capnp.Untyped.ReadCtx m b => Release b -> m Word32
get_Release'id (Release struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Release'referenceCount :: Data.Capnp.Untyped.ReadCtx m b => Release b -> m Word32
get_Release'referenceCount (Release struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 32)
    )
    (Data.Capnp.Untyped.getData 0 struct)

data Exception'Type b
    = Exception'Type'failed
    | Exception'Type'overloaded
    | Exception'Type'disconnected
    | Exception'Type'unimplemented
    | Exception'Type'unknown' Word16
instance Enum (Exception'Type b) where
    toEnum = Codec.Capnp.fromWord . fromIntegral
    fromEnum = fromIntegral . Codec.Capnp.toWord


instance Codec.Capnp.IsWord (Exception'Type b) where
    fromWord 3 = Exception'Type'unimplemented
    fromWord 2 = Exception'Type'disconnected
    fromWord 1 = Exception'Type'overloaded
    fromWord 0 = Exception'Type'failed
    fromWord tag = Exception'Type'unknown' (fromIntegral tag)
    toWord Exception'Type'unimplemented = 3
    toWord Exception'Type'disconnected = 2
    toWord Exception'Type'overloaded = 1
    toWord Exception'Type'failed = 0
    toWord (Exception'Type'unknown' tag) = fromIntegral tag

newtype Resolve b = Resolve (Data.Capnp.Untyped.Struct b)

get_Resolve''promiseId :: Data.Capnp.Untyped.ReadCtx m b => Resolve b -> m Word32
get_Resolve''promiseId (Resolve struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Resolve''union' :: Data.Capnp.Untyped.ReadCtx m b => Resolve b -> m (Resolve' b)
get_Resolve''union' (Resolve struct) = undefined -- TODO: handle groups/anonymous union fields
data Resolve' b
    = Resolve'cap (CapDescriptor b)
    | Resolve'exception (Exception b)
    | Resolve'unknown' Word16



newtype ThirdPartyCapDescriptor b = ThirdPartyCapDescriptor (Data.Capnp.Untyped.Struct b)

get_ThirdPartyCapDescriptor'id :: Data.Capnp.Untyped.ReadCtx m b => ThirdPartyCapDescriptor b -> m (Maybe (Data.Capnp.Untyped.Ptr b))
get_ThirdPartyCapDescriptor'id (ThirdPartyCapDescriptor struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

get_ThirdPartyCapDescriptor'vineId :: Data.Capnp.Untyped.ReadCtx m b => ThirdPartyCapDescriptor b -> m Word32
get_ThirdPartyCapDescriptor'vineId (ThirdPartyCapDescriptor struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

newtype Finish b = Finish (Data.Capnp.Untyped.Struct b)

get_Finish'questionId :: Data.Capnp.Untyped.ReadCtx m b => Finish b -> m Word32
get_Finish'questionId (Finish struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Finish'releaseResultCaps :: Data.Capnp.Untyped.ReadCtx m b => Finish b -> m Bool
get_Finish'releaseResultCaps (Finish struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 1
    . (`Data.Bits.shiftR` 32)
    )
    (Data.Capnp.Untyped.getData 0 struct)

newtype Accept b = Accept (Data.Capnp.Untyped.Struct b)

get_Accept'questionId :: Data.Capnp.Untyped.ReadCtx m b => Accept b -> m Word32
get_Accept'questionId (Accept struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Accept'provision :: Data.Capnp.Untyped.ReadCtx m b => Accept b -> m (Maybe (Data.Capnp.Untyped.Ptr b))
get_Accept'provision (Accept struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

get_Accept'embargo :: Data.Capnp.Untyped.ReadCtx m b => Accept b -> m Bool
get_Accept'embargo (Accept struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 32)
    )
    (Data.Capnp.Untyped.getData 0 struct)

data Disembargo'context b
    = Disembargo'context'senderLoopback Word32
    | Disembargo'context'receiverLoopback Word32
    | Disembargo'context'accept
    | Disembargo'context'provide Word32
    | Disembargo'context'unknown' Word16





newtype Exception b = Exception (Data.Capnp.Untyped.Struct b)

get_Exception'reason :: Data.Capnp.Untyped.ReadCtx m b => Exception b -> m (Data.Capnp.BuiltinTypes.Text b)
get_Exception'reason (Exception struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

get_Exception'obsoleteIsCallersFault :: Data.Capnp.Untyped.ReadCtx m b => Exception b -> m Bool
get_Exception'obsoleteIsCallersFault (Exception struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Exception'obsoleteDurability :: Data.Capnp.Untyped.ReadCtx m b => Exception b -> m Word16
get_Exception'obsoleteDurability (Exception struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 16)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Exception'type_ :: Data.Capnp.Untyped.ReadCtx m b => Exception b -> m (Exception'Type b)
get_Exception'type_ (Exception struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 32)
    )
    (Data.Capnp.Untyped.getData 0 struct)

newtype PromisedAnswer b = PromisedAnswer (Data.Capnp.Untyped.Struct b)

get_PromisedAnswer'questionId :: Data.Capnp.Untyped.ReadCtx m b => PromisedAnswer b -> m Word32
get_PromisedAnswer'questionId (PromisedAnswer struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_PromisedAnswer'transform :: Data.Capnp.Untyped.ReadCtx m b => PromisedAnswer b -> m (Data.Capnp.Untyped.ListOf b (PromisedAnswer'Op b))
get_PromisedAnswer'transform (PromisedAnswer struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

data Call'sendResultsTo b
    = Call'sendResultsTo'caller
    | Call'sendResultsTo'yourself
    | Call'sendResultsTo'thirdParty (Maybe (Data.Capnp.Untyped.Ptr b))
    | Call'sendResultsTo'unknown' Word16




newtype Bootstrap b = Bootstrap (Data.Capnp.Untyped.Struct b)

get_Bootstrap'questionId :: Data.Capnp.Untyped.ReadCtx m b => Bootstrap b -> m Word32
get_Bootstrap'questionId (Bootstrap struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Bootstrap'deprecatedObjectId :: Data.Capnp.Untyped.ReadCtx m b => Bootstrap b -> m (Maybe (Data.Capnp.Untyped.Ptr b))
get_Bootstrap'deprecatedObjectId (Bootstrap struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

data PromisedAnswer'Op b
    = PromisedAnswer'Op'noop
    | PromisedAnswer'Op'getPointerField Word16
    | PromisedAnswer'Op'unknown' Word16



newtype Disembargo b = Disembargo (Data.Capnp.Untyped.Struct b)

get_Disembargo'target :: Data.Capnp.Untyped.ReadCtx m b => Disembargo b -> m (MessageTarget b)
get_Disembargo'target (Disembargo struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

get_Disembargo'context :: Data.Capnp.Untyped.ReadCtx m b => Disembargo b -> m (Disembargo'context b)
get_Disembargo'context (Disembargo struct) = undefined -- TODO: handle groups/anonymous union fields
newtype Join b = Join (Data.Capnp.Untyped.Struct b)

get_Join'questionId :: Data.Capnp.Untyped.ReadCtx m b => Join b -> m Word32
get_Join'questionId (Join struct) = fmap
    ( Codec.Capnp.fromWord
    . Data.Bits.xor 0
    . (`Data.Bits.shiftR` 0)
    )
    (Data.Capnp.Untyped.getData 0 struct)

get_Join'target :: Data.Capnp.Untyped.ReadCtx m b => Join b -> m (MessageTarget b)
get_Join'target (Join struct) =
    Data.Capnp.Untyped.getPtr 0 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)

get_Join'keyPart :: Data.Capnp.Untyped.ReadCtx m b => Join b -> m (Maybe (Data.Capnp.Untyped.Ptr b))
get_Join'keyPart (Join struct) =
    Data.Capnp.Untyped.getPtr 1 struct
    >>= Codec.Capnp.fromPtr (Data.Capnp.Untyped.message struct)
