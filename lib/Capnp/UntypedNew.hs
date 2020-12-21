{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DuplicateRecordFields  #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE StrictData             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
-- Temporary, while stuff settles:
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Capnp.UntypedNew
    ( DataSz(..)
    , Repr(..)
    , ListRepr(..)
    , PtrRepr(..)
    , UntypedRaw
    , HasRepr
    , HasField
    , FieldLoc(..)
    , DataFieldLoc(..)
    , Field(..)
    , IsStruct
    , Untyped
    , AnyStruct
    , AnyPointer
    , AnyList
    , Capability
    , ReadCtx
    , RWCtx

    , get
    , getClient
    ) where

import Data.Int
import Data.Word

import Control.Monad.Catch  (MonadCatch, MonadThrow(throwM))
import GHC.OverloadedLabels (IsLabel)

import           Capnp.Address
    (OffsetError (..), WordAddr (..), pointerFrom)
import           Capnp.Bits           (WordCount)
import qualified Capnp.Errors         as E
import           Capnp.Message
    (Message, Mutability (..), Segment, WordPtr)
import qualified Capnp.Message        as M
import qualified Capnp.Pointer        as P
import           Capnp.TraversalLimit (MonadLimit(invoice))

-- | Type (constraint) synonym for the constraints needed for most read
-- operations.
type ReadCtx m mut = (M.MonadReadMessage mut m, MonadThrow m, MonadLimit m)

-- | Synonym for ReadCtx + WriteCtx
type RWCtx m s = (ReadCtx m ('Mut s), M.WriteCtx m s)

data DataSz = Sz0  | Sz1 | Sz8 | Sz16 | Sz32 | Sz64

data SSz (a :: DataSz) where
    Ssz0 :: SSz 'Sz0
    Ssz1 :: SSz 'Sz1
    Ssz8 :: SSz 'Sz8
    Ssz16 :: SSz 'Sz16
    Ssz32 :: SSz 'Sz32
    Ssz64 :: SSz 'Sz64

szBits :: SSz a -> Int
szBits Ssz0  = 0
szBits Ssz1  = 1
szBits Ssz8  = 8
szBits Ssz16 = 16
szBits Ssz32 = 32
szBits Ssz64 = 64

data ListRepr where
    ListNormal :: NormalListRepr -> ListRepr
    ListComposite :: ListRepr

data NormalListRepr where
    ListData :: DataSz -> NormalListRepr
    ListPtr :: NormalListRepr

data PtrRepr
    = Capability
    | List (Maybe ListRepr)
    | Struct

data Repr
    = Ptr (Maybe PtrRepr)
    | Data DataSz

data FieldLoc (r :: Repr) where
    GroupField :: FieldLoc ('Ptr ('Just 'Struct))
    UnionField :: Word16 -> FieldLoc ('Ptr ('Just 'Struct))
    PtrField :: Word16 -> FieldLoc ('Ptr a)
    DataField :: DataFieldLoc a -> FieldLoc ('Data a)

data DataFieldLoc sz = DataFieldLoc
    { offset       :: Int
    , size         :: SSz sz
    , defaultValue :: Word64
    }

class HasRepr a (r :: Repr) | a -> r

data Field a b where
    Field :: HasRepr b r => FieldLoc r -> Field a b

class
    ( HasRepr a ('Ptr ('Just 'Struct))
    , IsLabel name (Field a b)
    ) => HasField name a b | a name -> b

-- | Types that can be converted to and from a 64-bit word.
--
-- Anything that goes in the data section of a struct will have
-- an instance of this.
class HasRepr a ('Data sz) => IsData a sz where
    -- | Convert from a 64-bit words Truncates the word if the
    -- type has less than 64 bits.
    fromWord :: Word64 -> a

    -- | Convert to a 64-bit word.
    toWord :: a -> Word64

----

data Untyped (r :: Repr)

type Repr'AnyStruct = ('Ptr ('Just 'Struct))
type Repr'AnyPointer = ('Ptr 'Nothing)
type Repr'AnyList = ('Ptr ('Just ('List 'Nothing)))
type Repr'Capability = ('Ptr ('Just 'Capability))

type AnyStruct = Untyped Repr'AnyStruct
type AnyPointer = Untyped Repr'AnyPointer
type AnyList = Untyped Repr'AnyList
type Capability = Untyped Repr'Capability

data Raw mut a where
    Raw :: HasRepr a r => UntypedRaw mut r -> Raw mut a

data UntypedRaw mut r where
    UntypedRaw'List :: ListRaw mut r -> UntypedRaw mut ('Ptr ('Just ('List ('Just r))))
    UntypedRaw'Struct :: StructRaw mut -> UntypedRaw mut Repr'AnyStruct
    UntypedRaw'AnyPointer :: AnyPointerRaw mut -> UntypedRaw mut Repr'AnyPointer
    UntypedRaw'AnyList :: AnyListRaw mut -> UntypedRaw mut Repr'AnyList
    UntypedRaw'Capability :: CapabilityRaw mut -> UntypedRaw mut Repr'Capability
    UntypedRaw'Data :: DataRaw a -> UntypedRaw mut ('Data a)

data DataRaw a where
    DR0 :: DataRaw 'Sz0
    DR1 :: Bool -> DataRaw 'Sz1
    DR8 :: Word8 -> DataRaw 'Sz8
    DR16 :: Word16 -> DataRaw 'Sz16
    DR32 :: Word32 -> DataRaw 'Sz32
    DR64 :: Word64 -> DataRaw 'Sz64

data StructRaw mut = StructRaw
    { location :: WordPtr mut
    , nWords   :: Word16
    , nPtrs    :: Word16
    }

data ListRaw mut (r :: ListRepr) where
    ListRaw'Composite :: Int -> StructRaw mut -> ListRaw mut 'ListComposite
    ListRaw'Data :: NormalListRaw mut -> SSz sz -> ListRaw mut ('ListNormal ('ListData sz))
    ListRaw'Ptr :: NormalListRaw mut -> ListRaw mut ('ListNormal 'ListPtr)

data NormalListRaw mut = NormalListRaw
    { location :: WordPtr mut
    , len      :: Int
    }

data AnyPointerRaw mut
    = AnyPointerRaw'Struct (StructRaw mut)
    | AnyPointerRaw'List (AnyListRaw mut)
    | AnyPointerRaw'Capability (CapabilityRaw mut)

data CapabilityRaw mut = CapabilityRaw
    { index   :: Word32
    , message :: Message mut
    }

data AnyListRaw mut where
    AnyListRaw :: ListRaw mut a -> AnyListRaw mut

type IsStruct a = HasRepr a ('Ptr ('Just 'Struct))

---

instance HasRepr (Untyped r) r

instance HasRepr () ('Data 'Sz0)
instance HasRepr Bool ('Data 'Sz1)
instance HasRepr Word8 ('Data 'Sz8)
instance HasRepr Word16 ('Data 'Sz16)
instance HasRepr Word32 ('Data 'Sz32)
instance HasRepr Word64 ('Data 'Sz64)
instance HasRepr Int8 ('Data 'Sz8)
instance HasRepr Int16 ('Data 'Sz16)
instance HasRepr Int32 ('Data 'Sz32)
instance HasRepr Int64 ('Data 'Sz64)
instance HasRepr Float ('Data 'Sz32)
instance HasRepr Double ('Data 'Sz64)


type family PreferredListRepr (a :: Repr) :: ListRepr  where
    PreferredListRepr ('Data sz) = 'ListNormal ('ListData sz)
    PreferredListRepr ('Ptr ('Just 'Struct)) = 'ListComposite
    PreferredListRepr ('Ptr a) = 'ListNormal 'ListPtr

data List a

instance (HasRepr a r, rl ~ PreferredListRepr r)  => HasRepr (List a) ('Ptr ('Just ('List ('Just rl))))

getClient :: ReadCtx m mut => CapabilityRaw mut -> m M.Client
getClient CapabilityRaw{message, index} =
    M.getCap message (fromIntegral index)

-- | @get ptr@ returns the pointer stored at @ptr@.
-- Deducts 1 from the quota for each word read (which may be multiple in the
-- case of far pointers).
get :: ReadCtx m mut => M.WordPtr mut -> m (Maybe (AnyPointerRaw mut))
get ptr@M.WordPtr{pMessage, pAddr} = do
    word <- getWord ptr
    case P.parsePtr word of
        Nothing -> return Nothing
        Just p -> case p of
            P.CapPtr cap -> return $ Just $
                AnyPointerRaw'Capability CapabilityRaw
                    { message = pMessage
                    , index = cap
                    }
            P.StructPtr off dataSz ptrSz -> return $ Just $
                AnyPointerRaw'Struct $ StructRaw
                    ptr { M.pAddr = resolveOffset pAddr off } dataSz ptrSz
            P.ListPtr off eltSpec -> Just <$>
                getList ptr { M.pAddr = resolveOffset pAddr off } eltSpec
            P.FarPtr twoWords offset segment -> do
                landingSegment <- M.getSegment pMessage (fromIntegral segment)
                let addr' = WordAt { wordIndex = fromIntegral offset
                                   , segIndex = fromIntegral segment
                                   }
                let landingPtr = M.WordPtr
                        { pMessage
                        , pSegment = landingSegment
                        , pAddr = addr'
                        }
                if not twoWords
                    then get landingPtr
                    else do
                        landingPad <- getWord landingPtr
                        case P.parsePtr landingPad of
                            Just (P.FarPtr False off seg) -> do
                                let segIndex = fromIntegral seg
                                finalSegment <- M.getSegment pMessage segIndex
                                tagWord <- getWord M.WordPtr
                                    { pMessage
                                    , pSegment = landingSegment
                                    , M.pAddr = addr' { wordIndex = wordIndex addr' + 1 }
                                    }
                                let finalPtr = M.WordPtr
                                        { pMessage
                                        , pSegment = finalSegment
                                        , pAddr = WordAt
                                            { wordIndex = fromIntegral off
                                            , segIndex
                                            }
                                        }
                                case P.parsePtr tagWord of
                                    Just (P.StructPtr 0 dataSz ptrSz) ->
                                        return $ Just $
                                            AnyPointerRaw'Struct $
                                                StructRaw finalPtr dataSz ptrSz
                                    Just (P.ListPtr 0 eltSpec) ->
                                        Just <$> getList finalPtr eltSpec
                                    -- TODO: I'm not sure whether far pointers to caps are
                                    -- legal; it's clear how they would work, but I don't
                                    -- see a use, and the spec is unclear. Should check
                                    -- how the reference implementation does this, copy
                                    -- that, and submit a patch to the spec.
                                    Just (P.CapPtr cap) ->
                                        return $ Just $
                                            AnyPointerRaw'Capability $ CapabilityRaw
                                                { message = pMessage
                                                , index = cap
                                                }
                                    ptr -> throwM $ E.InvalidDataError $
                                        "The tag word of a far pointer's " ++
                                        "2-word landing pad should be an intra " ++
                                        "segment pointer with offset 0, but " ++
                                        "we read " ++ show ptr
                            ptr -> throwM $ E.InvalidDataError $
                                "The first word of a far pointer's 2-word " ++
                                "landing pad should be another far pointer " ++
                                "(with a one-word landing pad), but we read " ++
                                show ptr

  where
    getWord M.WordPtr{pSegment, pAddr=WordAt{wordIndex}} =
        invoice 1 *> M.read pSegment wordIndex
    resolveOffset addr@WordAt{..} off =
        addr { wordIndex = wordIndex + fromIntegral off + 1 }
    getList ptr@M.WordPtr{pAddr=addr@WordAt{wordIndex}} eltSpec = AnyPointerRaw'List <$>
        case eltSpec of
            P.EltNormal sz len -> pure $ case sz of
                P.Sz0   -> AnyListRaw $ ListRaw'Data nlist Ssz0
                P.Sz1   -> AnyListRaw $ ListRaw'Data nlist Ssz1
                P.Sz8   -> AnyListRaw $ ListRaw'Data nlist Ssz8
                P.Sz16  -> AnyListRaw $ ListRaw'Data nlist Ssz16
                P.Sz32  -> AnyListRaw $ ListRaw'Data nlist Ssz32
                P.Sz64  -> AnyListRaw $ ListRaw'Data nlist Ssz64
                P.SzPtr -> AnyListRaw $ ListRaw'Ptr nlist
              where
                nlist = NormalListRaw ptr (fromIntegral len)
            P.EltComposite _ -> do
                tagWord <- getWord ptr
                case P.parsePtr' tagWord of
                    P.StructPtr numElts dataSz ptrSz ->
                        pure $ AnyListRaw $ ListRaw'Composite (fromIntegral numElts)
                            (StructRaw
                                ptr { M.pAddr = addr { wordIndex = wordIndex + 1 } }
                                dataSz
                                ptrSz)
                    tag -> throwM $ E.InvalidDataError $
                        "Composite list tag was not a struct-" ++
                        "formatted word: " ++ show tag
