{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DuplicateRecordFields  #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StrictData             #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
-- Temporary, while stuff settles:
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Capnp.UntypedNew
    ( HasRepr
    , Repr(..)
    , PtrRepr(..)
    , ListRepr(..)
    , DataSz(..)

    , HasField
    , Field(..)
    , FieldLoc(..)
    , DataFieldLoc(..)

    , structByteCount
    , structWordCount
    , structPtrCount
    , structListByteCount
    , structListWordCount
    , structListPtrCount
    , getClient
    , get, index, length
    -- setIndex
    , take
    -- , rootPtr
    -- , setRoot
    , rawBytes
    , ReadCtx
    , RWCtx
    -- , HasMessage(..), MessageDefault(..)
    -- , allocStruct
    -- , allocCompositeList
    -- , allocList0
    -- , allocList1
    -- , allocList8
    -- , allocList16
    -- , allocList32
    -- , allocList64
    -- , allocListPtr
    -- , appendCap

    -- , TraverseMsg(..)
    ) where

import Prelude hiding (length, take)

import Data.Bits
import Data.Int
import Data.Word

import qualified Data.ByteString as BS

import Control.Monad        (when)
import Control.Monad.Catch  (MonadCatch, MonadThrow(throwM))
import Data.Kind            (Type)
import Data.Proxy           (Proxy)
import GHC.OverloadedLabels (IsLabel)

import           Capnp.Address
    (OffsetError (..), WordAddr (..), pointerFrom)
import           Capnp.Bits
    ( BitCount
    , ByteCount (..)
    , Word1 (..)
    , WordCount (..)
    , bytesToWordsCeil
    , replaceBits
    , wordsToBytes
    )
import qualified Capnp.Errors         as E
import           Capnp.Message
    (Message, Mutability (..), Segment, WordPtr)
import qualified Capnp.Message        as M
import qualified Capnp.Pointer        as P
import           Capnp.TraversalLimit (MonadLimit(invoice))
import           Internal.BoundsCheck (checkIndex)

-- | Type (constraint) synonym for the constraints needed for most read
-- operations.
type ReadCtx m mut = (M.MonadReadMessage mut m, MonadThrow m, MonadLimit m)

-- | Synonym for ReadCtx + WriteCtx
type RWCtx m s = (ReadCtx m ('Mut s), M.WriteCtx m s)

data DataSz = Sz0 | Sz1 | Sz8 | Sz16 | Sz32 | Sz64

class DataSizeBits (sz :: DataSz) where
    szBits :: BitCount

instance DataSizeBits 'Sz0 where szBits = 0
instance DataSizeBits 'Sz1 where szBits = 1
instance DataSizeBits 'Sz8 where szBits = 8
instance DataSizeBits 'Sz16 where szBits = 16
instance DataSizeBits 'Sz32 where szBits = 32
instance DataSizeBits 'Sz64 where szBits = 64

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

data DataFieldLoc (sz :: DataSz) = DataFieldLoc
    { offset       :: Int
    , size         :: Proxy sz
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

type family Raw (mut :: Mutability) (r :: Maybe Repr) :: Type where
    Raw mut ('Just r) = RawSome mut r
    Raw mut 'Nothing = RawAny mut

type family RawSome (mut :: Mutability) (r :: Repr) :: Type where
    RawSome mut ('Data sz) = RawData sz
    RawSome mut ('Ptr ptr) = RawPtr mut ptr

type family RawData (sz :: DataSz) :: Type where
    RawData 'Sz0 = ()
    RawData 'Sz1 = Bool
    RawData 'Sz8 = Word8
    RawData 'Sz16 = Word16
    RawData 'Sz32 = Word32
    RawData 'Sz64 = Word64

type family RawPtr (mut :: Mutability) (r :: Maybe PtrRepr) :: Type where
    RawPtr mut 'Nothing = Maybe (RawAnyPointer mut)
    RawPtr mut ('Just r) = RawSomePtr mut r


type family RawSomePtr (mut :: Mutability) (r :: PtrRepr) :: Type where
    RawSomePtr mut 'Struct = RawStruct mut
    RawSomePtr mut 'Capability = RawCapability mut
    RawSomePtr mut ('List r) = RawList mut r

type family RawList (mut :: Mutability) (r :: Maybe ListRepr) :: Type where
    RawList mut 'Nothing = RawAnyList mut
    RawList mut ('Just r) = RawSomeList mut r

type family RawSomeList (mut :: Mutability) (r :: ListRepr) :: Type where
    RawSomeList mut ('ListNormal r) = RawNormalList mut
    RawSomeList mut 'ListComposite = RawStructList mut

data RawStructList mut = RawStructList
    { len :: Int
    , tag :: RawStruct mut
    }

data RawStruct mut = RawStruct
    { location :: WordPtr mut
    , nWords   :: Word16
    , nPtrs    :: Word16
    }

data RawNormalList mut = RawNormalList
    { location :: WordPtr mut
    , len      :: Int
    }

data RawAny mut
    = RawAnyPointer (Maybe (RawAnyPointer mut))
    | RawAnyData RawAnyData

data RawAnyData
    = RawAnyData0 (RawData 'Sz0)
    | RawAnyData1 (RawData 'Sz1)
    | RawAnyData8 (RawData 'Sz8)
    | RawAnyData16 (RawData 'Sz16)
    | RawAnyData32 (RawData 'Sz32)
    | RawAnyData64 (RawData 'Sz64)

data RawAnyPointer mut
    = RawAnyPointer'Struct (RawSomePtr mut 'Struct)
    | RawAnyPointer'Capability (RawSomePtr mut 'Capability)
    | RawAnyPointer'List (RawSomePtr mut ('List 'Nothing))

data RawAnyList mut
    = RawAnyList'Struct (RawSomeList mut 'ListComposite)
    | RawAnyList'Normal (RawAnyNormalList mut)

data RawAnyNormalList mut
    = RawAnyNormalList'Ptr (RawNormalList mut)
    | RawAnyNormalList'Data (RawAnyDataList mut)

data RawAnyDataList mut = RawAnyDataList
    { eltSize :: DataSz
    , list    :: RawNormalList mut
    }

data RawCapability mut = RawCapability
    { capIndex :: Word32
    , message  :: Message mut
    }

---

-- instance HasRepr (Untyped r) r

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


type family ElemRepr (rl :: Maybe ListRepr) :: Maybe Repr where
    ElemRepr ('Just 'ListComposite) = 'Just ('Ptr ('Just 'Struct))
    ElemRepr ('Just ('ListNormal 'ListPtr)) = 'Just ('Ptr 'Nothing)
    ElemRepr ('Just ('ListNormal ('ListData sz))) = 'Just ('Data sz)
    ElemRepr 'Nothing = 'Nothing

type family ListReprFor (e :: Repr) :: ListRepr where
    ListReprFor ('Data sz) = 'ListNormal ('ListData sz)
    ListReprFor ('Ptr ('Just 'Struct)) = 'ListComposite
    ListReprFor ('Ptr a) = 'ListNormal 'ListPtr

-- | Get the size (in words) of a struct's data section.
structWordCount :: RawStruct mut -> WordCount
structWordCount RawStruct{nWords} = fromIntegral nWords

-- | Get the size (in bytes) of a struct's data section.
structByteCount :: RawStruct mut -> ByteCount
structByteCount = wordsToBytes . structWordCount

-- | Get the size of a struct's pointer section.
structPtrCount  :: RawStruct mut -> Word16
structPtrCount RawStruct{nPtrs} = nPtrs

-- | Get the size (in words) of the data sections in a struct list.
structListWordCount :: RawStructList mut -> WordCount
structListWordCount RawStructList{tag} = structWordCount tag

-- | Get the size (in words) of the data sections in a struct list.
structListByteCount :: RawStructList mut -> ByteCount
structListByteCount RawStructList{tag} = structByteCount tag

-- | Get the size of the pointer sections in a struct list.
structListPtrCount :: RawStructList mut -> Word16
structListPtrCount RawStructList{tag} = structPtrCount tag

getClient :: ReadCtx m mut => RawCapability mut -> m M.Client
getClient RawCapability{message, capIndex} =
    M.getCap message (fromIntegral capIndex)

-- | @get ptr@ returns the pointer stored at @ptr@.
-- Deducts 1 from the quota for each word read (which may be multiple in the
-- case of far pointers).
get :: ReadCtx m mut => M.WordPtr mut -> m (Maybe (RawAnyPointer mut))
get ptr@M.WordPtr{pMessage, pAddr} = do
    word <- getWord ptr
    case P.parsePtr word of
        Nothing -> return Nothing
        Just p -> case p of
            P.CapPtr cap -> return $ Just $
                RawAnyPointer'Capability RawCapability
                    { message = pMessage
                    , capIndex = cap
                    }
            P.StructPtr off dataSz ptrSz -> return $ Just $
                RawAnyPointer'Struct $ RawStruct
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
                                            RawAnyPointer'Struct $
                                                RawStruct finalPtr dataSz ptrSz
                                    Just (P.ListPtr 0 eltSpec) ->
                                        Just <$> getList finalPtr eltSpec
                                    -- TODO: I'm not sure whether far pointers to caps are
                                    -- legal; it's clear how they would work, but I don't
                                    -- see a use, and the spec is unclear. Should check
                                    -- how the reference implementation does this, copy
                                    -- that, and submit a patch to the spec.
                                    Just (P.CapPtr cap) ->
                                        return $ Just $
                                            RawAnyPointer'Capability $ RawCapability
                                                { message = pMessage
                                                , capIndex = cap
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
    getList ptr@M.WordPtr{pAddr=addr@WordAt{wordIndex}} eltSpec = RawAnyPointer'List <$>
        case eltSpec of
            P.EltNormal sz len -> pure $ RawAnyList'Normal $ case sz of
                P.Sz0   -> RawAnyNormalList'Data $ RawAnyDataList Sz0 nlist
                P.Sz1   -> RawAnyNormalList'Data $ RawAnyDataList Sz1 nlist
                P.Sz8   -> RawAnyNormalList'Data $ RawAnyDataList Sz8 nlist
                P.Sz16  -> RawAnyNormalList'Data $ RawAnyDataList Sz16 nlist
                P.Sz32  -> RawAnyNormalList'Data $ RawAnyDataList Sz32 nlist
                P.Sz64  -> RawAnyNormalList'Data $ RawAnyDataList Sz64 nlist
                P.SzPtr -> RawAnyNormalList'Ptr nlist
              where
                nlist = RawNormalList ptr (fromIntegral len)
            P.EltComposite _ -> do
                tagWord <- getWord ptr
                case P.parsePtr' tagWord of
                    P.StructPtr numElts dataSz ptrSz ->
                        pure $ RawAnyList'Struct RawStructList
                            { len = fromIntegral numElts
                            , tag = RawStruct
                                ptr { M.pAddr = addr { wordIndex = wordIndex + 1 } }
                                dataSz
                                ptrSz
                            }
                    tag -> throwM $ E.InvalidDataError $
                        "Composite list tag was not a struct-" ++
                        "formatted word: " ++ show tag

class List (r :: Maybe ListRepr) where
    -- | Returns the length of a list
    length :: RawList mut r -> Int

    -- | Index into a list, without checking bounds or traversal
    -- limits. Call 'index' instead of calling this directly.
    basicUnsafeIndex
        :: forall mut m. (ReadCtx m mut)
        => Int -> RawList mut r -> m (Raw mut (ElemRepr r))

    basicUnsafeSetIndex
        :: forall m s. (RWCtx m s)
        => Raw ('Mut s) (ElemRepr r) -> Int -> RawList ('Mut s) r -> m ()

    basicUnsafeTake :: Int -> RawList mut r -> RawList mut r

-- | @index i list@ returns the ith element in @list@. Deducts 1 from the quota
index
    :: forall r mut m. (ReadCtx m mut, List r)
    => Int -> RawList mut r -> m (Raw mut (ElemRepr r))
index i list = do
    invoice 1
    checkIndex i (length @r @mut list)
    basicUnsafeIndex @r @mut i list

-- | @'setIndex value i list@ sets the @i@th element of @list@ to @value@.
setIndex
    :: forall r m s. (List r, RWCtx m s)
    => Raw ('Mut s) (ElemRepr r) -> Int -> RawList ('Mut s) r -> m ()
setIndex value i list = do
    checkIndex i (length @r @('Mut s) list)
    basicUnsafeSetIndex @r value i list

-- | Return a prefix of the list, of the given length.
take :: forall m mut r. (MonadThrow m, List r) => Int -> RawList mut r -> m (RawList mut r)
take count list
    | length @r @mut list < count =
        throwM E.BoundsError { E.index = count, E.maxIndex = length @r @mut list - 1 }
    | otherwise = pure $ basicUnsafeTake @r @mut count list

instance List ('Just 'ListComposite) where
    length RawStructList{len} = len
    basicUnsafeIndex i RawStructList{tag = RawStruct ptr@M.WordPtr{pAddr=addr@WordAt{..}} dataSz ptrSz} = do
        let offset = WordCount $ i * (fromIntegral dataSz + fromIntegral ptrSz)
        let addr' = addr { wordIndex = wordIndex + offset }
        return $ RawStruct ptr { M.pAddr = addr' } dataSz ptrSz
    basicUnsafeTake i RawStructList{tag} = RawStructList{tag, len = i}
    basicUnsafeSetIndex = undefined


basicUnsafeTakeNormal :: Int -> RawNormalList mut -> RawNormalList mut
basicUnsafeTakeNormal i RawNormalList{location} = RawNormalList{location, len = i}

instance List ('Just ('ListNormal 'ListPtr)) where
    length RawNormalList{len} = len
    basicUnsafeIndex i (RawNormalList ptr@M.WordPtr{pAddr=addr@WordAt{..}} _) =
        get ptr { M.pAddr = addr { wordIndex = wordIndex + WordCount i } }
    basicUnsafeTake = basicUnsafeTakeNormal
    basicUnsafeSetIndex = undefined

basicUnsafeIndexNList :: (ReadCtx m mut, Integral a) => BitCount -> Int -> RawNormalList mut -> m a
basicUnsafeIndexNList nbits i (RawNormalList M.WordPtr{pSegment, pAddr=WordAt{..}} _) = do
    let eltsPerWord = 64 `div` fromIntegral nbits
    let wordIndex' = wordIndex + WordCount (i `div` eltsPerWord)
    word <- M.read pSegment wordIndex'
    let shift = fromIntegral (i `mod` eltsPerWord) * nbits
    pure $ fromIntegral $ word `shiftR` fromIntegral shift

basicUnsafeSetIndexNList
    :: (M.WriteCtx m s, Integral a, Bounded a)
    => BitCount -> a -> Int -> RawNormalList ('Mut s) -> m ()
basicUnsafeSetIndexNList
        nbits
        value
        i
        RawNormalList{location=M.WordPtr{pSegment, pAddr=WordAt{wordIndex}}}
    = do
        let eltsPerWord = 64 `div` fromIntegral nbits
        let eltWordIndex = wordIndex + WordCount (i `div` eltsPerWord)
        word <- M.read pSegment eltWordIndex
        let shift = fromIntegral (i `mod` eltsPerWord) * nbits
        M.write pSegment eltWordIndex $ replaceBits value word (fromIntegral shift)

instance {-# OVERLAPS #-} List ('Just ('ListNormal ('ListData 'Sz0))) where
    length RawNormalList{len} = len
    basicUnsafeIndex _ _ = pure ()
    basicUnsafeTake = basicUnsafeTakeNormal
    basicUnsafeSetIndex _ _ _ = pure ()

instance {-# OVERLAPS #-} List ('Just ('ListNormal ('ListData 'Sz1))) where
    length RawNormalList{len} = len
    basicUnsafeIndex i list = do
        Word1 val <- basicUnsafeIndexNList 1 i list
        pure val
    basicUnsafeTake = basicUnsafeTakeNormal
    basicUnsafeSetIndex val = basicUnsafeSetIndexNList 1 (Word1 val)

instance (DataSizeBits sz, Integral (RawData sz), Bounded (RawData sz))
    => List ('Just ('ListNormal ('ListData sz)))
  where
    length RawNormalList{len} = len
    basicUnsafeIndex = basicUnsafeIndexNList (szBits @sz)
    basicUnsafeTake = basicUnsafeTakeNormal
    basicUnsafeSetIndex = basicUnsafeSetIndexNList (szBits @sz)

instance List 'Nothing where
    length (RawAnyList'Struct (l :: RawStructList mut)) =
        length @('Just 'ListComposite) @mut l
    length (RawAnyList'Normal (l :: RawAnyNormalList mut)) =
        let list = case l of
                RawAnyNormalList'Ptr l'                    -> l'
                RawAnyNormalList'Data RawAnyDataList{list} -> list
        in
        -- The type checker insists we give it *some* type for the first parameter,
        -- but any normal list type will do, since the instances for length
        -- are all the same -- so this is fine even if the list was actually
        -- a data list.
        length @('Just ('ListNormal 'ListPtr)) @mut list

    basicUnsafeIndex i (RawAnyList'Struct (l :: RawStructList mut)) =
        RawAnyPointer . Just . RawAnyPointer'Struct <$>
            basicUnsafeIndex @('Just 'ListComposite) @mut i l
    basicUnsafeIndex i (RawAnyList'Normal (l :: RawAnyNormalList mut)) =
        case l of
            RawAnyNormalList'Ptr l' ->
                RawAnyPointer <$> basicUnsafeIndex @('Just ('ListNormal 'ListPtr)) i l'
            RawAnyNormalList'Data RawAnyDataList{eltSize, list} ->
                RawAnyData <$> case eltSize of
                    Sz0  -> RawAnyData0  <$> basicUnsafeIndex @('Just ('ListNormal ('ListData 'Sz0)))  i list
                    Sz1  -> RawAnyData1  <$> basicUnsafeIndex @('Just ('ListNormal ('ListData 'Sz1)))  i list
                    Sz8  -> RawAnyData8  <$> basicUnsafeIndex @('Just ('ListNormal ('ListData 'Sz8)))  i list
                    Sz16 -> RawAnyData16 <$> basicUnsafeIndex @('Just ('ListNormal ('ListData 'Sz16))) i list
                    Sz32 -> RawAnyData32 <$> basicUnsafeIndex @('Just ('ListNormal ('ListData 'Sz32))) i list
                    Sz64 -> RawAnyData64 <$> basicUnsafeIndex @('Just ('ListNormal ('ListData 'Sz64))) i list
    basicUnsafeTake i list = case list of
        RawAnyList'Struct (l :: RawStructList mut) ->
            RawAnyList'Struct $ basicUnsafeTake @('Just 'ListComposite) @mut i l
        RawAnyList'Normal (RawAnyNormalList'Ptr l) ->
            RawAnyList'Normal (RawAnyNormalList'Ptr (basicUnsafeTakeNormal i l))
        RawAnyList'Normal (RawAnyNormalList'Data RawAnyDataList{eltSize, list}) ->
            RawAnyList'Normal $ RawAnyNormalList'Data (RawAnyDataList { eltSize, list = basicUnsafeTakeNormal i list })
    basicUnsafeSetIndex = undefined

-- | 'rawBytes' returns the raw bytes corresponding to the list.
rawBytes
    :: ReadCtx m 'Const
    => RawSomeList 'Const (ListReprFor ('Data 'Sz8)) -> m BS.ByteString
-- TODO: we can get away with a more lax context than ReadCtx, maybe even make
-- this non-monadic.
rawBytes (RawNormalList M.WordPtr{pSegment, pAddr=WordAt{wordIndex}} len) = do
    invoice $ fromIntegral $ bytesToWordsCeil (ByteCount len)
    let bytes = M.toByteString pSegment
    let ByteCount byteOffset = wordsToBytes wordIndex
    pure $ BS.take len $ BS.drop byteOffset bytes


{-
-- | Returns the root pointer of a message.
rootPtr :: ReadCtx m mut => M.Message mut -> m (RawStruct mut)
rootPtr msg = do
    seg <- M.getSegment msg 0
    root <- get M.WordPtr
        { pMessage = msg
        , pSegment = seg
        , pAddr = WordAt 0 0
        }
    case root of
        Just (RawAnyPointer'Struct struct) -> pure struct
        Nothing -> messageDefault msg
        _ -> throwM $ E.SchemaViolationError
                "Unexpected root type; expected struct."
-}
