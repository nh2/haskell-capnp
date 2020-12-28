{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DuplicateRecordFields  #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE NamedFieldPuns         #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StrictData             #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-}
{-|
Module: Capnp.Untyped
Description: Utilities for reading capnproto messages with no schema.

The types and functions in this module know about things like structs and
lists, but are not schema aware.

Each of the data types exported by this module is parametrized over the message's
mutability (see "Capnp.Message").
-}
module Capnp.UntypedNew
    ( HasField
    , Field(..)
    , FieldLoc(..)
    , DataFieldLoc(..)

    , getData, getPtr
    , setData, setPtr
    , structByteCount
    , structWordCount
    , structPtrCount
    , structListByteCount
    , structListWordCount
    , structListPtrCount
    , getClient
    , get, index, length
    , setIndex
    , take
    , rootPtr
    , setRoot
    , rawBytes
    , ReadCtx
    , RWCtx
    , HasMessage(..), MessageDefault(..)
    , allocStruct
    , allocCompositeList
    , allocList0
    , allocList1
    , allocList8
    , allocList16
    , allocList32
    , allocList64
    , allocListPtr
    , appendCap

    -- , TraverseMsg(..)
    ) where

import Prelude hiding (length, take)

import Data.Bits
import Data.Word

import qualified Data.ByteString as BS

import Control.Monad.Catch  (MonadThrow(throwM))
import Data.Foldable        (for_)
import Data.Kind            (Type)
import Data.Proxy           (Proxy)
import GHC.OverloadedLabels (IsLabel)

import           Capnp.Address
    (OffsetError (..), WordAddr (..), pointerFrom)
import           Capnp.Bits
    ( BitCount (..)
    , ByteCount (..)
    , Word1 (..)
    , WordCount (..)
    , bitsToBytesCeil
    , bytesToWordsCeil
    , replaceBits
    , wordsToBytes
    )
import qualified Capnp.Errors         as E
import           Capnp.Message        (Message, Mutability (..), WordPtr)
import qualified Capnp.Message        as M
import qualified Capnp.Pointer        as P
import           Capnp.Repr
import           Capnp.TraversalLimit (MonadLimit(invoice))
import           Internal.BoundsCheck (checkIndex)

-- | Type (constraint) synonym for the constraints needed for most read
-- operations.
type ReadCtx m mut = (M.MonadReadMessage mut m, MonadThrow m, MonadLimit m)

-- | Synonym for ReadCtx + WriteCtx
type RWCtx m s = (ReadCtx m ('Mut s), M.WriteCtx m s)

-------------------------------------------------------------------------------
-- Representations
-------------------------------------------------------------------------------

data DataSzTag (sz :: DataSz) where
    D0 :: DataSzTag 'Sz0
    D1 :: DataSzTag 'Sz1
    D8 :: DataSzTag 'Sz8
    D16 :: DataSzTag 'Sz16
    D32 :: DataSzTag 'Sz32
    D64 :: DataSzTag 'Sz64

class DataSizeBits (sz :: DataSz) where
    szBits :: BitCount

instance DataSizeBits 'Sz0 where szBits = 0
instance DataSizeBits 'Sz1 where szBits = 1
instance DataSizeBits 'Sz8 where szBits = 8
instance DataSizeBits 'Sz16 where szBits = 16
instance DataSizeBits 'Sz32 where szBits = 32
instance DataSizeBits 'Sz64 where szBits = 64

-------------------------------------------------------------------------------
-- Fields. TODO: this probably belongs elsewhere.
-------------------------------------------------------------------------------

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

data Field a b where
    Field :: HasRepr b r => FieldLoc r -> Field a b

class
    ( HasRepr a ('Ptr ('Just 'Struct))
    , IsLabel name (Field a b)
    ) => HasField name a b | a name -> b

----


-------------------------------------------------------------------------------
-- Raw* type families
-------------------------------------------------------------------------------

-- | @Raw mut r@ is a value with representation @r@ stored in a message with
-- mutability @mut@.
type family Raw (mut :: Mutability) (r :: Repr) :: Type where
    Raw mut ('Data sz) = RawData sz
    Raw mut ('Ptr ptr) = RawPtr mut ptr

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
    RawSomeList mut ('ListNormal r) = RawNormalList mut r
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

data RawNormalList mut (r :: NormalListRepr) = RawNormalList
    { location :: WordPtr mut
    , len      :: Int
    }

data RawAnyPointer mut
    = RawAnyPointer'Struct (RawSomePtr mut 'Struct)
    | RawAnyPointer'Capability (RawSomePtr mut 'Capability)
    | RawAnyPointer'List (RawSomePtr mut ('List 'Nothing))

data RawAnyList mut
    = RawAnyList'Struct (RawSomeList mut 'ListComposite)
    | RawAnyList'Normal (RawAnyNormalList mut)

data RawAnyNormalList mut
    = RawAnyNormalList'Ptr (RawNormalList mut 'ListPtr)
    | RawAnyNormalList'Data (RawAnyDataList mut)

data RawAnyDataList mut where
    RawAnyDataList :: DataSzTag sz -> RawNormalList mut ('ListData sz) -> RawAnyDataList mut

data RawCapability mut = RawCapability
    { capIndex :: Word32
    , msg      :: Message mut
    }

---


-- | @ElemRepr r@ is the representation of elements of lists with
-- representation @r@.
type family ElemRepr (rl :: ListRepr) :: Repr where
    ElemRepr 'ListComposite = 'Ptr ('Just 'Struct)
    ElemRepr ('ListNormal 'ListPtr) = 'Ptr 'Nothing
    ElemRepr ('ListNormal ('ListData sz)) = 'Data sz

-- | @ListReprFor e@ is the representation of lists with elements
-- whose representation is @e@.
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
getClient RawCapability{msg, capIndex} =
    M.getCap msg (fromIntegral capIndex)

-- | @get ptr@ returns the pointer stored at @ptr@.
-- Deducts 1 from the quota for each word read (which may be multiple in the
-- case of far pointers).
get :: forall mut m. ReadCtx m mut => M.WordPtr mut -> m (Maybe (RawAnyPointer mut))
get ptr@M.WordPtr{pMessage, pAddr} = do
    word <- getWord ptr
    case P.parsePtr word of
        Nothing -> return Nothing
        Just p -> case p of
            P.CapPtr cap -> return $ Just $
                RawAnyPointer'Capability RawCapability
                    { msg = pMessage
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
                                                { msg = pMessage
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
            P.EltNormal sz len -> pure $ case sz of
                P.Sz0   -> RawAnyList'Normal $ RawAnyNormalList'Data $ RawAnyDataList D0 nlist
                P.Sz1   -> RawAnyList'Normal $ RawAnyNormalList'Data $ RawAnyDataList D1 nlist
                P.Sz8   -> RawAnyList'Normal $ RawAnyNormalList'Data $ RawAnyDataList D8 nlist
                P.Sz16  -> RawAnyList'Normal $ RawAnyNormalList'Data $ RawAnyDataList D16 nlist
                P.Sz32  -> RawAnyList'Normal $ RawAnyNormalList'Data $ RawAnyDataList D32 nlist
                P.Sz64  -> RawAnyList'Normal $ RawAnyNormalList'Data $ RawAnyDataList D64 nlist
                P.SzPtr -> RawAnyList'Normal $ RawAnyNormalList'Ptr nlist
              where
                nlist :: forall r. RawNormalList mut r
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

-------------------------------------------------------------------------------
-- Lists
-------------------------------------------------------------------------------

-- | Operations common to all list types.
class List (r :: ListRepr) where
    -- | Returns the length of a list
    length :: RawList mut ('Just r) -> Int

    -- | Index into a list, without checking bounds or traversal
    -- limits. Call 'index' instead of calling this directly.
    basicUnsafeIndex
        :: forall mut m. (ReadCtx m mut)
        => Int -> RawSomeList mut r -> m (Raw mut (ElemRepr r))

    basicUnsafeSetIndex
        :: forall m s. (RWCtx m s)
        => Raw ('Mut s) (ElemRepr r) -> Int -> RawSomeList ('Mut s) r -> m ()

    basicUnsafeTake :: Int -> RawSomeList mut r -> RawSomeList mut r

normalListLength :: RawNormalList mut r -> Int
normalListLength RawNormalList{len} = len

-- | @index i list@ returns the ith element in @list@. Deducts 1 from the quota
index
    :: forall r mut m. (ReadCtx m mut, List r)
    => Int -> RawList mut ('Just r) -> m (Raw mut (ElemRepr r))
index i list = do
    invoice 1
    checkIndex i (length @r @mut list)
    basicUnsafeIndex @r @mut i list

-- | @'setIndex value i list@ sets the @i@th element of @list@ to @value@.
setIndex
    :: forall r m s. (List r, RWCtx m s)
    => Raw ('Mut s) (ElemRepr r) -> Int -> RawSomeList ('Mut s) r -> m ()
setIndex value i list = do
    checkIndex i (length @r @('Mut s) list)
    basicUnsafeSetIndex @r value i list

-- | Return a prefix of the list, of the given length.
take :: forall m mut r. (MonadThrow m, List r) => Int -> RawSomeList mut r -> m (RawSomeList mut r)
take count list
    | length @r @mut list < count =
        throwM E.BoundsError { E.index = count, E.maxIndex = length @r @mut list - 1 }
    | otherwise = pure $ basicUnsafeTake @r @mut count list

instance List 'ListComposite where
    length RawStructList{len} = len
    basicUnsafeIndex i RawStructList{tag = RawStruct ptr@M.WordPtr{pAddr=addr@WordAt{..}} dataSz ptrSz} = do
        let offset = WordCount $ i * (fromIntegral dataSz + fromIntegral ptrSz)
        let addr' = addr { wordIndex = wordIndex + offset }
        return $ RawStruct ptr { M.pAddr = addr' } dataSz ptrSz
    basicUnsafeTake i RawStructList{tag} = RawStructList{tag, len = i}
    basicUnsafeSetIndex value i list = do
        dest <- basicUnsafeIndex @'ListComposite i list
        copyStruct dest value


basicUnsafeTakeNormal :: Int -> RawNormalList mut r -> RawNormalList mut r
basicUnsafeTakeNormal i RawNormalList{location} = RawNormalList{location, len = i}

instance List ('ListNormal 'ListPtr) where
    length RawNormalList{len} = len
    basicUnsafeIndex i (RawNormalList ptr@M.WordPtr{pAddr=addr@WordAt{..}} _) =
        get ptr { M.pAddr = addr { wordIndex = wordIndex + WordCount i } }
    basicUnsafeTake = basicUnsafeTakeNormal
    basicUnsafeSetIndex value i list = case value of
        Just p | message p /= message list -> do
            newPtr <- copyPtr (message list) value
            basicUnsafeSetIndex @('ListNormal 'ListPtr) newPtr i list
        Nothing ->
            basicUnsafeSetIndexNList 64 (P.serializePtr Nothing) i list
        Just (RawAnyPointer'Capability RawCapability{capIndex}) ->
            basicUnsafeSetIndexNList 64 (P.serializePtr (Just (P.CapPtr capIndex))) i list
        Just p@(RawAnyPointer'List ptrList) ->
            setPtrIndex list p $ P.ListPtr 0 (listEltSpec ptrList)
        Just p@(RawAnyPointer'Struct (RawStruct _ dataSz ptrSz)) ->
            setPtrIndex list p $ P.StructPtr 0 dataSz ptrSz
      where
        setPtrIndex
            :: (ReadCtx m ('Mut s), M.WriteCtx m s)
            => RawNormalList ('Mut s) r -> RawAnyPointer ('Mut s) -> P.Ptr -> m ()
        setPtrIndex RawNormalList{location=nPtr@M.WordPtr{pAddr=addr@WordAt{wordIndex}}} absPtr relPtr =
            let srcPtr = nPtr { M.pAddr = addr { wordIndex = wordIndex + WordCount i } }
            in setPointerTo srcPtr (ptrAddr absPtr) relPtr
        listEltSpec = \case
            RawAnyList'Struct RawStructList{tag = RawStruct _ dataSz ptrSz} ->
                P.EltComposite $ (*)
                    (fromIntegral $ length @('ListNormal 'ListPtr) list)
                    (fromIntegral dataSz + fromIntegral ptrSz)
            RawAnyList'Normal l ->
                case l of
                RawAnyNormalList'Ptr RawNormalList{len} ->
                    P.EltNormal P.SzPtr (fromIntegral len)
                RawAnyNormalList'Data (RawAnyDataList sz RawNormalList{len}) ->
                    let esize = case sz of
                            D0  -> P.Sz0
                            D1  -> P.Sz1
                            D8  -> P.Sz8
                            D16 -> P.Sz16
                            D32 -> P.Sz32
                            D64 -> P.Sz64
                    in
                    P.EltNormal esize (fromIntegral len)

-- | Return the address of the pointer's target. It is illegal to call this on
-- a pointer which targets a capability.
ptrAddr :: RawAnyPointer mut -> WordAddr
ptrAddr (RawAnyPointer'Capability _) = error "ptrAddr called on a capability pointer."
ptrAddr (RawAnyPointer'Struct (RawStruct M.WordPtr{pAddr}_ _)) = pAddr
ptrAddr (RawAnyPointer'List list) = listAddr list

-- | Return the starting address of the list.
listAddr :: RawAnyList mut -> WordAddr
listAddr (RawAnyList'Struct RawStructList{tag = RawStruct M.WordPtr{pAddr} _ _}) =
    -- pAddr is the address of the first element of the list, but
    -- composite lists start with a tag word:
    pAddr { wordIndex = wordIndex pAddr - 1 }
listAddr (RawAnyList'Normal l) = case l of
    RawAnyNormalList'Ptr RawNormalList{location=M.WordPtr{pAddr}} -> pAddr
    RawAnyNormalList'Data (RawAnyDataList _ RawNormalList{location=M.WordPtr{pAddr}}) -> pAddr

basicUnsafeIndexNList :: (ReadCtx m mut, Integral a) => BitCount -> Int -> RawNormalList mut r -> m a
basicUnsafeIndexNList nbits i (RawNormalList M.WordPtr{pSegment, pAddr=WordAt{..}} _) = do
    let eltsPerWord = 64 `div` fromIntegral nbits
    let wordIndex' = wordIndex + WordCount (i `div` eltsPerWord)
    word <- M.read pSegment wordIndex'
    let shift = fromIntegral (i `mod` eltsPerWord) * nbits
    pure $ fromIntegral $ word `shiftR` fromIntegral shift

basicUnsafeSetIndexNList
    :: (M.WriteCtx m s, Integral a, Bounded a)
    => BitCount -> a -> Int -> RawNormalList ('Mut s) r -> m ()
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

instance {-# OVERLAPS #-} List ('ListNormal ('ListData 'Sz0)) where
    length = normalListLength
    basicUnsafeIndex _ _ = pure ()
    basicUnsafeTake = basicUnsafeTakeNormal
    basicUnsafeSetIndex _ _ _ = pure ()

instance {-# OVERLAPS #-} List ('ListNormal ('ListData 'Sz1)) where
    length = normalListLength
    basicUnsafeIndex i list = do
        Word1 val <- basicUnsafeIndexNList 1 i list
        pure val
    basicUnsafeTake = basicUnsafeTakeNormal
    basicUnsafeSetIndex val = basicUnsafeSetIndexNList 1 (Word1 val)

instance (DataSizeBits sz, Integral (RawData sz), Bounded (RawData sz))
    => List ('ListNormal ('ListData sz))
  where
    length = normalListLength
    basicUnsafeIndex = basicUnsafeIndexNList (szBits @sz)
    basicUnsafeTake = basicUnsafeTakeNormal
    basicUnsafeSetIndex = basicUnsafeSetIndexNList (szBits @sz)

-- | The data section of a struct, as a list of Word64
dataSection :: RawStruct mut -> RawSomeList mut ('ListNormal ('ListData 'Sz64))
dataSection RawStruct{location, nWords} =
    RawNormalList location (fromIntegral nWords)

-- | The pointer section of a struct, as a list of Ptr
ptrSection :: RawStruct mut -> RawSomeList mut ('ListNormal 'ListPtr)
ptrSection (RawStruct ptr@M.WordPtr{pAddr=addr@WordAt{wordIndex}} dataSz ptrSz) =
    RawNormalList
        { location = ptr { M.pAddr = addr { wordIndex = wordIndex + fromIntegral dataSz } }
        , len = fromIntegral ptrSz
        }

-- | @'getData' i struct@ gets the @i@th word from the struct's data section,
-- returning 0 if it is absent.
getData :: ReadCtx m mut => Int -> RawStruct mut-> m Word64
getData i struct
    | fromIntegral (structWordCount struct) <= i = 0 <$ invoice 1
    | otherwise = index @('ListNormal ('ListData 'Sz64)) i (dataSection struct)

-- | @'getPtr' i struct@ gets the @i@th word from the struct's pointer section,
-- returning Nothing if it is absent.
getPtr :: ReadCtx m mut => Int -> RawStruct mut -> m (Maybe (RawAnyPointer mut))
getPtr i struct
    | fromIntegral (structPtrCount struct) <= i = Nothing <$ invoice 1
    | otherwise = index @('ListNormal 'ListPtr) i (ptrSection struct)

-- | @'setData' value i struct@ sets the @i@th word in the struct's data section
-- to @value@.
setData :: (ReadCtx m ('Mut s), M.WriteCtx m s)
    => Word64 -> Int -> RawStruct ('Mut s) -> m ()
setData value i = setIndex @('ListNormal ('ListData 'Sz64)) value i . dataSection

-- | @'setData' value i struct@ sets the @i@th pointer in the struct's pointer
-- section to @value@.
setPtr :: (ReadCtx m ('Mut s), M.WriteCtx m s) => Maybe (RawAnyPointer ('Mut s)) -> Int -> RawStruct ('Mut s) -> m ()
setPtr value i = setIndex @('ListNormal 'ListPtr) value i . ptrSection

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

-- | Allocate a struct in the message.
allocStruct :: M.WriteCtx m s => M.Message ('Mut s) -> Word16 -> Word16 -> m (RawStruct ('Mut s))
allocStruct msg dataSz ptrSz = do
    let totalSz = fromIntegral dataSz + fromIntegral ptrSz
    ptr <- M.alloc msg totalSz
    pure $ RawStruct ptr dataSz ptrSz

-- | Allocate a composite list.
allocCompositeList
    :: M.WriteCtx m s
    => M.Message ('Mut s) -- ^ The message to allocate in.
    -> Word16     -- ^ The size of the data section
    -> Word16     -- ^ The size of the pointer section
    -> Int        -- ^ The length of the list in elements.
    -> m (RawStructList ('Mut s))
allocCompositeList msg dataSz ptrSz len = do
    let eltSize = fromIntegral dataSz + fromIntegral ptrSz
    ptr@M.WordPtr{pSegment, pAddr=addr@WordAt{wordIndex}}
        <- M.alloc msg (WordCount $ len * eltSize + 1) -- + 1 for the tag word.
    M.write pSegment wordIndex $ P.serializePtr' $ P.StructPtr (fromIntegral len) dataSz ptrSz
    let firstStruct = RawStruct
            ptr { M.pAddr = addr { wordIndex = wordIndex + 1 } }
            dataSz
            ptrSz
    pure $ RawStructList { tag = firstStruct, len }

-- | Allocate a list of capnproto @Void@ values.
allocList0   :: M.WriteCtx m s => M.Message ('Mut s) -> Int -> m (RawNormalList ('Mut s) ('ListData 'Sz0))

-- | Allocate a list of booleans
allocList1   :: M.WriteCtx m s => M.Message ('Mut s) -> Int -> m (RawNormalList ('Mut s) ('ListData 'Sz1))

-- | Allocate a list of 8-bit values.
allocList8   :: M.WriteCtx m s => M.Message ('Mut s) -> Int -> m (RawNormalList ('Mut s) ('ListData 'Sz8))

-- | Allocate a list of 16-bit values.
allocList16  :: M.WriteCtx m s => M.Message ('Mut s) -> Int -> m (RawNormalList ('Mut s) ('ListData 'Sz16))

-- | Allocate a list of 32-bit values.
allocList32  :: M.WriteCtx m s => M.Message ('Mut s) -> Int -> m (RawNormalList ('Mut s) ('ListData 'Sz32))

-- | Allocate a list of 64-bit words.
allocList64  :: M.WriteCtx m s => M.Message ('Mut s) -> Int -> m (RawNormalList ('Mut s) ('ListData 'Sz64))

-- | Allocate a list of pointers.
allocListPtr :: M.WriteCtx m s => M.Message ('Mut s) -> Int -> m (RawNormalList ('Mut s) 'ListPtr)

allocList0   = allocNormalList 0
allocList1   = allocNormalList 1
allocList8   = allocNormalList 8
allocList16  = allocNormalList 16
allocList32  = allocNormalList 32
allocList64  = allocNormalList 64
allocListPtr = allocNormalList 64

-- | Allocate a NormalList
allocNormalList
    :: M.WriteCtx m s
    => Int                  -- ^ The number bits per element
    -> M.Message ('Mut s) -- ^ The message to allocate in
    -> Int                  -- ^ The number of elements in the list.
    -> m (RawNormalList ('Mut s) r)
allocNormalList bitsPerElt msg len = do
    -- round 'len' up to the nearest word boundary.
    let totalBits = BitCount (len * bitsPerElt)
        totalWords = bytesToWordsCeil $ bitsToBytesCeil totalBits
    ptr <- M.alloc msg totalWords
    pure RawNormalList { location = ptr, len }


appendCap :: M.WriteCtx m s => M.Message ('Mut s) -> M.Client -> m (RawCapability ('Mut s))
appendCap msg client = do
    i <- M.appendCap msg client
    pure RawCapability { msg, capIndex = fromIntegral i }

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

-- | Make the given struct the root object of its message.
setRoot :: M.WriteCtx m s => RawStruct ('Mut s) -> m ()
setRoot (RawStruct M.WordPtr{pMessage, pAddr=addr} dataSz ptrSz) = do
    pSegment <- M.getSegment pMessage 0
    let rootPtr = M.WordPtr{pMessage, pSegment, pAddr = WordAt 0 0}
    setPointerTo rootPtr addr (P.StructPtr 0 dataSz ptrSz)

-- | @'setPointerTo' msg srcLoc dstAddr relPtr@ sets the word at @srcLoc@ in @msg@ to a
-- pointer like @relPtr@, but pointing to @dstAddr@. @relPtr@ should not be a far pointer.
-- If the two addresses are in different segments, a landing pad will be allocated and
-- @srcLoc@ will contain a far pointer.
setPointerTo :: M.WriteCtx m s => M.WordPtr ('Mut s) -> WordAddr -> P.Ptr -> m ()
setPointerTo
        M.WordPtr
            { pMessage = msg
            , pSegment=srcSegment
            , pAddr=srcAddr@WordAt{wordIndex=srcWordIndex}
            }
        dstAddr
        relPtr
    | P.StructPtr _ 0 0 <- relPtr =
        -- We special case zero-sized structs, since (1) we don't have to
        -- really point at the correct offset, since they can "fit" anywhere,
        -- and (2) they cause problems with double-far pointers, where part
        -- of the landing pad needs to have a zero offset, but that makes it
        -- look like a null pointer... so we just avoid that case by cutting
        -- it off here.
        M.write srcSegment srcWordIndex $
            P.serializePtr $ Just $ P.StructPtr (-1) 0 0
    | otherwise = case pointerFrom srcAddr dstAddr relPtr of
        Right absPtr ->
            M.write srcSegment srcWordIndex $ P.serializePtr $ Just absPtr
        Left OutOfRange ->
            error "BUG: segment is too large to set the pointer."
        Left DifferentSegments -> do
            -- We need a far pointer; allocate a landing pad in the target segment,
            -- set it to point to the final destination, an then set the source pointer
            -- pointer to point to the landing pad.
            let WordAt{segIndex} = dstAddr
            M.allocInSeg msg segIndex 1 >>= \case
                Just M.WordPtr{pSegment=landingPadSegment, pAddr=landingPadAddr} ->
                    case pointerFrom landingPadAddr dstAddr relPtr of
                        Right landingPad -> do
                            let WordAt{segIndex,wordIndex} = landingPadAddr
                            M.write landingPadSegment wordIndex (P.serializePtr $ Just landingPad)
                            M.write srcSegment srcWordIndex $
                                P.serializePtr $ Just $ P.FarPtr False (fromIntegral wordIndex) (fromIntegral segIndex)
                        Left DifferentSegments ->
                            error "BUG: allocated a landing pad in the wrong segment!"
                        Left OutOfRange ->
                            error "BUG: segment is too large to set the pointer."
                Nothing -> do
                    -- The target segment is full. We need to do a double-far pointer.
                    -- First allocate the 2-word landing pad, wherever it will fit:
                    M.WordPtr
                        { pSegment = landingPadSegment
                        , pAddr = WordAt
                            { wordIndex = landingPadOffset
                            , segIndex = landingPadSegIndex
                            }
                        } <- M.alloc msg 2
                    -- Next, point the source pointer at the landing pad:
                    M.write srcSegment srcWordIndex $
                        P.serializePtr $ Just $ P.FarPtr True
                            (fromIntegral landingPadOffset)
                            (fromIntegral landingPadSegIndex)
                    -- Finally, fill in the landing pad itself.
                    --
                    -- The first word is a far pointer whose offset is the
                    -- starting address of our target object:
                    M.write landingPadSegment landingPadOffset $
                        let WordAt{wordIndex, segIndex} = dstAddr in
                        P.serializePtr $ Just $ P.FarPtr False
                            (fromIntegral wordIndex)
                            (fromIntegral segIndex)
                    -- The second word is a pointer of the right "shape"
                    -- for the target, but with a zero offset:
                    M.write landingPadSegment (landingPadOffset + 1) $
                        P.serializePtr $ Just $ case relPtr of
                            P.StructPtr _ nWords nPtrs -> P.StructPtr 0 nWords nPtrs
                            P.ListPtr _ eltSpec -> P.ListPtr 0 eltSpec
                            _ -> relPtr

--------------------------------------------------------------------

-- | Types @a@ whose storage is owned by a message..
class HasMessage a mut | a -> mut where
    -- | Get the message in which the @a@ is stored.
    message :: a -> M.Message mut

-- | Types which have a "default" value, but require a message
-- to construct it.
--
-- The default is usually conceptually zero-size. This is mostly useful
-- for generated code, so that it can use standard decoding techniques
-- on default values.
class HasMessage a mut => MessageDefault a mut where
    messageDefault :: ReadCtx m mut => M.Message mut -> m a

instance HasMessage (WordPtr mut) mut where
    message M.WordPtr{pMessage} = pMessage

instance HasMessage (RawStructList mut) mut where
    message RawStructList{tag} = message tag

instance HasMessage (RawStruct mut) mut where
    message RawStruct{location} = message location

instance HasMessage (RawNormalList mut r) mut where
    message RawNormalList{location} = message location

instance HasMessage (RawAnyPointer mut) mut where
    message (RawAnyPointer'Struct p)     = message p
    message (RawAnyPointer'Capability p) = message p
    message (RawAnyPointer'List p)       = message p

instance HasMessage (RawAnyList mut) mut where
    message (RawAnyList'Struct l) = message l
    message (RawAnyList'Normal l) = message l

instance HasMessage (RawAnyNormalList mut) mut where
    message (RawAnyNormalList'Ptr l)  = message l
    message (RawAnyNormalList'Data l) = message l

instance HasMessage (RawAnyDataList mut) mut where
    message (RawAnyDataList _ l) = message l

instance HasMessage (RawCapability mut) mut where
    message RawCapability{msg} = msg

instance MessageDefault (M.WordPtr mut) mut where
    messageDefault msg = do
        pSegment <- M.getSegment msg 0
        pure M.WordPtr{pMessage = msg, pSegment, pAddr = WordAt 0 0}

instance MessageDefault (RawStructList mut) mut where
    messageDefault msg = do
        tag <- messageDefault msg
        pure RawStructList {tag, len = 0}

instance MessageDefault (RawStruct mut) mut where
    messageDefault msg = do
        location <- messageDefault msg
        pure $ RawStruct location 0 0

instance MessageDefault (RawNormalList mut r) mut where
    messageDefault msg = do
        location <- messageDefault msg
        pure RawNormalList{location, len = 0}


-------------------------------------------------------------------------------
-- Copying data from one message to another
-------------------------------------------------------------------------------

copyCap :: RWCtx m s => M.Message ('Mut s) -> RawCapability ('Mut s) -> m (RawCapability ('Mut s))
copyCap dest cap = getClient cap >>= appendCap dest

copyPtr :: RWCtx m s => M.Message ('Mut s) -> Maybe (RawAnyPointer ('Mut s)) -> m (Maybe (RawAnyPointer ('Mut s)))
copyPtr _ Nothing                = pure Nothing
copyPtr dest (Just (RawAnyPointer'Capability cap)) =
    Just . RawAnyPointer'Capability <$> copyCap dest cap
copyPtr dest (Just (RawAnyPointer'List src)) =
    Just . RawAnyPointer'List <$> copyList dest src
copyPtr dest (Just (RawAnyPointer'Struct src)) = Just . RawAnyPointer'Struct <$> do
    destStruct <- allocStruct
            dest
            (fromIntegral $ structWordCount src)
            (fromIntegral $ structPtrCount src)
    copyStruct destStruct src
    pure destStruct

copyList :: RWCtx m s => M.Message ('Mut s) -> RawAnyList ('Mut s) -> m (RawAnyList ('Mut s))
copyList dest src = case src of
    RawAnyList'Struct src -> RawAnyList'Struct <$> do
        destList <- allocCompositeList
            dest
            (fromIntegral $ structListWordCount src)
            (structListPtrCount src)
            (length @'ListComposite src)
        copyListOf @'ListComposite destList src
        pure destList
    RawAnyList'Normal src -> RawAnyList'Normal <$> case src of
        RawAnyNormalList'Data src ->
            RawAnyNormalList'Data <$> case src of
                RawAnyDataList D0 src ->
                    RawAnyDataList D0 <$> allocList0 dest (length @(DL 'Sz0) src)
                RawAnyDataList D1 src ->
                    RawAnyDataList D1 <$> allocList1 dest (length @(DL 'Sz1) src)
                RawAnyDataList D8 src ->
                    RawAnyDataList D8 <$> allocList8 dest (length @(DL 'Sz8) src)
                RawAnyDataList D16 src ->
                    RawAnyDataList D16 <$> allocList16 dest (length @(DL 'Sz16) src)
                RawAnyDataList D32 src ->
                    RawAnyDataList D32 <$> allocList32 dest (length @(DL 'Sz32) src)
                RawAnyDataList D64 src ->
                    RawAnyDataList D64 <$> allocList64 dest (length @(DL 'Sz64) src)
        RawAnyNormalList'Ptr src ->
            RawAnyNormalList'Ptr <$> copyNewListOf @('ListNormal 'ListPtr) dest src allocListPtr

type DL r = 'ListNormal ('ListData r)

copyNewListOf
    :: forall r m s. (RWCtx m s, List r)
    => M.Message ('Mut s)
    -> RawSomeList ('Mut s) r
    -> (M.Message ('Mut s) -> Int -> m (RawSomeList ('Mut s) r))
    -> m (RawSomeList ('Mut s) r)
copyNewListOf destMsg src new = do
    dest <- new destMsg (length @r @('Mut s) src)
    copyListOf @r dest src
    pure dest

copyListOf :: forall r m s. (RWCtx m s, List r) => RawSomeList ('Mut s) r -> RawSomeList ('Mut s) r -> m ()
copyListOf dest src =
    for_ [0..length @r @('Mut s) src - 1] $ \i -> do
        value <- index @r @('Mut s) i src
        setIndex @r value i dest

-- | @'copyStruct' dest src@ copies the source struct to the destination struct.
copyStruct :: forall m s. RWCtx m s => RawStruct ('Mut s) -> RawStruct ('Mut s) -> m ()
copyStruct dest src = do
    -- We copy both the data and pointer sections from src to dest,
    -- padding the tail of the destination section with zeros/null
    -- pointers as necessary. If the destination section is
    -- smaller than the source section, this will raise a BoundsError.
    --
    -- TODO: possible enhancement: allow the destination section to be
    -- smaller than the source section if and only if the tail of the
    -- source section is all zeros (default values).
    copySection @('ListNormal ('ListData 'Sz64))
        (dataSection dest)
        (dataSection src)
        0
    copySection @('ListNormal 'ListPtr)
        (ptrSection  dest)
        (ptrSection  src)
        (Nothing @(RawAnyPointer ('Mut s)))
  where
    copySection
        :: forall r. List r
        => RawSomeList ('Mut s) r
        -> RawSomeList ('Mut s) r
        -> Raw ('Mut s) (ElemRepr r)
        -> m ()
    copySection dest src pad = do
        -- Copy the source section to the destination section:
        copyListOf @r dest src
        -- Pad the remainder with zeros/default values:
        for_ [length @r @('Mut s) src..length @r @('Mut s) dest - 1] $ \i ->
            setIndex @r pad i dest
