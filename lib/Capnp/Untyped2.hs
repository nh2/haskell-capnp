{-# LANGUAGE ApplicativeDo         #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecordWildCards       #-}
{-# LANGUAGE TypeFamilies          #-}
{-|
Module: Capnp.Untyped
Description: Utilities for reading capnproto messages with no schema.

The types and functions in this module know about things like structs and
lists, but are not schema aware.

Each of the data types exported by this module is parametrized over a Message
type (see "Capnp.Message"), used as the underlying storage.
-}
module Capnp.Untyped2
    ( Ptr(..), List(..), Struct, ListOf, Cap
    , structByteCount
    , structWordCount
    , structPtrCount
    , structListByteCount
    , structListWordCount
    , structListPtrCount
    , getData, getPtr
    , setData, setPtr
    , copyStruct
    , getClient
    , get, index, length
    , setIndex
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
    )
  where

import Prelude hiding (length)

import Data.Bits
import Data.Word

import Control.Monad       (forM_)
import Control.Monad.Catch (MonadThrow(throwM))

import qualified Data.ByteString as BS

import Capnp.Address        (OffsetError(..), WordAddr(..), pointerFrom)
import Capnp.Bits
    ( BitCount(..)
    , ByteCount(..)
    , Word1(..)
    , WordCount(..)
    , bitsToBytesCeil
    , bytesToWordsCeil
    , replaceBits
    , wordsToBytes
    )
import Capnp.Message2       (TraverseMsg(..))
import Capnp.Mutability     (Mutability(..), Phantom(..))
import Capnp.Parsable       (Parsable(..), ReadCtx)
import Capnp.Pointer        (ElementSize(..))
import Capnp.TraversalLimit (MonadLimit(invoice))

import qualified Capnp.Errors   as E
import qualified Capnp.Message2 as M
import qualified Capnp.Pointer  as P

-- | Synonym for ReadCtx + WriteCtx
type RWCtx m s = (ReadCtx m ('Mut s), M.WriteCtx m s)

-- | A an absolute pointer to a value (of arbitrary type) in a message.
-- Note that there is no variant for far pointers, which don't make sense
-- with absolute addressing.
data Ptr mut
    = PtrCap (Cap mut)
    | PtrList (List mut)
    | PtrStruct (Struct mut)

newtype MaybePtr mut = MaybePtr { unwrapPtr :: Maybe (Ptr mut) }

data DataListOf a mut = DataListOf (ListSz a) (NormalList mut)

data ListSz a where
    SZ0  :: ListSz ()
    SZ1  :: ListSz Bool
    SZ8  :: ListSz Word8
    SZ16 :: ListSz Word16
    SZ32 :: ListSz Word32
    SZ64 :: ListSz Word64

bitsPerElt :: ListSz a -> BitCount
bitsPerElt = \case
    SZ0 -> 0
    SZ1 -> 1
    SZ8 -> 8
    SZ16 -> 16
    SZ32 -> 32
    SZ64 -> 64

data ListOf (f :: Mutability -> *) (mut :: Mutability) where
    ListOf_Data :: DataListOf a mut -> ListOf (Phantom a) mut
    ListOf_Ptr :: PtrListOf f mut -> ListOf f mut

-- | A list of values (of arbitrary type) in a message.
data List mut
    = List0 (ListOf (Phantom ()) mut)
    | List1 (ListOf (Phantom Bool) mut)
    | List8 (ListOf (Phantom Word8) mut)
    | List16 (ListOf (Phantom Word16) mut)
    | List32 (ListOf (Phantom Word32) mut)
    | List64 (ListOf (Phantom Word64) mut)
    | ListPtr (ListOf MaybePtr mut)
    | ListStruct (ListOf Struct mut)

-- | A "normal" (non-composite) list.
data NormalList mut = NormalList
    { nMsg  :: M.Msg mut
    , nAddr :: WordAddr
    , nLen  :: Int
    }

-- | A list of values of type 'f' in a message.
data PtrListOf f mut where
    ListOfPtr :: !(NormalList mut) -> PtrListOf MaybePtr mut
    ListOfStruct
        :: Struct mut -- First element. data/ptr sizes are the same for
                      -- all elements.
        -> !Int       -- Number of elements
        -> PtrListOf Struct mut

-- | A Capability in a message.
data Cap mut = Cap' (M.Msg mut) !Word32

instance Parsable Cap where
    data Parsed Cap = Cap M.Client

    decode = fmap Cap . getClient
    encode msg (Cap client) = appendCap msg client

-- | A struct value in a message.
data Struct mut
    = Struct'
        (M.Msg mut)
        !WordAddr -- Start of struct
        !Word16 -- Data section size.
        !Word16 -- Pointer section size.

{-
instance Parseable Struct where
    data Parsed Struct = Struct
        { structData :: Parsed (ListOf (Phantom Word64))
        , structPtrs :: Parsed (ListOf MaybePtr)
        }
-}

-- Boilerplate instances:
instance TraverseMsg MaybePtr where
    tMsg f (MaybePtr mp) = MaybePtr <$> traverse (tMsg f) mp
instance TraverseMsg Ptr where
    tMsg f = \case
        PtrCap cap ->
            PtrCap <$> tMsg f cap
        PtrList l ->
            PtrList <$> tMsg f l
        PtrStruct s ->
            PtrStruct <$> tMsg f s
instance TraverseMsg Cap where
    tMsg f (Cap' msg n) = Cap' <$> f msg <*> pure n
instance TraverseMsg Struct where
    tMsg f (Struct' msg addr dataSz ptrSz) = Struct'
        <$> f msg
        <*> pure addr
        <*> pure dataSz
        <*> pure ptrSz
instance TraverseMsg List where
    tMsg f = \case
        List0      l -> List0      <$> tMsg f l
        List1      l -> List1      <$> tMsg f l
        List8      l -> List8      <$> tMsg f l
        List16     l -> List16     <$> tMsg f l
        List32     l -> List32     <$> tMsg f l
        List64     l -> List64     <$> tMsg f l
        ListPtr    l -> ListPtr    <$> tMsg f l
        ListStruct l -> ListStruct <$> tMsg f l
instance TraverseMsg (ListOf f) where
    tMsg f = \case
        ListOf_Data l -> ListOf_Data <$> tMsg f l
        ListOf_Ptr l -> ListOf_Ptr <$> tMsg f l
instance TraverseMsg (DataListOf a) where
    tMsg f (DataListOf sz l) = DataListOf sz <$> tMsg f l
instance TraverseMsg (PtrListOf f) where
    tMsg f (ListOfPtr l)        = ListOfPtr <$> tMsg f l
    tMsg f (ListOfStruct s len) = (`ListOfStruct` len) <$> tMsg f s
instance TraverseMsg NormalList where
    tMsg f NormalList{..} = do
        msg <- f nMsg
        pure NormalList { nMsg = msg, .. }

-------------------------------------------------------------------------------

-- | Types @a@ whose storage is owned by a message..
class HasMessage (f :: Mutability -> *) where
    -- | Get the message in which the @a@ is stored.
    message :: f mut -> M.Msg mut

-- | Types which have a "default" value, but require a message
-- to construct it.
--
-- The default is usually conceptually zero-size. This is mostly useful
-- for generated code, so that it can use standard decoding techniques
-- on default values.
class HasMessage f => MessageDefault f where
    messageDefault :: M.Msg mut -> f mut

instance HasMessage Ptr where
    message (PtrCap cap)       = message cap
    message (PtrList list)     = message list
    message (PtrStruct struct) = message struct

instance HasMessage Cap where
    message (Cap' msg _) = msg

instance HasMessage Struct where
    message (Struct' msg _ _ _) = msg

instance MessageDefault Struct where
    messageDefault msg = Struct' msg (WordAt 0 0) 0 0

instance HasMessage List where
    message (List0 list)      = message list
    message (List1 list)      = message list
    message (List8 list)      = message list
    message (List16 list)     = message list
    message (List32 list)     = message list
    message (List64 list)     = message list
    message (ListPtr list)    = message list
    message (ListStruct list) = message list

instance HasMessage (ListOf f) where
    message (ListOf_Data l) = message l
    message (ListOf_Ptr l)  = message l

instance HasMessage (DataListOf a) where
    message (DataListOf _ nl) = message nl

instance HasMessage (PtrListOf f) where
    message (ListOfStruct tag _) = message tag
    message (ListOfPtr list)     = message list

instance MessageDefault (DataListOf ()) where
    messageDefault = dataMsgDefault SZ0
instance MessageDefault (DataListOf Bool) where
    messageDefault = dataMsgDefault SZ1
instance MessageDefault (DataListOf Word8) where
    messageDefault = dataMsgDefault SZ8
instance MessageDefault (DataListOf Word16) where
    messageDefault = dataMsgDefault SZ16
instance MessageDefault (DataListOf Word32) where
    messageDefault = dataMsgDefault SZ32
instance MessageDefault (DataListOf Word64) where
    messageDefault = dataMsgDefault SZ64

dataMsgDefault :: ListSz a -> M.Msg mut -> DataListOf a mut
dataMsgDefault sz msg = DataListOf sz (messageDefault msg)

instance MessageDefault (PtrListOf Struct) where
    messageDefault msg =
        -- XXX TODO: make sure this is right; we might need to do something
        -- other than pass through to Struct's instance; IIRC there's something
        -- special about what the offset field means in a list?
        ListOfStruct (messageDefault msg) 0

instance HasMessage NormalList where
    message = nMsg

instance MessageDefault NormalList where
    messageDefault msg = NormalList msg (WordAt 0 0) 0

getClient :: ReadCtx m mut => Cap mut -> m M.Client
getClient (Cap' msg idx) = M.getCap msg (fromIntegral idx)

-- | @get msg addr@ returns the Ptr stored at @addr@ in @msg@.
-- Deducts 1 from the quota for each word read (which may be multiple in the
-- case of far pointers).
get :: ReadCtx m mut => M.Msg mut -> WordAddr -> m (MaybePtr mut)
get msg addr = do
    word <- getWord msg addr
    case P.parsePtr word of
        Nothing -> return $ MaybePtr Nothing
        Just p -> case p of
            P.CapPtr cap -> return $ MaybePtr $ Just $ PtrCap (Cap' msg cap)
            P.StructPtr off dataSz ptrSz -> return $ MaybePtr $ Just $ PtrStruct $
                Struct' msg (resolveOffset addr off) dataSz ptrSz
            P.ListPtr off eltSpec -> MaybePtr . Just <$> getList (resolveOffset addr off) eltSpec
            P.FarPtr twoWords offset segment -> do
                let addr' = WordAt { wordIndex = fromIntegral offset
                                   , segIndex = fromIntegral segment
                                   }
                if not twoWords
                    then get msg addr'
                    else do
                        landingPad <- getWord msg addr'
                        case P.parsePtr landingPad of
                            Just (P.FarPtr False off seg) -> do
                                tagWord <- getWord
                                            msg
                                            addr' { wordIndex = wordIndex addr' + 1 }
                                let finalAddr = WordAt { wordIndex = fromIntegral off
                                                       , segIndex = fromIntegral seg
                                                       }
                                case P.parsePtr tagWord of
                                    Just (P.StructPtr 0 dataSz ptrSz) ->
                                        return $ MaybePtr $ Just $ PtrStruct $
                                            Struct' msg finalAddr dataSz ptrSz
                                    Just (P.ListPtr 0 eltSpec) ->
                                        MaybePtr . Just <$> getList finalAddr eltSpec
                                    -- TODO: I'm not sure whether far pointers to caps are
                                    -- legal; it's clear how they would work, but I don't
                                    -- see a use, and the spec is unclear. Should check
                                    -- how the reference implementation does this, copy
                                    -- that, and submit a patch to the spec.
                                    Just (P.CapPtr cap) ->
                                        return $ MaybePtr $ Just $ PtrCap (Cap' msg cap)
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
    getWord msg addr = invoice 1 *> M.getWord msg addr
    resolveOffset addr@WordAt{..} off =
        addr { wordIndex = wordIndex + fromIntegral off + 1 }
    getList addr@WordAt{..} eltSpec = PtrList <$>
        case eltSpec of
            P.EltNormal sz len -> pure $ case sz of
                Sz0   -> List0  (ListOf_Data (DataListOf SZ0 nlist))
                Sz1   -> List1  (ListOf_Data (DataListOf SZ1 nlist))
                Sz8   -> List8  (ListOf_Data (DataListOf SZ8 nlist))
                Sz16  -> List16 (ListOf_Data (DataListOf SZ16 nlist))
                Sz32  -> List32 (ListOf_Data (DataListOf SZ32 nlist))
                Sz64  -> List64 (ListOf_Data (DataListOf SZ64 nlist))
                SzPtr -> ListPtr (ListOf_Ptr (ListOfPtr nlist))
              where
                nlist = NormalList msg addr (fromIntegral len)
            P.EltComposite _ -> do
                tagWord <- getWord msg addr
                case P.parsePtr' tagWord of
                    P.StructPtr numElts dataSz ptrSz ->
                        pure $ ListStruct $ ListOf_Ptr $ ListOfStruct
                            (Struct' msg
                                    addr { wordIndex = wordIndex + 1 }
                                    dataSz
                                    ptrSz)
                            (fromIntegral numElts)
                    tag -> throwM $ E.InvalidDataError $
                        "Composite list tag was not a struct-" ++
                        "formatted word: " ++ show tag

-- | Return the EltSpec needed for a pointer to the given list.
listEltSpec :: List msg -> P.EltSpec
listEltSpec (ListStruct list@(ListOf_Ptr (ListOfStruct (Struct' _ _ dataSz ptrSz) _))) =
    P.EltComposite $ fromIntegral (length list) * (fromIntegral dataSz + fromIntegral ptrSz)
listEltSpec (List0 list)   = P.EltNormal Sz0 $ fromIntegral (length list)
listEltSpec (List1 list)   = P.EltNormal Sz1 $ fromIntegral (length list)
listEltSpec (List8 list)   = P.EltNormal Sz8 $ fromIntegral (length list)
listEltSpec (List16 list)  = P.EltNormal Sz16 $ fromIntegral (length list)
listEltSpec (List32 list)  = P.EltNormal Sz32 $ fromIntegral (length list)
listEltSpec (List64 list)  = P.EltNormal Sz64 $ fromIntegral (length list)
listEltSpec (ListPtr list) = P.EltNormal SzPtr $ fromIntegral (length list)


-- | Return the starting address of the list.
listAddr :: List msg -> WordAddr
listAddr = \case
    ListStruct (ListOf_Ptr (ListOfStruct (Struct' _ addr _ _) _)) ->
        -- addr is the address of the first element of the list, but
        -- composite lists start with a tag word:
        addr { wordIndex = wordIndex addr - 1 }
    List0 l -> dataListAddr l
    List1 l -> dataListAddr l
    List8 l -> dataListAddr l
    List16 l -> dataListAddr l
    List32 l -> dataListAddr l
    List64 l -> dataListAddr l
    ListPtr (ListOf_Ptr (ListOfPtr NormalList{nAddr})) -> nAddr
  where
    dataListAddr :: ListOf (Phantom a) mut -> WordAddr
    dataListAddr (ListOf_Data (DataListOf _ NormalList{nAddr})) = nAddr
    dataListAddr _ = error "Impossible"

-- | Return the address of the pointer's target. It is illegal to call this on
-- a pointer which targets a capability.
ptrAddr :: Ptr msg -> WordAddr
ptrAddr (PtrCap _) = error "ptrAddr called on a capability pointer."
ptrAddr (PtrStruct (Struct' _ addr _ _)) = addr
ptrAddr (PtrList list) = listAddr list

-- | @'setIndex value i list@ Set the @i@th element of @list@ to @value@.
setIndex :: RWCtx m s => f ('Mut s) -> Int -> ListOf f ('Mut s) -> m ()
setIndex _ i list | length list <= i =
    throwM E.BoundsError { E.index = i, E.maxIndex = length list }
setIndex value i list = case list of
    ListOf_Data (DataListOf sz nlist) ->
        let v = unPhantom value in
        case sz of
            SZ0  -> pure ()
            SZ1  -> setNIndex nlist 64 (Word1 v)
            SZ8  -> setNIndex nlist 8 v
            SZ16 -> setNIndex nlist 4 v
            SZ32 -> setNIndex nlist 2 v
            SZ64 -> setNIndex nlist 1 v
    ListOf_Ptr (ListOfPtr nlist) -> case unwrapPtr value of
        Just p | message p /= message list -> do
            newPtr <- copyPtr (message list) value
            setIndex newPtr i list
        Nothing                -> setNIndex nlist 1 (P.serializePtr Nothing)
        Just (PtrCap (Cap' _ cap))    -> setNIndex nlist 1 (P.serializePtr (Just (P.CapPtr cap)))
        Just p@(PtrList ptrList)     ->
            setPtrIndex nlist p $ P.ListPtr 0 (listEltSpec ptrList)
        Just p@(PtrStruct (Struct' _ _ dataSz ptrSz)) ->
            setPtrIndex nlist p $ P.StructPtr 0 dataSz ptrSz
    ListOf_Ptr (ListOfStruct _ _) -> do
        dest <- index i list
        copyStruct dest value
  where
    setNIndex :: (RWCtx m s, Bounded a, Integral a) => NormalList ('Mut s) -> Int -> a -> m ()
    setNIndex NormalList{nAddr=nAddr@WordAt{..},..} eltsPerWord value = do
        let wordAddr = nAddr { wordIndex = wordIndex + WordCount (i `div` eltsPerWord) }
        word <- M.getWord nMsg wordAddr
        let shift = (i `mod` eltsPerWord) * (64 `div` eltsPerWord)
        M.setWord nMsg wordAddr $ replaceBits value word shift
    setPtrIndex :: RWCtx m s => NormalList ('Mut s) -> Ptr ('Mut s) -> P.Ptr -> m ()
    setPtrIndex NormalList{..} absPtr relPtr =
        let srcAddr = nAddr { wordIndex = wordIndex nAddr + WordCount i }
        in setPointerTo nMsg srcAddr (ptrAddr absPtr) relPtr

-- | @'setPointerTo' msg srcAddr dstAddr relPtr@ sets the word at @srcAddr@ in @msg@ to a
-- pointer like @relPtr@, but pointing to @dstAddr@. @relPtr@ should not be a far pointer.
-- If the two addresses are in different segments, a landing pad will be allocated and
-- @dstAddr@ will contain a far pointer.
setPointerTo :: M.WriteCtx m s => M.Msg ('Mut s) -> WordAddr -> WordAddr -> P.Ptr -> m ()
setPointerTo msg srcAddr dstAddr relPtr =
    case pointerFrom srcAddr dstAddr relPtr of
        Right absPtr ->
            M.setWord msg srcAddr (P.serializePtr $ Just absPtr)
        Left OutOfRange ->
            error "BUG: segment is too large to set the pointer."
        Left DifferentSegments -> do
            -- We need a far pointer; allocate a landing pad in the target segment,
            -- set it to point to the final destination, an then set the source pointer
            -- pointer to point to the landing pad.
            let WordAt{segIndex} = dstAddr
            landingPadAddr <- M.allocInSeg msg segIndex 1
            case pointerFrom landingPadAddr dstAddr relPtr of
                Right landingPad -> do
                    M.setWord msg landingPadAddr (P.serializePtr $ Just landingPad)
                    let WordAt{segIndex,wordIndex} = landingPadAddr
                    M.setWord msg srcAddr $
                        P.serializePtr $ Just $ P.FarPtr False (fromIntegral wordIndex) (fromIntegral segIndex)
                Left DifferentSegments ->
                    error "BUG: allocated a landing pad in the wrong segment!"
                Left OutOfRange ->
                    error "BUG: segment is too large to set the pointer."

copyCap :: RWCtx m s => M.Msg ('Mut s) -> Cap ('Mut s) -> m (Cap ('Mut s))
copyCap dest cap = getClient cap >>= appendCap dest

copyPtr :: RWCtx m s => M.Msg ('Mut s) -> MaybePtr ('Mut s) -> m (MaybePtr ('Mut s))
copyPtr dest (MaybePtr p) = case p of
    Nothing            -> pure $ MaybePtr Nothing
    Just (PtrCap cap)  -> MaybePtr . Just . PtrCap <$> copyCap dest cap
    Just (PtrList src) -> MaybePtr . Just . PtrList <$> copyList dest src
    Just (PtrStruct src) -> MaybePtr . Just . PtrStruct <$> do
        destStruct <- allocStruct
                dest
                (fromIntegral $ structWordCount src)
                (fromIntegral $ structPtrCount src)
        copyStruct destStruct src
        pure destStruct

copyList :: RWCtx m s => M.Msg ('Mut s) -> List ('Mut s) -> m (List ('Mut s))
copyList dest src = case src of
    List0 src      -> List0 <$> allocList0 dest (length src)
    List1 src      -> List1 <$> copyNewListOf dest src allocList1
    List8 src      -> List8 <$> copyNewListOf dest src allocList8
    List16 src     -> List16 <$> copyNewListOf dest src allocList16
    List32 src     -> List32 <$> copyNewListOf dest src allocList32
    List64 src     -> List64 <$> copyNewListOf dest src allocList64
    ListPtr src    -> ListPtr <$> copyNewListOf dest src allocListPtr
    ListStruct src -> ListStruct <$> do
        destList <- ListOf_Ptr <$> allocCompositeList
            dest
            (fromIntegral $ structListWordCount src)
            (structListPtrCount src)
            (length src)
        copyListOf destList src
        pure destList

copyNewListOf
    :: RWCtx m s
    => M.Msg ('Mut s)
    -> ListOf f ('Mut s)
    -> (M.Msg ('Mut s) -> Int -> m (ListOf f ('Mut s)))
    -> m (ListOf f ('Mut s))
copyNewListOf destMsg src new = do
    dest <- new destMsg (length src)
    copyListOf dest src
    pure dest


copyListOf :: RWCtx m s => ListOf f ('Mut s) -> ListOf f ('Mut s) -> m ()
copyListOf dest src =
    forM_ [0..length src - 1] $ \i -> do
        value <- index i src
        setIndex value i dest

-- | @'copyStruct' dest src@ copies the source struct to the destination struct.
copyStruct :: RWCtx m s => Struct ('Mut s) -> Struct ('Mut s) -> m ()
copyStruct dest src = do
    -- We copy both the data and pointer sections from src to dest,
    -- padding the tail of the destination section with zeros/null
    -- pointers as necessary. If the destination section is
    -- smaller than the source section, this will raise a BoundsError.
    --
    -- TODO: possible enhancement: allow the destination section to be
    -- smaller than the source section if and only if the tail of the
    -- source section is all zeros (default values).
    copySection (dataSection dest) (dataSection src) 0
    copySection (ptrSection  dest) (ptrSection  src) (MaybePtr Nothing)
  where
    copySection dest src pad = do
        -- Copy the source section to the destination section:
        copyListOf dest src
        -- Pad the remainder with zeros/default values:
        forM_ [length src..length dest - 1] $ \i ->
            setIndex pad i dest


-- | @index i list@ returns the ith element in @list@. Deducts 1 from the quota
index :: ReadCtx m mut => Int -> ListOf f mut -> m (f mut)
index i list = invoice 1 >> index' list
  where
    index' :: ReadCtx m mut => ListOf f mut -> m (f mut)
    index' (ListOf_Data (DataListOf SZ0 NormalList{nLen = len}))
        | i < len = pure $ Phantom ()
        | otherwise = throwM E.BoundsError { E.index = i, E.maxIndex = len - 1 }
    index' (ListOf_Data (DataListOf SZ1 nlist)) = do
        Phantom (Word1 val) <- indexNList nlist 64
        pure $ Phantom val
    index' (ListOf_Data (DataListOf SZ8  nlist)) = indexNList nlist 8
    index' (ListOf_Data (DataListOf SZ16 nlist)) = indexNList nlist 4
    index' (ListOf_Data (DataListOf SZ32 nlist)) = indexNList nlist 2
    index' (ListOf_Data (DataListOf SZ64 nlist)) = indexNList nlist 1
    index' (ListOf_Ptr (ListOfStruct (Struct' msg addr@WordAt{..} dataSz ptrSz) len))
        | i < len = do
            let offset = WordCount $ i * (fromIntegral dataSz + fromIntegral ptrSz)
            let addr' = addr { wordIndex = wordIndex + offset }
            return $ Struct' msg addr' dataSz ptrSz
        | otherwise = throwM E.BoundsError { E.index = i, E.maxIndex = len - 1}
    index' (ListOf_Ptr (ListOfPtr (NormalList msg addr@WordAt{..} len)))
        | i < len = get msg addr { wordIndex = wordIndex + WordCount i }
        | otherwise = throwM E.BoundsError { E.index = i, E.maxIndex = len - 1}
    indexNList :: (ReadCtx m mut, Integral a) => NormalList mut -> Int -> m (Phantom a mut)
    indexNList (NormalList msg addr@WordAt{..} len) eltsPerWord
        | i < len = do
            let wordIndex' = wordIndex + WordCount (i `div` eltsPerWord)
            word <- M.getWord msg addr { wordIndex = wordIndex' }
            let shift = (i `mod` eltsPerWord) * (64 `div` eltsPerWord)
            pure $ Phantom $ fromIntegral $ word `shiftR` shift
        | otherwise = throwM E.BoundsError { E.index = i, E.maxIndex = len - 1 }

-- | Returns the length of a list
length :: ListOf msg a -> Int
length (ListOf_Data (DataListOf _ NormalList{nLen})) = nLen
length (ListOf_Ptr (ListOfPtr NormalList{nLen}))     = nLen
length (ListOf_Ptr (ListOfStruct _ len))             = len

-- | The data section of a struct, as a list of Word64
dataSection :: Struct mut -> ListOf (Phantom Word64) mut
dataSection (Struct' msg addr dataSz _) =
    ListOf_Data $ DataListOf SZ64 $ NormalList msg addr (fromIntegral dataSz)

-- | The pointer section of a struct, as a list of Ptr
ptrSection :: Struct mut -> ListOf MaybePtr mut
ptrSection (Struct' msg addr@WordAt{..} dataSz ptrSz) =
    ListOf_Ptr $ ListOfPtr $ NormalList
        msg
        addr { wordIndex = wordIndex + fromIntegral dataSz }
        (fromIntegral ptrSz)

-- | Get the size (in words) of a struct's data section.
structWordCount :: Struct mut -> WordCount
structWordCount (Struct' _msg _addr dataSz _ptrSz) = fromIntegral dataSz

-- | Get the size (in bytes) of a struct's data section.
structByteCount :: Struct mut -> ByteCount
structByteCount = wordsToBytes . structWordCount

-- | Get the size of a struct's pointer section.
structPtrCount  :: Struct mut -> Word16
structPtrCount (Struct' _msg _addr _dataSz ptrSz) = ptrSz

-- | Get the size (in words) of the data sections in a struct list.
structListWordCount :: ListOf Struct mut -> WordCount
structListWordCount (ListOf_Ptr (ListOfStruct s _)) = structWordCount s

-- | Get the size (in bytes) of the data sections in a struct list.
structListByteCount :: ListOf Struct mut -> ByteCount
structListByteCount (ListOf_Ptr (ListOfStruct s _)) = structByteCount s

-- | Get the size of the pointer sections in a struct list.
structListPtrCount :: ListOf Struct mut -> Word16
structListPtrCount (ListOf_Ptr (ListOfStruct s _)) = structPtrCount s

-- | @'getData' i struct@ gets the @i@th word from the struct's data section,
-- returning 0 if it is absent.
getData :: ReadCtx m mut => Int -> Struct mut -> m Word64
getData i struct
    | fromIntegral (structWordCount struct) <= i = 0 <$ invoice 1
    | otherwise = unPhantom <$> index i (dataSection struct)

-- | @'getPtr' i struct@ gets the @i@th word from the struct's pointer section,
-- returning Nothing if it is absent.
getPtr :: ReadCtx m mut => Int -> Struct mut -> m (MaybePtr mut)
getPtr i struct
    | fromIntegral (structPtrCount struct) <= i = MaybePtr Nothing <$ invoice 1
    | otherwise = index i (ptrSection struct)

-- | @'setData' value i struct@ sets the @i@th word in the struct's data section
-- to @value@.
setData :: (ReadCtx m ('Mut s), M.WriteCtx m s)
    => Word64 -> Int -> Struct ('Mut s) -> m ()
setData value i = setIndex (Phantom value) i . dataSection

-- | @'setData' value i struct@ sets the @i@th pointer in the struct's pointer
-- section to @value@.
setPtr :: (ReadCtx m ('Mut s), M.WriteCtx m s) => MaybePtr ('Mut s) -> Int -> Struct ('Mut s) -> m ()
setPtr value i = setIndex value i . ptrSection

-- | 'rawBytes' returns the raw bytes corresponding to the list.
rawBytes :: ReadCtx m mut => DataListOf Word8 mut -> m BS.ByteString
rawBytes (DataListOf SZ8 (NormalList msg WordAt{..} len)) = do
    invoice $ fromIntegral $ bytesToWordsCeil (ByteCount len)
    bytes <- M.getSegment msg segIndex >>= M.toByteString
    let ByteCount byteOffset = wordsToBytes wordIndex
    pure $ BS.take len $ BS.drop byteOffset bytes


-- | Returns the root pointer of a message.
rootPtr :: ReadCtx m mut => M.Msg mut -> m (Struct mut)
rootPtr msg = do
    root <- get msg (WordAt 0 0)
    case unwrapPtr root of
        Just (PtrStruct struct) -> pure struct
        Nothing -> pure (messageDefault msg)
        _ -> throwM $ E.SchemaViolationError
                "Unexpected root type; expected struct."


-- | Make the given struct the root object of its message.
setRoot :: M.WriteCtx m s => Struct ('Mut s) -> m ()
setRoot (Struct' msg addr dataSz ptrSz) =
    setPointerTo msg (WordAt 0 0) addr (P.StructPtr 0 dataSz ptrSz)

-- | Allocate a struct in the message.
allocStruct :: M.WriteCtx m s => M.Msg ('Mut s) -> Word16 -> Word16 -> m (Struct ('Mut s))
allocStruct msg dataSz ptrSz = do
    let totalSz = fromIntegral dataSz + fromIntegral ptrSz
    addr <- M.alloc msg totalSz
    pure $ Struct' msg addr dataSz ptrSz

-- | Allocate a composite list.
allocCompositeList
    :: M.WriteCtx m s
    => M.Msg ('Mut s) -- ^ The message to allocate in.
    -> Word16     -- ^ The size of the data sections
    -> Word16     -- ^ The size of the pointer sections
    -> Int        -- ^ The length of the list in elements.
    -> m (PtrListOf Struct ('Mut s))
allocCompositeList msg dataSz ptrSz len = do
    let eltSize = fromIntegral dataSz + fromIntegral ptrSz
    addr <- M.alloc msg (WordCount $ len * eltSize + 1) -- + 1 for the tag word.
    M.setWord msg addr $ P.serializePtr' $ P.StructPtr (fromIntegral len) dataSz ptrSz
    let firstStruct = Struct'
            msg
            addr { wordIndex = wordIndex addr + 1 }
            dataSz
            ptrSz
    pure $ ListOfStruct firstStruct len

-- | Allocate a list of capnproto @Void@ values.
allocList0   :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (ListOf (Phantom ()) ('Mut s))

-- | Allocate a list of booleans
allocList1   :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (ListOf (Phantom Bool) ('Mut s))

-- | Allocate a list of 8-bit values.
allocList8   :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (ListOf (Phantom Word8) ('Mut s))

-- | Allocate a list of 16-bit values.
allocList16  :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (ListOf (Phantom Word16) ('Mut s))

-- | Allocate a list of 32-bit values.
allocList32  :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (ListOf (Phantom Word32) ('Mut s))

-- | Allocate a list of 64-bit words.
allocList64  :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (ListOf (Phantom Word64) ('Mut s))

-- | Allocate a list of pointers.
allocListPtr :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (ListOf MaybePtr ('Mut s))

allocDataList :: M.WriteCtx m s => ListSz a -> M.Msg ('Mut s) -> Int -> m (ListOf (Phantom a) ('Mut s))
allocDataList sz msg len =
    ListOf_Data . DataListOf sz <$> allocNormalList (bitsPerElt sz) msg len

allocList0   = allocDataList SZ0
allocList1   = allocDataList SZ1
allocList8   = allocDataList SZ8
allocList16  = allocDataList SZ16
allocList32  = allocDataList SZ32
allocList64  = allocDataList SZ64

allocListPtr msg len = ListOf_Ptr . ListOfPtr <$> allocNormalList 64 msg len

-- | Allocate a NormalList
allocNormalList
    :: M.WriteCtx m s
    => BitCount -- ^ The number bits per element
    -> M.Msg ('Mut s) -- ^ The message to allocate in
    -> Int        -- ^ The length of the list, in elements.
    -> m (NormalList ('Mut s))
allocNormalList bitsPerElt msg len = do
    -- round 'len' up to the nearest word boundary for allocation purposes.
    let totalBits = BitCount (len * fromIntegral bitsPerElt)
        totalWords = bytesToWordsCeil $ bitsToBytesCeil totalBits
    addr <- M.alloc msg totalWords
    pure NormalList
        { nMsg = msg
        , nAddr = addr
        , nLen = len
        }

appendCap :: M.WriteCtx m s => M.Msg ('Mut s) -> M.Client -> m (Cap ('Mut s))
appendCap msg client = do
    i <- M.appendCap msg client
    pure $ Cap' msg (fromIntegral i)
