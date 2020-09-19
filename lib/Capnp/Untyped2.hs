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

    , TraverseMsg(..)
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
import Capnp.Mutability     (Mutability(..))
import Capnp.Pointer        (ElementSize(..))
import Capnp.TraversalLimit (MonadLimit(invoice))
import Data.Mutable         (Thaw(..))

import qualified Capnp.Errors   as E
import qualified Capnp.Message2 as M
import qualified Capnp.Pointer  as P

-- | Type (constraint) synonym for the constraints needed for most read
-- operations.
type ReadCtx m mut = (M.Message m mut, MonadThrow m, MonadLimit m)

-- | Synonym for ReadCtx + WriteCtx
type RWCtx m s = (ReadCtx m ('Mut s), M.WriteCtx m s)

-- | A an absolute pointer to a value (of arbitrary type) in a message.
-- Note that there is no variant for far pointers, which don't make sense
-- with absolute addressing.
data Ptr mut
    = PtrCap (Cap mut)
    | PtrList (List mut)
    | PtrStruct (Struct mut)

newtype MaybePtr mut = MaybePtr (Maybe (Ptr mut))

newtype DataListOf a mut = DataListOf (NormalList mut)

-- | A list of values (of arbitrary type) in a message.
data List mut
    = List0 (DataListOf () mut)
    | List1 (DataListOf Bool mut)
    | List8 (DataListOf Word8 mut)
    | List16 (DataListOf Word16 mut)
    | List32 (DataListOf Word32 mut)
    | List64 (DataListOf Word64 mut)
    | ListPtr (PtrListOf MaybePtr mut)
    | ListStruct (PtrListOf Struct mut)

-- | A "normal" (non-composite) list.
data NormalList mut = NormalList
    { nMsg  :: M.Msg mut
    , nAddr :: WordAddr
    , nLen  :: Int
    }

-- | A list of values of type 'f' in a message.
data PtrListOf f mut where
    ListOfPtr :: !(NormalList mut) -> ListOf MaybePtr mut
    ListOfStruct
        :: Struct mut -- First element. data/ptr sizes are the same for
                      -- all elements.
        -> !Int       -- Number of elements
        -> ListOf Struct mut

-- | A Capability in a message.
data Cap mut = Cap (M.Msg mut) !Word32

-- | A struct value in a message.
data Struct mut
    = Struct
        (M.Msg mut)
        !WordAddr -- Start of struct
        !Word16 -- Data section size.
        !Word16 -- Pointer section size.

-- | 'TraverseMsg' is basically 'Traversable' from the prelude, but
-- the intent is that rather than conceptually being a "container",
-- the instance is a value backed by a message, and the point of the
-- type class is to be able to apply transformations to the underlying
-- message.
--
-- We don't just use 'Traversable' for this because while algebraically
-- it makes sense, it would be very unintuitive to e.g. have the
-- 'Traversable' instance for 'List' not traverse over the *elements*
-- of the list.
class TraverseMsg f where
    tMsg :: Applicative m => (M.Msg a -> m (M.Msg b)) -> f (M.Msg a) -> m (f (M.Msg b))

instance TraverseMsg Ptr where
    tMsg f = \case
        PtrCap cap ->
            PtrCap <$> tMsg f cap
        PtrList l ->
            PtrList <$> tMsg f l
        PtrStruct s ->
            PtrStruct <$> tMsg f s

instance TraverseMsg Cap where
    tMsg f (Cap msg n) = Cap <$> f msg <*> pure n

instance TraverseMsg Struct where
    tMsg f (Struct msg addr dataSz ptrSz) = Struct
        <$> f msg
        <*> pure addr
        <*> pure dataSz
        <*> pure ptrSz

instance TraverseMsg List where
    tMsg f = \case
        List0      l -> List0      . unflip  <$> tMsg f (FlipList  l)
        List1      l -> List1      . unflip  <$> tMsg f (FlipList  l)
        List8      l -> List8      . unflip  <$> tMsg f (FlipList  l)
        List16     l -> List16     . unflip  <$> tMsg f (FlipList  l)
        List32     l -> List32     . unflip  <$> tMsg f (FlipList  l)
        List64     l -> List64     . unflip  <$> tMsg f (FlipList  l)
        ListPtr    l -> ListPtr    . unflipP <$> tMsg f (FlipListP l)
        ListStruct l -> ListStruct . unflipS <$> tMsg f (FlipListS l)

instance TraverseMsg NormalList where
    tMsg f NormalList{..} = do
        msg <- f nMsg
        pure NormalList { nMsg = msg, .. }

-------------------------------------------------------------------------------
-- newtype wrappers for the purpose of implementing 'TraverseMsg'; these adjust
-- the shape of 'ListOf' so that we can define an instance. We need a couple
-- different wrappers depending on the shape of the element type.
-------------------------------------------------------------------------------

-- 'FlipList' wraps a @ListOf msg a@ where 'a' is of kind @*@.
newtype FlipList  a msg = FlipList  { unflip  :: ListOf msg a                 }

-- 'FlipListS' wraps a @ListOf msg (Struct msg)@. We can't use 'FlipList' for
-- our instances, because we need both instances of the 'msg' parameter to stay
-- equal.
newtype FlipListS   msg = FlipListS { unflipS :: ListOf msg (Struct msg)      }

-- 'FlipListP' wraps a @ListOf msg (Maybe (Ptr msg))@. Pointers can't use
-- 'FlipList' for the same reason as structs.
newtype FlipListP   msg = FlipListP { unflipP :: ListOf msg (Maybe (Ptr msg)) }

-------------------------------------------------------------------------------
-- 'TraverseMsg' instances for 'FlipList'
-------------------------------------------------------------------------------

instance TraverseMsg (FlipList ()) where
    tMsg f (FlipList (ListOfVoid msg len)) = FlipList <$> (ListOfVoid <$> f msg <*> pure len)

instance TraverseMsg (FlipList Bool) where
    tMsg f (FlipList (ListOfBool   nlist)) = FlipList . ListOfBool   <$> tMsg f nlist

instance TraverseMsg (FlipList Word8) where
    tMsg f (FlipList (ListOfWord8  nlist)) = FlipList . ListOfWord8  <$> tMsg f nlist

instance TraverseMsg (FlipList Word16) where
    tMsg f (FlipList (ListOfWord16 nlist)) = FlipList . ListOfWord16 <$> tMsg f nlist

instance TraverseMsg (FlipList Word32) where
    tMsg f (FlipList (ListOfWord32 nlist)) = FlipList . ListOfWord32 <$> tMsg f nlist

instance TraverseMsg (FlipList Word64) where
    tMsg f (FlipList (ListOfWord64 nlist)) = FlipList . ListOfWord64 <$> tMsg f nlist

-------------------------------------------------------------------------------
-- 'TraverseMsg' instances for struct and pointer lists.
-------------------------------------------------------------------------------

instance TraverseMsg FlipListP where
    tMsg f (FlipListP (ListOfPtr nlist))   = FlipListP . ListOfPtr   <$> tMsg f nlist

instance TraverseMsg FlipListS where
    tMsg f (FlipListS (ListOfStruct tag size)) =
        FlipListS <$> (ListOfStruct <$> tMsg f tag <*> pure size)

-- helpers for applying tMsg to a @ListOf@.
tFlip  :: (TraverseMsg (FlipList a), Applicative m) => (msgA -> m msg) -> ListOf msgA a -> m (ListOf msg a)
tFlipS :: Applicative m => (msgA -> m msg) -> ListOf msgA (Struct msgA) -> m (ListOf msg (Struct msg))
tFlipP :: Applicative m => (msgA -> m msg) -> ListOf msgA (Maybe (Ptr msgA)) -> m (ListOf msg (Maybe (Ptr msg)))
tFlip  f list  = unflip  <$> tMsg f (FlipList  list)
tFlipS f list  = unflipS <$> tMsg f (FlipListS list)
tFlipP f list  = unflipP <$> tMsg f (FlipListP list)

-------------------------------------------------------------------------------
-- Boilerplate 'MaybeMutable' instances.
--
-- These all just call the underlying methods on the message, using 'TraverseMsg'.
-------------------------------------------------------------------------------

instance Thaw a => Thaw (Maybe a) where
    type Mutable s (Maybe a) = Maybe (Mutable s a)

    thaw         = traverse thaw
    freeze       = traverse freeze
    unsafeThaw   = traverse unsafeThaw
    unsafeFreeze = traverse unsafeFreeze

instance Thaw msg => Thaw (Ptr msg) where
    type Mutable s (Ptr msg) = Ptr (Mutable s msg)

    thaw         = tMsg thaw
    freeze       = tMsg freeze
    unsafeThaw   = tMsg unsafeThaw
    unsafeFreeze = tMsg unsafeFreeze

instance Thaw msg => Thaw (List msg) where
    type Mutable s (List msg) = List (Mutable s msg)

    thaw         = tMsg thaw
    freeze       = tMsg freeze
    unsafeThaw   = tMsg unsafeThaw
    unsafeFreeze = tMsg unsafeFreeze

instance Thaw msg => Thaw (NormalList msg) where
    type Mutable s (NormalList msg) = NormalList (Mutable s msg)

    thaw         = tMsg thaw
    freeze       = tMsg freeze
    unsafeThaw   = tMsg unsafeThaw
    unsafeFreeze = tMsg unsafeFreeze

instance Thaw msg => Thaw (ListOf msg ()) where
    type Mutable s (ListOf msg ()) = ListOf (Mutable s msg) ()

    thaw         = tFlip thaw
    freeze       = tFlip freeze
    unsafeThaw   = tFlip unsafeThaw
    unsafeFreeze = tFlip unsafeFreeze

instance Thaw msg => Thaw (ListOf msg Bool) where
    type Mutable s (ListOf msg Bool) = ListOf (Mutable s msg) Bool

    thaw         = tFlip thaw
    freeze       = tFlip freeze
    unsafeThaw   = tFlip unsafeThaw
    unsafeFreeze = tFlip unsafeFreeze

instance Thaw msg => Thaw (ListOf msg Word8) where
    type Mutable s (ListOf msg Word8) = ListOf (Mutable s msg) Word8

    thaw         = tFlip thaw
    freeze       = tFlip freeze
    unsafeThaw   = tFlip unsafeThaw
    unsafeFreeze = tFlip unsafeFreeze

instance Thaw msg => Thaw (ListOf msg Word16) where
    type Mutable s (ListOf msg Word16) = ListOf (Mutable s msg) Word16

    thaw         = tFlip thaw
    freeze       = tFlip freeze
    unsafeThaw   = tFlip unsafeThaw
    unsafeFreeze = tFlip unsafeFreeze

instance Thaw msg => Thaw (ListOf msg Word32) where
    type Mutable s (ListOf msg Word32) = ListOf (Mutable s msg) Word32

    thaw         = tFlip thaw
    freeze       = tFlip freeze
    unsafeThaw   = tFlip unsafeThaw
    unsafeFreeze = tFlip unsafeFreeze

instance Thaw msg => Thaw (ListOf msg Word64) where
    type Mutable s (ListOf msg Word64) = ListOf (Mutable s msg) Word64

    thaw         = tFlip thaw
    freeze       = tFlip freeze
    unsafeThaw   = tFlip unsafeThaw
    unsafeFreeze = tFlip unsafeFreeze

instance Thaw msg => Thaw (ListOf msg (Struct msg)) where
    type Mutable s (ListOf msg (Struct msg)) = ListOf (Mutable s msg) (Struct (Mutable s msg))

    thaw         = tFlipS thaw
    freeze       = tFlipS freeze
    unsafeThaw   = tFlipS unsafeThaw
    unsafeFreeze = tFlipS unsafeFreeze

{-
instance Thaw msg => Thaw (ListOf msg (Maybe (Ptr msg))) where
    type Mutable s (ListOf msg (Maybe (Ptr msg))) =
        ListOf (Mutable s msg) (Maybe (Ptr (Mutable s msg)))

    thaw         = tFlipP thaw
    freeze       = tFlipP freeze
    unsafeThaw   = tFlipP unsafeThaw
    unsafeFreeze = tFlipP unsafeFreeze
-}

instance MaybeMutable Struct where
    thaw         = tMsg thaw
    freeze       = tMsg freeze
    unsafeThaw   = tMsg unsafeThaw
    unsafeFreeze = tMsg unsafeFreeze

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
    message (Cap msg _) = msg

instance HasMessage Struct where
    message (Struct msg _ _ _) = msg

instance MessageDefault Struct where
    messageDefault msg = Struct msg (WordAt 0 0) 0 0

instance HasMessage List where
    message (List0 list)      = message list
    message (List1 list)      = message list
    message (List8 list)      = message list
    message (List16 list)     = message list
    message (List32 list)     = message list
    message (List64 list)     = message list
    message (ListPtr list)    = message list
    message (ListStruct list) = message list

instance HasMessasge (DataListOf a) where
    message (DatListOf nl) = message nl

instance HasMessage (PtrListOf f) where
    message (ListOfStruct tag _) = message tag
    message (ListOfPtr list)     = message list

instance MessageDefault (DataListOf a) where
    messageDefaulut msg = DataListOf $ messageDefault msg

instance MessageDefault (PtrListOf Struct) where
    messageDefault msg =
        -- XXX TODO: make sure this is right; we might need to do something
        -- other than pass through to Struct's instance; IIRC there's something
        -- special about what the offset field means in a list?
        ListOfStruct (messageDefault msg) 0

instance MessageDefault MaybePtr a where
    messageDefault msg = ListOfPtr $ messageDefault msg

instance HasMessage NormalList where
    message = nMsg

instance MessageDefault NormalList where
    messageDefault msg = NormalList msg (WordAt 0 0) 0

getClient :: ReadCtx m mut => Cap mut -> m M.Client
getClient (Cap msg idx) = M.getCap msg (fromIntegral idx)

-- | @get msg addr@ returns the Ptr stored at @addr@ in @msg@.
-- Deducts 1 from the quota for each word read (which may be multiple in the
-- case of far pointers).
get :: ReadCtx m mut => M.Msg mut -> WordAddr -> m (Maybe (Ptr mut))
get msg addr = do
    word <- getWord msg addr
    case P.parsePtr word of
        Nothing -> return Nothing
        Just p -> case p of
            P.CapPtr cap -> return $ Just $ PtrCap (Cap msg cap)
            P.StructPtr off dataSz ptrSz -> return $ Just $ PtrStruct $
                Struct msg (resolveOffset addr off) dataSz ptrSz
            P.ListPtr off eltSpec -> Just <$> getList (resolveOffset addr off) eltSpec
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
                                        return $ Just $ PtrStruct $
                                            Struct msg finalAddr dataSz ptrSz
                                    Just (P.ListPtr 0 eltSpec) ->
                                        Just <$> getList finalAddr eltSpec
                                    -- TODO: I'm not sure whether far pointers to caps are
                                    -- legal; it's clear how they would work, but I don't
                                    -- see a use, and the spec is unclear. Should check
                                    -- how the reference implementation does this, copy
                                    -- that, and submit a patch to the spec.
                                    Just (P.CapPtr cap) ->
                                        return $ Just $ PtrCap (Cap msg cap)
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
                Sz0   -> List0  (ListOfVoid    msg (fromIntegral len))
                Sz1   -> List1  (ListOfBool    nlist)
                Sz8   -> List8  (ListOfWord8   nlist)
                Sz16  -> List16 (ListOfWord16  nlist)
                Sz32  -> List32 (ListOfWord32  nlist)
                Sz64  -> List64 (ListOfWord64  nlist)
                SzPtr -> ListPtr (ListOfPtr nlist)
              where
                nlist = NormalList msg addr (fromIntegral len)
            P.EltComposite _ -> do
                tagWord <- getWord msg addr
                case P.parsePtr' tagWord of
                    P.StructPtr numElts dataSz ptrSz ->
                        pure $ ListStruct $ ListOfStruct
                            (Struct msg
                                    addr { wordIndex = wordIndex + 1 }
                                    dataSz
                                    ptrSz)
                            (fromIntegral numElts)
                    tag -> throwM $ E.InvalidDataError $
                        "Composite list tag was not a struct-" ++
                        "formatted word: " ++ show tag

-- | Return the EltSpec needed for a pointer to the given list.
listEltSpec :: List msg -> P.EltSpec
listEltSpec (ListStruct list@(ListOfStruct (Struct _ _ dataSz ptrSz) _)) =
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
listAddr (ListStruct (ListOfStruct (Struct _ addr _ _) _)) =
    -- addr is the address of the first element of the list, but
    -- composite lists start with a tag word:
    addr { wordIndex = wordIndex addr - 1 }
listAddr (List0 _) = WordAt { segIndex = 0, wordIndex = 1 }
listAddr (List1 (ListOfBool NormalList{nAddr})) = nAddr
listAddr (List8 (ListOfWord8 NormalList{nAddr})) = nAddr
listAddr (List16 (ListOfWord16 NormalList{nAddr})) = nAddr
listAddr (List32 (ListOfWord32 NormalList{nAddr})) = nAddr
listAddr (List64 (ListOfWord64 NormalList{nAddr})) = nAddr
listAddr (ListPtr (ListOfPtr NormalList{nAddr})) = nAddr

-- | Return the address of the pointer's target. It is illegal to call this on
-- a pointer which targets a capability.
ptrAddr :: Ptr msg -> WordAddr
ptrAddr (PtrCap _) = error "ptrAddr called on a capability pointer."
ptrAddr (PtrStruct (Struct _ addr _ _)) = addr
ptrAddr (PtrList list) = listAddr list

-- | @'setIndex value i list@ Set the @i@th element of @list@ to @value@.
setIndex :: RWCtx m s => a -> Int -> ListOf ('Mut s) a -> m ()
setIndex _ i list | length list <= i =
    throwM E.BoundsError { E.index = i, E.maxIndex = length list }
setIndex value i list = case list of
    ListOfVoid _ _     -> pure ()
    ListOfBool nlist   -> setNIndex nlist 64 (Word1 value)
    ListOfWord8 nlist  -> setNIndex nlist 8 value
    ListOfWord16 nlist -> setNIndex nlist 4 value
    ListOfWord32 nlist -> setNIndex nlist 2 value
    ListOfWord64 nlist -> setNIndex nlist 1 value
    ListOfPtr nlist -> case value of
        Just p | message p /= message list -> do
            newPtr <- copyPtr (message list) value
            setIndex newPtr i list
        Nothing                -> setNIndex nlist 1 (P.serializePtr Nothing)
        Just (PtrCap (Cap _ cap))    -> setNIndex nlist 1 (P.serializePtr (Just (P.CapPtr cap)))
        Just p@(PtrList ptrList)     ->
            setPtrIndex nlist p $ P.ListPtr 0 (listEltSpec ptrList)
        Just p@(PtrStruct (Struct _ _ dataSz ptrSz)) ->
            setPtrIndex nlist p $ P.StructPtr 0 dataSz ptrSz
    list@(ListOfStruct _ _) -> do
        dest <- index i list
        copyStruct dest value
  where
    setNIndex :: (ReadCtx m ('Mut s), M.WriteCtx m s, Bounded a, Integral a) => NormalList ('Mut s) -> Int -> a -> m ()
    setNIndex NormalList{nAddr=nAddr@WordAt{..},..} eltsPerWord value = do
        let wordAddr = nAddr { wordIndex = wordIndex + WordCount (i `div` eltsPerWord) }
        word <- M.getWord nMsg wordAddr
        let shift = (i `mod` eltsPerWord) * (64 `div` eltsPerWord)
        M.setWord nMsg wordAddr $ replaceBits value word shift
    setPtrIndex :: (ReadCtx m ('Mut s), M.WriteCtx m s) => NormalList ('Mut s) -> Ptr ('Mut s) -> P.Ptr -> m ()
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

copyPtr :: RWCtx m s => M.Msg ('Mut s) -> Maybe (Ptr ('Mut s)) -> m (Maybe (Ptr ('Mut s)))
copyPtr _ Nothing                = pure Nothing
copyPtr dest (Just (PtrCap cap))    = Just . PtrCap <$> copyCap dest cap
copyPtr dest (Just (PtrList src))   = Just . PtrList <$> copyList dest src
copyPtr dest (Just (PtrStruct src)) = Just . PtrStruct <$> do
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
        destList <- allocCompositeList
            dest
            (fromIntegral $ structListWordCount src)
            (structListPtrCount  src)
            (length src)
        copyListOf destList src
        pure destList

copyNewListOf
    :: RWCtx m s
    => M.Msg ('Mut s)
    -> ListOf ('Mut s) a
    -> (M.Msg ('Mut s) -> Int -> m (ListOf ('Mut s) a))
    -> m (ListOf ('Mut s) a)
copyNewListOf destMsg src new = do
    dest <- new destMsg (length src)
    copyListOf dest src
    pure dest


copyListOf :: RWCtx m s => ListOf ('Mut s) a -> ListOf ('Mut s) a -> m ()
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
    copySection (ptrSection  dest) (ptrSection  src) Nothing
  where
    copySection dest src pad = do
        -- Copy the source section to the destination section:
        copyListOf dest src
        -- Pad the remainder with zeros/default values:
        forM_ [length src..length dest - 1] $ \i ->
            setIndex pad i dest


-- | @index i list@ returns the ith element in @list@. Deducts 1 from the quota
index :: ReadCtx m msg => Int -> ListOf msg a -> m a
index i list = invoice 1 >> index' list
  where
    index' :: ReadCtx m msg => ListOf msg a -> m a
    index' (ListOfVoid _ len)
        | i < len = pure ()
        | otherwise = throwM E.BoundsError { E.index = i, E.maxIndex = len - 1 }
    index' (ListOfStruct (Struct msg addr@WordAt{..} dataSz ptrSz) len)
        | i < len = do
            let offset = WordCount $ i * (fromIntegral dataSz + fromIntegral ptrSz)
            let addr' = addr { wordIndex = wordIndex + offset }
            return $ Struct msg addr' dataSz ptrSz
        | otherwise = throwM E.BoundsError { E.index = i, E.maxIndex = len - 1}
    index' (ListOfBool   nlist) = do
        Word1 val <- indexNList nlist 64
        pure val
    index' (ListOfWord8  nlist) = indexNList nlist 8
    index' (ListOfWord16 nlist) = indexNList nlist 4
    index' (ListOfWord32 nlist) = indexNList nlist 2
    index' (ListOfWord64 (NormalList msg addr@WordAt{..} len))
        | i < len = M.getWord msg addr { wordIndex = wordIndex + WordCount i }
        | otherwise = throwM E.BoundsError { E.index = i, E.maxIndex = len - 1}
    index' (ListOfPtr (NormalList msg addr@WordAt{..} len))
        | i < len = get msg addr { wordIndex = wordIndex + WordCount i }
        | otherwise = throwM E.BoundsError { E.index = i, E.maxIndex = len - 1}
    indexNList :: (ReadCtx m msg, Integral a) => NormalList msg -> Int -> m a
    indexNList (NormalList msg addr@WordAt{..} len) eltsPerWord
        | i < len = do
            let wordIndex' = wordIndex + WordCount (i `div` eltsPerWord)
            word <- M.getWord msg addr { wordIndex = wordIndex' }
            let shift = (i `mod` eltsPerWord) * (64 `div` eltsPerWord)
            pure $ fromIntegral $ word `shiftR` shift
        | otherwise = throwM E.BoundsError { E.index = i, E.maxIndex = len - 1 }

-- | Returns the length of a list
length :: ListOf msg a -> Int
length (ListOfVoid _ len)   = len
length (ListOfStruct _ len) = len
length (ListOfBool   nlist) = nLen nlist
length (ListOfWord8  nlist) = nLen nlist
length (ListOfWord16 nlist) = nLen nlist
length (ListOfWord32 nlist) = nLen nlist
length (ListOfWord64 nlist) = nLen nlist
length (ListOfPtr    nlist) = nLen nlist

-- | The data section of a struct, as a list of Word64
dataSection :: Struct mut -> DataListOf Word64 mut
dataSection (Struct msg addr dataSz _) =
    DataListOf $ NormalList msg addr (fromIntegral dataSz)

-- | The pointer section of a struct, as a list of Ptr
ptrSection :: Struct mut -> PtrListOf MaybePtr mut
ptrSection (Struct msg addr@WordAt{..} dataSz ptrSz) =
    ListOfPtr $ NormalList
        msg
        addr { wordIndex = wordIndex + fromIntegral dataSz }
        (fromIntegral ptrSz)

-- | Get the size (in words) of a struct's data section.
structWordCount :: Struct mut -> WordCount
structWordCount (Struct _msg _addr dataSz _ptrSz) = fromIntegral dataSz

-- | Get the size (in bytes) of a struct's data section.
structByteCount :: Struct mut -> ByteCount
structByteCount = wordsToBytes . structWordCount

-- | Get the size of a struct's pointer section.
structPtrCount  :: Struct mut -> Word16
structPtrCount (Struct _msg _addr _dataSz ptrSz) = ptrSz

-- | Get the size (in words) of the data sections in a struct list.
structListWordCount :: PtrListOf Struct mut -> WordCount
structListWordCount (ListOfStruct s _) = structWordCount s

-- | Get the size (in bytes) of the data sections in a struct list.
structListByteCount :: PtrListOf Struct mut -> ByteCount
structListByteCount (ListOfStruct s _) = structByteCount s

-- | Get the size of the pointer sections in a struct list.
structListPtrCount  :: PtrListOf Struct mut -> Word16
structListPtrCount  (ListOfStruct s _) = structPtrCount s

-- | @'getData' i struct@ gets the @i@th word from the struct's data section,
-- returning 0 if it is absent.
getData :: ReadCtx m msg => Int -> Struct msg -> m Word64
getData i struct
    | fromIntegral (structWordCount struct) <= i = 0 <$ invoice 1
    | otherwise = index i (dataSection struct)

-- | @'getPtr' i struct@ gets the @i@th word from the struct's pointer section,
-- returning Nothing if it is absent.
getPtr :: ReadCtx m msg => Int -> Struct msg -> m (Maybe (Ptr msg))
getPtr i struct
    | fromIntegral (structPtrCount struct) <= i = Nothing <$ invoice 1
    | otherwise = index i (ptrSection struct)

-- | @'setData' value i struct@ sets the @i@th word in the struct's data section
-- to @value@.
setData :: (ReadCtx m ('Mut s), M.WriteCtx m s)
    => Word64 -> Int -> Struct ('Mut s) -> m ()
setData value i = setIndex value i . dataSection

-- | @'setData' value i struct@ sets the @i@th pointer in the struct's pointer
-- section to @value@.
setPtr :: (ReadCtx m ('Mut s), M.WriteCtx m s) => Maybe (Ptr ('Mut s)) -> Int -> Struct ('Mut s) -> m ()
setPtr value i = setIndex value i . ptrSection

-- | 'rawBytes' returns the raw bytes corresponding to the list.
rawBytes :: ReadCtx m mut => DataListOf Word8 mut -> m BS.ByteString
rawBytes (DataListOf (NormalList msg WordAt{..} len)) = do
    invoice $ fromIntegral $ bytesToWordsCeil (ByteCount len)
    bytes <- M.getSegment msg segIndex >>= M.toByteString
    let ByteCount byteOffset = wordsToBytes wordIndex
    pure $ BS.take len $ BS.drop byteOffset bytes


-- | Returns the root pointer of a message.
rootPtr :: ReadCtx m msg => msg -> m (Struct msg)
rootPtr msg = do
    root <- get msg (WordAt 0 0)
    case root of
        Just (PtrStruct struct) -> pure struct
        Nothing -> pure (messageDefault msg)
        _ -> throwM $ E.SchemaViolationError
                "Unexpected root type; expected struct."


-- | Make the given struct the root object of its message.
setRoot :: M.WriteCtx m s => Struct ('Mut s) -> m ()
setRoot (Struct msg addr dataSz ptrSz) =
    setPointerTo msg (WordAt 0 0) addr (P.StructPtr 0 dataSz ptrSz)

-- | Allocate a struct in the message.
allocStruct :: M.WriteCtx m s => M.Msg ('Mut s) -> Word16 -> Word16 -> m (Struct ('Mut s))
allocStruct msg dataSz ptrSz = do
    let totalSz = fromIntegral dataSz + fromIntegral ptrSz
    addr <- M.alloc msg totalSz
    pure $ Struct msg addr dataSz ptrSz

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
    let firstStruct = Struct
            msg
            addr { wordIndex = wordIndex addr + 1 }
            dataSz
            ptrSz
    pure $ ListOfStruct firstStruct len

-- | Allocate a list of capnproto @Void@ values.
allocList0   :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (DataListOf () ('Mut s))

-- | Allocate a list of booleans
allocList1   :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (DataListOf Bool ('Mut s))

-- | Allocate a list of 8-bit values.
allocList8   :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (DataListOf Word8 ('Mut s))

-- | Allocate a list of 16-bit values.
allocList16  :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (DataListOf Word16 ('Mut s))

-- | Allocate a list of 32-bit values.
allocList32  :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (DataListOf Word32 ('Mut s))

-- | Allocate a list of 64-bit words.
allocList64  :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (DataListOf Word64 ('Mut s))

-- | Allocate a list of pointers.
allocListPtr :: M.WriteCtx m s => M.Msg ('Mut s) -> Int -> m (PtrListOf MaybePtr ('Mut s))

allocDataList :: M.WriteCtx m s => Int -> M.Msg ('Mut s) -> Int -> m (DataListOf a ('Mut s))
allocDataList sz msg len = DataListOf <$> allocNormalList sz msg len

allocList0   = allocDataList  0
allocList1   = allocDataList  1
allocList8   = allocDataList  8
allocList16  = allocDataList 16
allocList32  = allocDataList 32
allocList64  = allocDataList 64

allocListPtr msg len = ListOfPtr <$> allocNormalList 64 msg len

-- | Allocate a NormalList
allocNormalList
    :: M.WriteCtx m s
    => Int        -- ^ The number bits per element
    -> M.Msg ('Mut s) -- ^ The message to allocate in
    -> Int        -- ^ The length of the list, in elements.
    -> m (NormalList ('Mut s))
allocNormalList bitsPerElt msg len = do
    -- round 'len' up to the nearest word boundary for allocation purposes.
    let totalBits = BitCount (len * bitsPerElt)
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
    pure $ Cap msg (fromIntegral i)
