{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE TypeFamilies          #-}
{-|
Module: Capnp.Message
Description: Cap'N Proto messages

This module provides support for working directly with Cap'N Proto messages.
-}
module Capnp.Message2 (
    -- * Reading and writing messages
      hPutMsg
    , hGetMsg
    , putMsg
    , getMsg

    , readMessage
    , writeMessage

    -- * Limits on message size
    , maxSegmentSize
    , maxSegments
    , maxCaps

    -- * Converting between messages and 'ByteString's
    , encode
    , decode

    -- * Message type class
    , Message(..)

    -- * Immutable messages
    , empty

    -- * Reading data from messages
    , getSegment
    , getWord
    , getCap
    , getCapTable

    -- * Mutable Messages
    , newMessage

    -- ** Allocating space in messages
    , alloc
    , allocInSeg
    , newSegment

    -- ** Modifying messages
    , setSegment
    , setWord
    , setCap
    , appendCap

    , WriteCtx

    , Client
    , nullClient
    , withCapTable


    --
    , Mutability(..)
    , Msg
    ) where

-- import {-# SOURCE #-} Capnp.Rpc.Untyped (Client, nullClient)
import Capnp.Rpc.Untyped (Client, nullClient)

import Prelude hiding (read)

import Data.Bits (shiftL)

import Control.Monad             (void, when, (>=>))
import Control.Monad.Catch       (MonadThrow(..))
import Control.Monad.Primitive   (PrimMonad, PrimState)
import Control.Monad.State       (evalStateT, get, put)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Writer      (execWriterT, tell)
import Data.Bytes.Get            (getWord32le, runGetS)
import Data.ByteString.Internal  (ByteString(..))
import Data.Kind                 (Type)
import Data.Maybe                (fromJust)
import Data.Primitive            (MutVar, newMutVar, readMutVar, writeMutVar)
import Data.Word                 (Word32, Word64)
import System.Endian             (fromLE64, toLE64)
import System.IO                 (Handle, stdin, stdout)

import qualified Data.ByteString              as BS
import qualified Data.ByteString.Builder      as BB
import qualified Data.Vector                  as V
import qualified Data.Vector.Generic.Mutable  as GMV
import qualified Data.Vector.Mutable          as MV
import qualified Data.Vector.Storable         as SV
import qualified Data.Vector.Storable.Mutable as SMV

import Capnp.Address        (WordAddr(..))
import Capnp.Bits           (WordCount(..), hi, lo)
import Capnp.TraversalLimit (LimitT, MonadLimit(invoice), evalLimitT)
import Data.Mutable         (Mutable(..))
import Internal.AppendVec   (AppendVec)

import qualified Capnp.Errors       as E
import qualified Internal.AppendVec as AppendVec

-- | The maximum size of a segment supported by this libarary, in words.
maxSegmentSize :: Int
maxSegmentSize = 1 `shiftL` 28 -- 2 GiB.

-- | The maximum number of segments allowed in a message by this library.
maxSegments :: Int
maxSegments = 1024

-- | The maximum number of capabilities allowed in a message by this library.
maxCaps :: Int
maxCaps = 512

data Mutability = Mut Type | Const

data Msg :: Mutability -> * where
    MutMsg :: {-# UNPACK #-} !(MutMsg' s) -> Msg ('Mut s)
    ConstMsg :: {-# UNPACK #-} !ConstMsg' -> Msg 'Const

data Segment :: Mutability -> * where
    MutSegment :: AppendVec SMV.MVector s Word64 -> Segment ('Mut s)
    ConstSegment :: SV.Vector Word64 -> Segment 'Const

-- | GHC seems not to be smart enough in some cases to tell that the
-- pattern @MutSegment x@ ins irrefutble for Mut s when used in-line
-- in a more complex funciton. It seems to work to factor it out into
-- a separate function like this.
unwrapMutSegment :: Segment ('Mut s) -> AppendVec SMV.MVector s Word64
unwrapMutSegment (MutSegment x)   = x

instance Eq (Segment 'Const) where
    ConstSegment v1 == ConstSegment v2 = v1 == v2

-- | A 'Message' is a (possibly read-only) capnproto message. It is
-- parameterized over a monad in which operations are performed.
class Monad m => Message m (mut :: Mutability) where
    -- | 'numSegs' gets the number of segments in a message.
    numSegs :: Msg mut -> m Int
    -- | 'numWords' gets the number of words in a segment.
    numWords :: Segment mut-> m WordCount
    -- | 'numCaps' gets the number of capabilities in a message's capability
    -- table.
    numCaps :: Msg mut -> m Int
    -- | @'internalGetSeg' message index@ gets the segment at index 'index'
    -- in 'message'. Most callers should use the 'getSegment' wrapper, instead
    -- of calling this directly.
    internalGetSeg :: Msg mut -> Int -> m (Segment mut)
    -- | @'internalGetCap' cap index@ reads a capability from the message's
    -- capability table, returning the client. does not check bounds. Callers
    -- should use getCap instead.
    internalGetCap :: Msg mut -> Int -> m Client
    -- | @'slice' start length segment@ extracts a sub-section of the segment,
    -- starting at index @start@, of length @length@.
    slice   :: WordCount -> WordCount -> Segment mut -> m (Segment mut)
    -- | @'read' segment index@ reads a 64-bit word from the segement at the
    -- given index. Consider using 'getWord' on the message, instead of
    -- calling this directly.
    read    :: Segment mut-> WordCount -> m Word64
    -- | Convert a ByteString to a segment.
    fromByteString :: ByteString -> m (Segment mut)
    -- | Convert a segment to a byte string.
    toByteString :: Segment mut -> m ByteString

instance Monad m => Message m 'Const where
    numSegs (ConstMsg ConstMsg'{constSegs}) = pure $ V.length constSegs
    numCaps (ConstMsg ConstMsg'{constCaps}) = pure $ V.length constCaps
    internalGetSeg (ConstMsg ConstMsg'{constSegs}) i = constSegs `V.indexM` i
    internalGetCap (ConstMsg ConstMsg'{constCaps}) i = constCaps `V.indexM` i

    numWords (ConstSegment vec) = pure $ WordCount $ SV.length vec

    slice (WordCount start) (WordCount len) (ConstSegment vec) =
        pure $ ConstSegment (SV.slice start len vec)
    read (ConstSegment vec) i = fromLE64 <$> vec `SV.indexM` fromIntegral i

    -- FIXME: Verify that the pointer is actually 64-bit aligned before casting.
    fromByteString (PS fptr offset len) =
        pure $ ConstSegment (SV.unsafeCast $ SV.unsafeFromForeignPtr fptr offset len)
    toByteString (ConstSegment vec) = pure $ PS fptr offset len where
        (fptr, offset, len) = SV.unsafeToForeignPtr (SV.unsafeCast vec)

instance (PrimMonad m, s ~ PrimState m) => Message m ('Mut s) where
    numWords (MutSegment mseg) = pure $ WordCount $ GMV.length (AppendVec.getVector mseg)

    slice (WordCount start) (WordCount len) (MutSegment mseg) =
        pure $ MutSegment $ AppendVec.fromVector $
            SMV.slice start len (AppendVec.getVector mseg)
    read (MutSegment mseg) i = fromLE64 <$> SMV.read (AppendVec.getVector mseg) (fromIntegral i)
    fromByteString bytes = do
        seg <- fromByteString bytes
        thaw (seg :: Segment 'Const)
    toByteString mseg = do
        seg <- freeze mseg
        toByteString (seg :: Segment 'Const)

    numSegs (MutMsg MutMsg'{mutSegs}) = GMV.length . AppendVec.getVector <$> readMutVar mutSegs
    numCaps (MutMsg MutMsg'{mutCaps}) = GMV.length . AppendVec.getVector <$> readMutVar mutCaps
    internalGetSeg (MutMsg MutMsg'{mutSegs}) i = do
        segs <- AppendVec.getVector <$> readMutVar mutSegs
        MV.read segs i
    internalGetCap (MutMsg MutMsg'{mutCaps}) i = do
        caps <- AppendVec.getVector <$> readMutVar mutCaps
        MV.read caps i

-- | @'getSegment' message index@ fetches the given segment in the message.
-- It throws a 'E.BoundsError' if the address is out of bounds.
getSegment :: (MonadThrow m, Message m mut) => Msg mut -> Int -> m (Segment mut)
getSegment msg i = do
    checkIndex i =<< numSegs msg
    internalGetSeg msg i

-- | @'withCapTable'@ replaces the capability table in the message.
withCapTable :: V.Vector Client -> Msg 'Const -> Msg 'Const
withCapTable newCaps (ConstMsg msg) = ConstMsg msg { constCaps = newCaps }

-- | 'getCapTable' gets the capability table from a 'ConstMsg'.
getCapTable :: Msg 'Const -> V.Vector Client
getCapTable (ConstMsg ConstMsg'{constCaps}) = constCaps

-- | @'getCap' message index@ gets the capability with the given index from
-- the message. throws 'E.BoundsError' if the index is out
-- of bounds.
getCap :: (MonadThrow m, Message m mut) => Msg mut -> Int -> m Client
getCap msg i = do
    ncaps <- numCaps msg
    if i >= ncaps || i < 0
        then pure nullClient
        else msg `internalGetCap` i

-- | @'getWord' msg addr@ returns the word at @addr@ within @msg@. It throws a
-- 'E.BoundsError' if the address is out of bounds.
getWord :: (MonadThrow m, Message m mut) => Msg mut -> WordAddr -> m Word64
getWord msg WordAt{wordIndex=i, segIndex} = do
    seg <- getSegment msg segIndex
    checkIndex i =<< numWords seg
    seg `read` i

-- | @'setSegment' message index segment@ sets the segment at the given index
-- in the message. It throws a 'E.BoundsError' if the address is out of bounds.
setSegment :: (WriteCtx m s, MonadThrow m) => Msg ('Mut s) -> Int -> Segment ('Mut s) -> m ()
setSegment msg i seg = do
    checkIndex i =<< numSegs msg
    internalSetSeg msg i seg

-- | @'setWord' message address value@ sets the word at @address@ in the
-- message to @value@. If the address is not valid in the message, a
-- 'E.BoundsError' will be thrown.
setWord :: (WriteCtx m s, MonadThrow m) => Msg ('Mut s) -> WordAddr -> Word64 -> m ()
setWord msg WordAt{wordIndex=i, segIndex} val = do
    seg <- getSegment msg segIndex
    checkIndex i =<< numWords seg
    write seg i val

-- | @'setCap' message index cap@ sets the sets the capability at @index@ in
-- the message's capability table to @cap@. If the index is out of bounds, a
-- 'E.BoundsError' will be thrown.
setCap :: (WriteCtx m s, MonadThrow m) => Msg ('Mut s) -> Int -> Client -> m ()
setCap msg@(MutMsg MutMsg'{mutCaps}) i cap = do
    checkIndex i =<< numCaps msg
    capTable <- AppendVec.getVector <$> readMutVar mutCaps
    MV.write capTable i cap

-- | 'appendCap' appends a new capabilty to the end of a message's capability
-- table, returning its index.
appendCap :: WriteCtx m s => Msg ('Mut s) -> Client -> m Int
appendCap msg@(MutMsg MutMsg'{mutCaps}) cap = do
    i <- numCaps msg
    capTable <- readMutVar mutCaps
    capTable <- AppendVec.grow capTable 1 maxCaps
    writeMutVar mutCaps capTable
    setCap msg i cap
    pure i

-- | A read-only capnproto message.
--
-- 'ConstMsg' is an instance of the generic 'Message' type class. its
-- implementations of 'toByteString' and 'fromByteString' are O(1);
-- the underlying bytes are not copied.
data ConstMsg' = ConstMsg'
    { constSegs :: V.Vector (Segment 'Const)
    , constCaps :: V.Vector Client
    }
    deriving(Eq)

-- | 'decode' decodes a message from a bytestring.
--
-- The segments will not be copied; the resulting message will be a view into
-- the original bytestring. Runs in O(number of segments in the message).
decode :: MonadThrow m => ByteString -> m (Msg 'Const)
decode bytes = fromByteString bytes >>= decodeSeg

-- | 'encode' encodes a message as a bytestring builder.
encode :: Monad m => Msg 'Const -> m BB.Builder
encode msg =
    -- We use Maybe as the MonadThrow instance required by
    -- writeMessage/toByteString, but we know this can't actually fail,
    -- so we ignore errors. TODO: we should get rid of the Monad constraint
    -- on this function and just have the tyep be ConstMsg -> BB.Builder,
    -- but that will have some cascading api effects, so we're deferring
    -- that for a bit.
    pure $ fromJust $ execWriterT $ writeMessage
        msg
        (tell . BB.word32LE)
        (toByteString >=> tell . BB.byteString)

-- | 'decodeSeg' decodes a message from a segment, treating the segment as if
-- it were raw bytes.
--
-- this is mostly here as a helper for 'decode'.
decodeSeg :: MonadThrow m => Segment 'Const -> m (Msg 'Const)
decodeSeg seg = do
    len <- numWords seg
    flip evalStateT (Nothing, 0) $ evalLimitT len $
        -- Note: we use the traversal limit to avoid needing to do bounds checking
        -- here; since readMessage invoices the limit before reading, we can rely
        -- on it not to read past the end of the blob.
        --
        -- TODO: while this works, it means that we throw 'TraversalLimitError'
        -- on failure, which makes for a confusing API.
        readMessage read32 readSegment
  where
    read32 = do
        (cur, idx) <- get
        case cur of
            Just n -> do
                put (Nothing, idx)
                return n
            Nothing -> do
                word <- lift $ lift $ read seg idx
                put (Just $ hi word, idx + 1)
                return (lo word)
    readSegment len = do
        (cur, idx) <- get
        put (cur, idx + len)
        lift $ lift $ slice idx len seg

-- | @'readMessage' read32 readSegment@ reads in a message using the
-- monadic context, which should manage the current read position,
-- into a message. read32 should read a 32-bit little-endian integer,
-- and @readSegment n@ should read a blob of @n@ 64-bit words.
-- The size of the message (in 64-bit words) is deducted from the traversal,
-- limit which can be used to set the maximum message size.
readMessage :: (MonadThrow m, MonadLimit m) => m Word32 -> (WordCount -> m (Segment 'Const)) -> m (Msg 'Const)
readMessage read32 readSegment = do
    invoice 1
    numSegs' <- read32
    let numSegs = numSegs' + 1
    invoice (fromIntegral numSegs `div` 2)
    segSizes <- V.replicateM (fromIntegral numSegs) read32
    when (even numSegs) $ void read32
    V.mapM_ (invoice . fromIntegral) segSizes
    constSegs <- V.mapM (readSegment . fromIntegral) segSizes
    pure $ ConstMsg ConstMsg'{constSegs, constCaps = V.empty}

-- | @'writeMesage' write32 writeSegment@ writes out the message. @write32@
-- should write a 32-bit word in little-endian format to the output stream.
-- @writeSegment@ should write a blob.
writeMessage :: MonadThrow m => Msg 'Const -> (Word32 -> m ()) -> (Segment 'Const -> m ()) -> m ()
writeMessage (ConstMsg ConstMsg'{constSegs}) write32 writeSegment = do
    let numSegs = V.length constSegs
    write32 (fromIntegral numSegs - 1)
    V.forM_ constSegs $ \seg -> write32 . fromIntegral =<< numWords seg
    when (even numSegs) $ write32 0
    V.forM_ constSegs writeSegment


-- | @'hPutMsg' handle msg@ writes @msg@ to @handle@. If there is an exception,
-- it will be an 'IOError' raised by the underlying IO libraries.
hPutMsg :: Handle -> Msg 'Const -> IO ()
hPutMsg handle msg = encode msg >>= BB.hPutBuilder handle

-- | Equivalent to @'hPutMsg' 'stdout'@
putMsg :: Msg 'Const -> IO ()
putMsg = hPutMsg stdout

-- | @'hGetMsg' handle limit@ reads a message from @handle@ that is at most
-- @limit@ 64-bit words in length.
hGetMsg :: Handle -> WordCount -> IO (Msg 'Const)
hGetMsg handle size =
    evalLimitT size $ readMessage read32 readSegment
  where
    read32 :: LimitT IO Word32
    read32 = lift $ do
        bytes <- BS.hGet handle 4
        case runGetS getWord32le bytes of
            Left _ ->
                -- the only way this can happen is if we get < 4 bytes.
                throwM $ E.InvalidDataError "Unexpected end of input"
            Right result ->
                pure result
    readSegment n = lift $ BS.hGet handle (fromIntegral n * 8) >>= fromByteString

-- | Equivalent to @'hGetMsg' 'stdin'@
getMsg :: WordCount -> IO (Msg 'Const)
getMsg = hGetMsg stdin

-- | A 'MutMsg' is a mutable capnproto message. The type parameter @s@ is the
-- state token for the instance of 'PrimMonad' in which the message may be
-- modified.
--
-- Due to mutabilty, the implementations of 'toByteString' and 'fromByteString'
-- must make full copies, and so are O(n) in the length of the segment.
data MutMsg' s = MutMsg'
    { mutSegs :: MutVar s (AppendVec MV.MVector s (Segment ('Mut s)))
    , mutCaps :: MutVar s (AppendVec MV.MVector s Client)
    }
    deriving(Eq)

-- | 'WriteCtx' is the context needed for most write operations.
type WriteCtx m s = (PrimMonad m, s ~ PrimState m, MonadThrow m)


-- | @'internalSetSeg' message index segment@ sets the segment at the given
-- index in the message. Most callers should use the 'setSegment' wrapper,
-- instead of calling this directly.
internalSetSeg :: WriteCtx m s => Msg ('Mut s) -> Int -> Segment ('Mut s) -> m ()
internalSetSeg (MutMsg MutMsg'{mutSegs}) segIndex seg = do
    segs <- AppendVec.getVector <$> readMutVar mutSegs
    MV.write segs segIndex seg

-- | @'write' segment index value@ writes a value to the 64-bit word
-- at the provided index. Consider using 'setWord' on the message,
-- instead of calling this directly.
write :: WriteCtx m s => Segment ('Mut s) -> WordCount -> Word64 -> m ()
write (MutSegment seg) (WordCount i) val =
    SMV.write (AppendVec.getVector seg) i (toLE64 val)

-- | @'grow' segment amount@ grows the segment by the specified number
-- of 64-bit words. The original segment should not be used afterwards.
grow  :: WriteCtx m s => Segment ('Mut s) -> Int -> m (Segment ('Mut s))
grow (MutSegment vec) amount =
    MutSegment <$> AppendVec.grow vec amount maxSegmentSize

-- | @'newSegment' msg sizeHint@ allocates a new, initially empty segment in
-- @msg@ with a capacity of @sizeHint@. It returns the a pair of the segment
-- number and the segment itself. Amortized O(1).
newSegment :: WriteCtx m s => Msg ('Mut s) -> Int -> m (Int, Segment ('Mut s))
newSegment msg@(MutMsg MutMsg'{mutSegs}) sizeHint = do
    -- the next segment number will be equal to the *current* number of
    -- segments:
    segIndex <- numSegs msg

    -- make space for th new segment
    segs <- readMutVar mutSegs
    segs <- AppendVec.grow segs 1 maxSegments
    writeMutVar mutSegs segs

    newSeg <- MutSegment . AppendVec.makeEmpty <$> SMV.new sizeHint
    setSegment msg segIndex newSeg
    pure (segIndex, newSeg)

-- | Like 'alloc', but the second argument allows the caller to specify the
-- index of the segment in which to allocate the data.
allocInSeg :: WriteCtx m s => Msg ('Mut s) -> Int -> WordCount -> m WordAddr
allocInSeg msg segIndex (WordCount size) = do
    oldSeg <- getSegment msg segIndex
    let vec = unwrapMutSegment oldSeg
    let ret = WordAt
            { segIndex
            , wordIndex = WordCount $ GMV.length $ AppendVec.getVector vec
            }
    newSeg <- grow oldSeg size
    setSegment msg segIndex newSeg
    pure ret

-- | @'alloc' size@ allocates 'size' words within a message. it returns the
-- starting address of the allocated memory.
alloc :: WriteCtx m s => Msg ('Mut s) -> WordCount -> m WordAddr
alloc msg size@(WordCount sizeInt) = do
    segIndex <- pred <$> numSegs msg
    vec <- unwrapMutSegment <$> getSegment msg segIndex
    if AppendVec.canGrowWithoutCopy vec sizeInt
        then
            allocInSeg msg segIndex size
        else do
            let MutMsg MutMsg'{mutSegs} = msg
            segments <- readMutVar mutSegs
            segs <- V.freeze (AppendVec.getVector segments)
            let totalAllocation = V.sum $ fmap (\(MutSegment vec) -> AppendVec.getCapacity vec) segs
            -- the new segment's size should match the total size of existing segments
            ( newSegIndex, _ ) <- newSegment msg (min maxSegmentSize (max totalAllocation sizeInt))
            allocInSeg msg newSegIndex size

-- | 'empty' is an empty message, i.e. a minimal message with a null pointer as
-- its root object.
empty :: Msg 'Const
empty = ConstMsg ConstMsg'
    { constSegs = V.fromList [ ConstSegment $ SV.fromList [0] ]
    , constCaps = V.empty
    }

-- | @'newMessage' sizeHint@ allocates a new empty message, with a single segment
-- having capacity @sizeHint@. If @sizeHint@ is 'Nothing', defaults to a sensible
-- value.
newMessage :: WriteCtx m s => Maybe WordCount -> m (Msg ('Mut s))
newMessage Nothing = newMessage (Just 32)
    -- The default value above is somewhat arbitrary, and just a guess -- we
    -- should do some profiling to figure out what a good value is here.
newMessage (Just (WordCount sizeHint)) = do
    mutSegs <- MV.new 1 >>= newMutVar . AppendVec.makeEmpty
    mutCaps <- MV.new 0 >>= newMutVar . AppendVec.makeEmpty
    let msg = MutMsg MutMsg'{mutSegs,mutCaps}
    -- allocte the first segment, and make space for the root pointer:
    _ <- newSegment msg sizeHint
    _ <- alloc msg 1
    pure msg


instance Thaw (Segment 'Const) where
    type Mutable s (Segment 'Const) = Segment ('Mut s)

    thaw         = thawSeg   thaw
    unsafeThaw   = thawSeg   unsafeThaw
    freeze       = freezeSeg freeze
    unsafeFreeze = freezeSeg unsafeFreeze

-- Helpers for @Segment ConstMsg@'s Thaw instance.
thawSeg
    :: (PrimMonad m, s ~ PrimState m)
    => (AppendVec.FrozenAppendVec SV.Vector Word64 -> m (AppendVec SMV.MVector s Word64))
    -> Segment 'Const
    -> m (Segment ('Mut s))
thawSeg thaw (ConstSegment vec) =
    MutSegment <$> thaw (AppendVec.FrozenAppendVec vec)

freezeSeg
    :: (PrimMonad m, s ~ PrimState m)
    => (AppendVec SMV.MVector s Word64 -> m (AppendVec.FrozenAppendVec SV.Vector Word64))
    -> Segment ('Mut s)
    -> m (Segment 'Const)
freezeSeg freeze (MutSegment mvec) =
    ConstSegment . AppendVec.getFrozenVector <$> freeze mvec

instance Thaw (Msg 'Const) where
    type Mutable s (Msg 'Const) = Msg ('Mut s)

    thaw         = thawMsg   thaw         V.thaw
    unsafeThaw   = thawMsg   unsafeThaw   V.unsafeThaw
    freeze       = freezeMsg freeze       V.freeze
    unsafeFreeze = freezeMsg unsafeFreeze V.unsafeFreeze

-- Helpers for (Msg Const)'s Thaw instance.
thawMsg :: (PrimMonad m, s ~ PrimState m)
    => (Segment 'Const -> m (Segment ('Mut s)))
    -> (V.Vector Client -> m (MV.MVector s Client))
    -> Msg 'Const
    -> m (Msg ('Mut s))
thawMsg thawSeg thawCaps (ConstMsg ConstMsg'{constSegs, constCaps}) = do
    mutSegs <- newMutVar . AppendVec.fromVector =<< (V.mapM thawSeg constSegs >>= V.unsafeThaw)
    mutCaps <- newMutVar . AppendVec.fromVector =<< thawCaps constCaps
    pure $ MutMsg MutMsg'{mutSegs, mutCaps}
freezeMsg :: (PrimMonad m, s ~ PrimState m)
    => (Segment ('Mut s) -> m (Segment 'Const))
    -> (MV.MVector s Client -> m (V.Vector Client))
    -> Msg ('Mut s)
    -> m (Msg 'Const)
freezeMsg freezeSeg freezeCaps msg@(MutMsg MutMsg'{mutCaps}) = do
    len <- numSegs msg
    constSegs <- V.generateM len (internalGetSeg msg >=> freezeSeg)
    constCaps <- freezeCaps . AppendVec.getVector =<< readMutVar mutCaps
    pure $ ConstMsg ConstMsg'{constSegs, constCaps}

-- | @'checkIndex' index length@ checkes that 'index' is in the range
-- [0, length), throwing a 'BoundsError' if not.
checkIndex :: (Integral a, MonadThrow m) => a -> a -> m ()
checkIndex i len =
    when (i < 0 || i >= len) $
        throwM E.BoundsError
            { E.index = fromIntegral i
            , E.maxIndex = fromIntegral len
            }
