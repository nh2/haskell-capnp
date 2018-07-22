{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Internal.Gen.ListElem where
-- This module is auto-generated by gen-builtintypes-lists.hs; DO NOT EDIT.

import Data.Int
import Data.ReinterpretCast
import Data.Word

import Codec.Capnp (ListElem(..), MutListElem(..))

import qualified Data.Capnp.Untyped as U

instance ListElem msg Int8 where
    newtype List msg Int8 = ListInt8 (U.ListOf msg Word8)
    length (ListInt8 l) = U.length l
    index i (ListInt8 l) = fromIntegral <$> U.index i l
instance MutListElem s Int8 where
    setIndex elt i (ListInt8 l) = U.setIndex (fromIntegral elt) i l
    allocList msg size = ListInt8 <$> U.allocList8 msg size
instance ListElem msg Int16 where
    newtype List msg Int16 = ListInt16 (U.ListOf msg Word16)
    length (ListInt16 l) = U.length l
    index i (ListInt16 l) = fromIntegral <$> U.index i l
instance MutListElem s Int16 where
    setIndex elt i (ListInt16 l) = U.setIndex (fromIntegral elt) i l
    allocList msg size = ListInt16 <$> U.allocList16 msg size
instance ListElem msg Int32 where
    newtype List msg Int32 = ListInt32 (U.ListOf msg Word32)
    length (ListInt32 l) = U.length l
    index i (ListInt32 l) = fromIntegral <$> U.index i l
instance MutListElem s Int32 where
    setIndex elt i (ListInt32 l) = U.setIndex (fromIntegral elt) i l
    allocList msg size = ListInt32 <$> U.allocList32 msg size
instance ListElem msg Int64 where
    newtype List msg Int64 = ListInt64 (U.ListOf msg Word64)
    length (ListInt64 l) = U.length l
    index i (ListInt64 l) = fromIntegral <$> U.index i l
instance MutListElem s Int64 where
    setIndex elt i (ListInt64 l) = U.setIndex (fromIntegral elt) i l
    allocList msg size = ListInt64 <$> U.allocList64 msg size
instance ListElem msg Word8 where
    newtype List msg Word8 = ListWord8 (U.ListOf msg Word8)
    length (ListWord8 l) = U.length l
    index i (ListWord8 l) = id <$> U.index i l
instance MutListElem s Word8 where
    setIndex elt i (ListWord8 l) = U.setIndex (id elt) i l
    allocList msg size = ListWord8 <$> U.allocList8 msg size
instance ListElem msg Word16 where
    newtype List msg Word16 = ListWord16 (U.ListOf msg Word16)
    length (ListWord16 l) = U.length l
    index i (ListWord16 l) = id <$> U.index i l
instance MutListElem s Word16 where
    setIndex elt i (ListWord16 l) = U.setIndex (id elt) i l
    allocList msg size = ListWord16 <$> U.allocList16 msg size
instance ListElem msg Word32 where
    newtype List msg Word32 = ListWord32 (U.ListOf msg Word32)
    length (ListWord32 l) = U.length l
    index i (ListWord32 l) = id <$> U.index i l
instance MutListElem s Word32 where
    setIndex elt i (ListWord32 l) = U.setIndex (id elt) i l
    allocList msg size = ListWord32 <$> U.allocList32 msg size
instance ListElem msg Word64 where
    newtype List msg Word64 = ListWord64 (U.ListOf msg Word64)
    length (ListWord64 l) = U.length l
    index i (ListWord64 l) = id <$> U.index i l
instance MutListElem s Word64 where
    setIndex elt i (ListWord64 l) = U.setIndex (id elt) i l
    allocList msg size = ListWord64 <$> U.allocList64 msg size
instance ListElem msg Float where
    newtype List msg Float = ListFloat (U.ListOf msg Word32)
    length (ListFloat l) = U.length l
    index i (ListFloat l) = wordToFloat <$> U.index i l
instance MutListElem s Float where
    setIndex elt i (ListFloat l) = U.setIndex (floatToWord elt) i l
    allocList msg size = ListFloat <$> U.allocList32 msg size
instance ListElem msg Double where
    newtype List msg Double = ListDouble (U.ListOf msg Word64)
    length (ListDouble l) = U.length l
    index i (ListDouble l) = wordToDouble <$> U.index i l
instance MutListElem s Double where
    setIndex elt i (ListDouble l) = U.setIndex (doubleToWord elt) i l
    allocList msg size = ListDouble <$> U.allocList64 msg size
instance ListElem msg Bool where
    newtype List msg Bool = ListBool (U.ListOf msg Bool)
    length (ListBool l) = U.length l
    index i (ListBool l) = id <$> U.index i l
instance MutListElem s Bool where
    setIndex elt i (ListBool l) = U.setIndex (id elt) i l
    allocList msg size = ListBool <$> U.allocList1 msg size
