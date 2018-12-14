{-# OPTIONS_GHC -Wno-unused-imports #-}
{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{- |
Module: Capnp.Gen.Calculator
Description: Low-level generated module for calculator.capnp
This module is the generated code for calculator.capnp, for the
low-level api.
-}
module Capnp.Gen.Calculator where
-- Code generated by capnpc-haskell. DO NOT EDIT.
-- Generated from schema file: calculator.capnp
import Data.Int
import Data.Word
import GHC.Generics (Generic)
import Capnp.Bits (Word1)
import qualified Data.Bits
import qualified Data.Maybe
import qualified Data.ByteString
import qualified Capnp.Classes as C'
import qualified Capnp.Basics as B'
import qualified Capnp.GenHelpers as H'
import qualified Capnp.TraversalLimit as TL'
import qualified Capnp.Untyped as U'
import qualified Capnp.Message as M'
newtype Calculator msg = Calculator (Maybe (U'.Cap msg))
instance C'.FromPtr msg (Calculator msg) where
    fromPtr msg cap = Calculator <$> C'.fromPtr msg cap
instance C'.ToPtr s (Calculator (M'.MutMsg s)) where
    toPtr msg (Calculator Nothing) = pure Nothing
    toPtr msg (Calculator (Just cap)) = pure $ Just $ U'.PtrCap cap
newtype Expression msg = Expression_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Expression where
    tMsg f (Expression_newtype_ s) = Expression_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Expression msg) where
    fromStruct = pure . Expression_newtype_
instance C'.ToStruct msg (Expression msg) where
    toStruct (Expression_newtype_ struct) = struct
instance U'.HasMessage (Expression msg) where
    type InMessage (Expression msg) = msg
    message (Expression_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Expression msg) where
    messageDefault = Expression_newtype_ . U'.messageDefault
instance B'.ListElem msg (Expression msg) where
    newtype List msg (Expression msg) = List_Expression (U'.ListOf msg (U'.Struct msg))
    listFromPtr msg ptr = List_Expression <$> C'.fromPtr msg ptr
    toUntypedList (List_Expression l) = U'.ListStruct l
    length (List_Expression l) = U'.length l
    index i (List_Expression l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (Expression msg); go = C'.fromStruct} in go)
instance C'.FromPtr msg (Expression msg) where
    fromPtr msg ptr = Expression_newtype_ <$> C'.fromPtr msg ptr
instance C'.ToPtr s (Expression (M'.MutMsg s)) where
    toPtr msg (Expression_newtype_ struct) = C'.toPtr msg struct
instance B'.MutListElem s (Expression (M'.MutMsg s)) where
    setIndex (Expression_newtype_ elt) i (List_Expression l) = U'.setIndex elt i l
    newList msg len = List_Expression <$> U'.allocCompositeList msg 2 2 len
instance C'.Allocate s (Expression (M'.MutMsg s)) where
    new msg = Expression_newtype_ <$> U'.allocStruct msg 2 2
data Expression' msg
    = Expression'literal Double
    | Expression'previousResult (Value msg)
    | Expression'parameter Word32
    | Expression'call (Expression'call'group' msg)
    | Expression'unknown' Word16
get_Expression' :: U'.ReadCtx m msg => Expression msg -> m (Expression' msg)
get_Expression' (Expression_newtype_ struct) = C'.fromStruct struct
set_Expression'literal :: U'.RWCtx m s => Expression (M'.MutMsg s) -> Double -> m ()
set_Expression'literal (Expression_newtype_ struct) value = do
    H'.setWordField struct (0 :: Word16) 1 0 0
    H'.setWordField struct (fromIntegral (C'.toWord value) :: Word64) 0 0 0
set_Expression'previousResult :: U'.RWCtx m s => Expression (M'.MutMsg s) -> (Value (M'.MutMsg s)) -> m ()
set_Expression'previousResult(Expression_newtype_ struct) value = do
    H'.setWordField struct (1 :: Word16) 1 0 0
    ptr <- C'.toPtr (U'.message struct) value
    U'.setPtr ptr 0 struct
set_Expression'parameter :: U'.RWCtx m s => Expression (M'.MutMsg s) -> Word32 -> m ()
set_Expression'parameter (Expression_newtype_ struct) value = do
    H'.setWordField struct (2 :: Word16) 1 0 0
    H'.setWordField struct (fromIntegral (C'.toWord value) :: Word32) 0 0 0
set_Expression'call :: U'.RWCtx m s => Expression (M'.MutMsg s) -> m (Expression'call'group' (M'.MutMsg s))
set_Expression'call (Expression_newtype_ struct) = do
    H'.setWordField struct (3 :: Word16) 1 0 0
    pure $ Expression'call'group'_newtype_ struct
set_Expression'unknown' :: U'.RWCtx m s => Expression (M'.MutMsg s) -> Word16 -> m ()
set_Expression'unknown'(Expression_newtype_ struct) tagValue = H'.setWordField struct (tagValue :: Word16) 1 0 0
newtype Expression'call'group' msg = Expression'call'group'_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Expression'call'group' where
    tMsg f (Expression'call'group'_newtype_ s) = Expression'call'group'_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Expression'call'group' msg) where
    fromStruct = pure . Expression'call'group'_newtype_
instance C'.ToStruct msg (Expression'call'group' msg) where
    toStruct (Expression'call'group'_newtype_ struct) = struct
instance U'.HasMessage (Expression'call'group' msg) where
    type InMessage (Expression'call'group' msg) = msg
    message (Expression'call'group'_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Expression'call'group' msg) where
    messageDefault = Expression'call'group'_newtype_ . U'.messageDefault
get_Expression'call'function :: U'.ReadCtx m msg => Expression'call'group' msg -> m (Function msg)
get_Expression'call'function (Expression'call'group'_newtype_ struct) =
    U'.getPtr 0 struct
    >>= C'.fromPtr (U'.message struct)
has_Expression'call'function :: U'.ReadCtx m msg => Expression'call'group' msg -> m Bool
has_Expression'call'function(Expression'call'group'_newtype_ struct) = Data.Maybe.isJust <$> U'.getPtr 0 struct
set_Expression'call'function :: U'.RWCtx m s => Expression'call'group' (M'.MutMsg s) -> (Function (M'.MutMsg s)) -> m ()
set_Expression'call'function (Expression'call'group'_newtype_ struct) value = do
    ptr <- C'.toPtr (U'.message struct) value
    U'.setPtr ptr 0 struct
get_Expression'call'params :: U'.ReadCtx m msg => Expression'call'group' msg -> m (B'.List msg (Expression msg))
get_Expression'call'params (Expression'call'group'_newtype_ struct) =
    U'.getPtr 1 struct
    >>= C'.fromPtr (U'.message struct)
has_Expression'call'params :: U'.ReadCtx m msg => Expression'call'group' msg -> m Bool
has_Expression'call'params(Expression'call'group'_newtype_ struct) = Data.Maybe.isJust <$> U'.getPtr 1 struct
set_Expression'call'params :: U'.RWCtx m s => Expression'call'group' (M'.MutMsg s) -> (B'.List (M'.MutMsg s) (Expression (M'.MutMsg s))) -> m ()
set_Expression'call'params (Expression'call'group'_newtype_ struct) value = do
    ptr <- C'.toPtr (U'.message struct) value
    U'.setPtr ptr 1 struct
new_Expression'call'params :: U'.RWCtx m s => Int -> Expression'call'group' (M'.MutMsg s) -> m ((B'.List (M'.MutMsg s) (Expression (M'.MutMsg s))))
new_Expression'call'params len struct = do
    result <- C'.newList (U'.message struct) len
    set_Expression'call'params struct result
    pure result
instance C'.FromStruct msg (Expression' msg) where
    fromStruct struct = do
        tag <-  H'.getWordField struct 1 0 0
        case tag of
            3 -> Expression'call <$> C'.fromStruct struct
            2 -> Expression'parameter <$>  H'.getWordField struct 0 0 0
            1 -> Expression'previousResult <$>  (U'.getPtr 0 struct >>= C'.fromPtr (U'.message struct))
            0 -> Expression'literal <$>  H'.getWordField struct 0 0 0
            _ -> pure $ Expression'unknown' tag
newtype Function msg = Function (Maybe (U'.Cap msg))
instance C'.FromPtr msg (Function msg) where
    fromPtr msg cap = Function <$> C'.fromPtr msg cap
instance C'.ToPtr s (Function (M'.MutMsg s)) where
    toPtr msg (Function Nothing) = pure Nothing
    toPtr msg (Function (Just cap)) = pure $ Just $ U'.PtrCap cap
data Operator
    = Operator'add
    | Operator'subtract
    | Operator'multiply
    | Operator'divide
    | Operator'unknown' Word16
    deriving(Show,Read,Eq,Generic)
instance Enum Operator where
    toEnum = C'.fromWord . fromIntegral
    fromEnum = fromIntegral . C'.toWord
instance C'.IsWord Operator where
    fromWord n = go (fromIntegral n :: Word16) where
        go 0 = Operator'add
        go 1 = Operator'subtract
        go 2 = Operator'multiply
        go 3 = Operator'divide
        go tag = Operator'unknown' (fromIntegral tag)
    toWord Operator'add = 0
    toWord Operator'subtract = 1
    toWord Operator'multiply = 2
    toWord Operator'divide = 3
    toWord (Operator'unknown' tag) = fromIntegral tag
instance B'.ListElem msg Operator where
    newtype List msg Operator = List_Operator (U'.ListOf msg Word16)
    listFromPtr msg ptr = List_Operator <$> C'.fromPtr msg ptr
    toUntypedList (List_Operator l) = U'.List16 l
    length (List_Operator l) = U'.length l
    index i (List_Operator l) = (C'.fromWord . fromIntegral) <$> U'.index i l
instance B'.MutListElem s Operator where
    setIndex elt i (List_Operator l) = U'.setIndex (fromIntegral $ C'.toWord elt) i l
    newList msg size = List_Operator <$> U'.allocList16 msg size
newtype Value msg = Value (Maybe (U'.Cap msg))
instance C'.FromPtr msg (Value msg) where
    fromPtr msg cap = Value <$> C'.fromPtr msg cap
instance C'.ToPtr s (Value (M'.MutMsg s)) where
    toPtr msg (Value Nothing) = pure Nothing
    toPtr msg (Value (Just cap)) = pure $ Just $ U'.PtrCap cap
newtype Calculator'defFunction'params msg = Calculator'defFunction'params_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Calculator'defFunction'params where
    tMsg f (Calculator'defFunction'params_newtype_ s) = Calculator'defFunction'params_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Calculator'defFunction'params msg) where
    fromStruct = pure . Calculator'defFunction'params_newtype_
instance C'.ToStruct msg (Calculator'defFunction'params msg) where
    toStruct (Calculator'defFunction'params_newtype_ struct) = struct
instance U'.HasMessage (Calculator'defFunction'params msg) where
    type InMessage (Calculator'defFunction'params msg) = msg
    message (Calculator'defFunction'params_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Calculator'defFunction'params msg) where
    messageDefault = Calculator'defFunction'params_newtype_ . U'.messageDefault
instance B'.ListElem msg (Calculator'defFunction'params msg) where
    newtype List msg (Calculator'defFunction'params msg) = List_Calculator'defFunction'params (U'.ListOf msg (U'.Struct msg))
    listFromPtr msg ptr = List_Calculator'defFunction'params <$> C'.fromPtr msg ptr
    toUntypedList (List_Calculator'defFunction'params l) = U'.ListStruct l
    length (List_Calculator'defFunction'params l) = U'.length l
    index i (List_Calculator'defFunction'params l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (Calculator'defFunction'params msg); go = C'.fromStruct} in go)
instance C'.FromPtr msg (Calculator'defFunction'params msg) where
    fromPtr msg ptr = Calculator'defFunction'params_newtype_ <$> C'.fromPtr msg ptr
instance C'.ToPtr s (Calculator'defFunction'params (M'.MutMsg s)) where
    toPtr msg (Calculator'defFunction'params_newtype_ struct) = C'.toPtr msg struct
instance B'.MutListElem s (Calculator'defFunction'params (M'.MutMsg s)) where
    setIndex (Calculator'defFunction'params_newtype_ elt) i (List_Calculator'defFunction'params l) = U'.setIndex elt i l
    newList msg len = List_Calculator'defFunction'params <$> U'.allocCompositeList msg 1 1 len
instance C'.Allocate s (Calculator'defFunction'params (M'.MutMsg s)) where
    new msg = Calculator'defFunction'params_newtype_ <$> U'.allocStruct msg 1 1
get_Calculator'defFunction'params'paramCount :: U'.ReadCtx m msg => Calculator'defFunction'params msg -> m Int32
get_Calculator'defFunction'params'paramCount (Calculator'defFunction'params_newtype_ struct) = H'.getWordField struct 0 0 0
set_Calculator'defFunction'params'paramCount :: U'.RWCtx m s => Calculator'defFunction'params (M'.MutMsg s) -> Int32 -> m ()
set_Calculator'defFunction'params'paramCount (Calculator'defFunction'params_newtype_ struct) value = H'.setWordField struct (fromIntegral (C'.toWord value) :: Word32) 0 0 0
get_Calculator'defFunction'params'body :: U'.ReadCtx m msg => Calculator'defFunction'params msg -> m (Expression msg)
get_Calculator'defFunction'params'body (Calculator'defFunction'params_newtype_ struct) =
    U'.getPtr 0 struct
    >>= C'.fromPtr (U'.message struct)
has_Calculator'defFunction'params'body :: U'.ReadCtx m msg => Calculator'defFunction'params msg -> m Bool
has_Calculator'defFunction'params'body(Calculator'defFunction'params_newtype_ struct) = Data.Maybe.isJust <$> U'.getPtr 0 struct
set_Calculator'defFunction'params'body :: U'.RWCtx m s => Calculator'defFunction'params (M'.MutMsg s) -> (Expression (M'.MutMsg s)) -> m ()
set_Calculator'defFunction'params'body (Calculator'defFunction'params_newtype_ struct) value = do
    ptr <- C'.toPtr (U'.message struct) value
    U'.setPtr ptr 0 struct
new_Calculator'defFunction'params'body :: U'.RWCtx m s => Calculator'defFunction'params (M'.MutMsg s) -> m ((Expression (M'.MutMsg s)))
new_Calculator'defFunction'params'body struct = do
    result <- C'.new (U'.message struct)
    set_Calculator'defFunction'params'body struct result
    pure result
newtype Calculator'defFunction'results msg = Calculator'defFunction'results_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Calculator'defFunction'results where
    tMsg f (Calculator'defFunction'results_newtype_ s) = Calculator'defFunction'results_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Calculator'defFunction'results msg) where
    fromStruct = pure . Calculator'defFunction'results_newtype_
instance C'.ToStruct msg (Calculator'defFunction'results msg) where
    toStruct (Calculator'defFunction'results_newtype_ struct) = struct
instance U'.HasMessage (Calculator'defFunction'results msg) where
    type InMessage (Calculator'defFunction'results msg) = msg
    message (Calculator'defFunction'results_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Calculator'defFunction'results msg) where
    messageDefault = Calculator'defFunction'results_newtype_ . U'.messageDefault
instance B'.ListElem msg (Calculator'defFunction'results msg) where
    newtype List msg (Calculator'defFunction'results msg) = List_Calculator'defFunction'results (U'.ListOf msg (U'.Struct msg))
    listFromPtr msg ptr = List_Calculator'defFunction'results <$> C'.fromPtr msg ptr
    toUntypedList (List_Calculator'defFunction'results l) = U'.ListStruct l
    length (List_Calculator'defFunction'results l) = U'.length l
    index i (List_Calculator'defFunction'results l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (Calculator'defFunction'results msg); go = C'.fromStruct} in go)
instance C'.FromPtr msg (Calculator'defFunction'results msg) where
    fromPtr msg ptr = Calculator'defFunction'results_newtype_ <$> C'.fromPtr msg ptr
instance C'.ToPtr s (Calculator'defFunction'results (M'.MutMsg s)) where
    toPtr msg (Calculator'defFunction'results_newtype_ struct) = C'.toPtr msg struct
instance B'.MutListElem s (Calculator'defFunction'results (M'.MutMsg s)) where
    setIndex (Calculator'defFunction'results_newtype_ elt) i (List_Calculator'defFunction'results l) = U'.setIndex elt i l
    newList msg len = List_Calculator'defFunction'results <$> U'.allocCompositeList msg 0 1 len
instance C'.Allocate s (Calculator'defFunction'results (M'.MutMsg s)) where
    new msg = Calculator'defFunction'results_newtype_ <$> U'.allocStruct msg 0 1
get_Calculator'defFunction'results'func :: U'.ReadCtx m msg => Calculator'defFunction'results msg -> m (Function msg)
get_Calculator'defFunction'results'func (Calculator'defFunction'results_newtype_ struct) =
    U'.getPtr 0 struct
    >>= C'.fromPtr (U'.message struct)
has_Calculator'defFunction'results'func :: U'.ReadCtx m msg => Calculator'defFunction'results msg -> m Bool
has_Calculator'defFunction'results'func(Calculator'defFunction'results_newtype_ struct) = Data.Maybe.isJust <$> U'.getPtr 0 struct
set_Calculator'defFunction'results'func :: U'.RWCtx m s => Calculator'defFunction'results (M'.MutMsg s) -> (Function (M'.MutMsg s)) -> m ()
set_Calculator'defFunction'results'func (Calculator'defFunction'results_newtype_ struct) value = do
    ptr <- C'.toPtr (U'.message struct) value
    U'.setPtr ptr 0 struct
newtype Calculator'evaluate'params msg = Calculator'evaluate'params_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Calculator'evaluate'params where
    tMsg f (Calculator'evaluate'params_newtype_ s) = Calculator'evaluate'params_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Calculator'evaluate'params msg) where
    fromStruct = pure . Calculator'evaluate'params_newtype_
instance C'.ToStruct msg (Calculator'evaluate'params msg) where
    toStruct (Calculator'evaluate'params_newtype_ struct) = struct
instance U'.HasMessage (Calculator'evaluate'params msg) where
    type InMessage (Calculator'evaluate'params msg) = msg
    message (Calculator'evaluate'params_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Calculator'evaluate'params msg) where
    messageDefault = Calculator'evaluate'params_newtype_ . U'.messageDefault
instance B'.ListElem msg (Calculator'evaluate'params msg) where
    newtype List msg (Calculator'evaluate'params msg) = List_Calculator'evaluate'params (U'.ListOf msg (U'.Struct msg))
    listFromPtr msg ptr = List_Calculator'evaluate'params <$> C'.fromPtr msg ptr
    toUntypedList (List_Calculator'evaluate'params l) = U'.ListStruct l
    length (List_Calculator'evaluate'params l) = U'.length l
    index i (List_Calculator'evaluate'params l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (Calculator'evaluate'params msg); go = C'.fromStruct} in go)
instance C'.FromPtr msg (Calculator'evaluate'params msg) where
    fromPtr msg ptr = Calculator'evaluate'params_newtype_ <$> C'.fromPtr msg ptr
instance C'.ToPtr s (Calculator'evaluate'params (M'.MutMsg s)) where
    toPtr msg (Calculator'evaluate'params_newtype_ struct) = C'.toPtr msg struct
instance B'.MutListElem s (Calculator'evaluate'params (M'.MutMsg s)) where
    setIndex (Calculator'evaluate'params_newtype_ elt) i (List_Calculator'evaluate'params l) = U'.setIndex elt i l
    newList msg len = List_Calculator'evaluate'params <$> U'.allocCompositeList msg 0 1 len
instance C'.Allocate s (Calculator'evaluate'params (M'.MutMsg s)) where
    new msg = Calculator'evaluate'params_newtype_ <$> U'.allocStruct msg 0 1
get_Calculator'evaluate'params'expression :: U'.ReadCtx m msg => Calculator'evaluate'params msg -> m (Expression msg)
get_Calculator'evaluate'params'expression (Calculator'evaluate'params_newtype_ struct) =
    U'.getPtr 0 struct
    >>= C'.fromPtr (U'.message struct)
has_Calculator'evaluate'params'expression :: U'.ReadCtx m msg => Calculator'evaluate'params msg -> m Bool
has_Calculator'evaluate'params'expression(Calculator'evaluate'params_newtype_ struct) = Data.Maybe.isJust <$> U'.getPtr 0 struct
set_Calculator'evaluate'params'expression :: U'.RWCtx m s => Calculator'evaluate'params (M'.MutMsg s) -> (Expression (M'.MutMsg s)) -> m ()
set_Calculator'evaluate'params'expression (Calculator'evaluate'params_newtype_ struct) value = do
    ptr <- C'.toPtr (U'.message struct) value
    U'.setPtr ptr 0 struct
new_Calculator'evaluate'params'expression :: U'.RWCtx m s => Calculator'evaluate'params (M'.MutMsg s) -> m ((Expression (M'.MutMsg s)))
new_Calculator'evaluate'params'expression struct = do
    result <- C'.new (U'.message struct)
    set_Calculator'evaluate'params'expression struct result
    pure result
newtype Calculator'evaluate'results msg = Calculator'evaluate'results_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Calculator'evaluate'results where
    tMsg f (Calculator'evaluate'results_newtype_ s) = Calculator'evaluate'results_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Calculator'evaluate'results msg) where
    fromStruct = pure . Calculator'evaluate'results_newtype_
instance C'.ToStruct msg (Calculator'evaluate'results msg) where
    toStruct (Calculator'evaluate'results_newtype_ struct) = struct
instance U'.HasMessage (Calculator'evaluate'results msg) where
    type InMessage (Calculator'evaluate'results msg) = msg
    message (Calculator'evaluate'results_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Calculator'evaluate'results msg) where
    messageDefault = Calculator'evaluate'results_newtype_ . U'.messageDefault
instance B'.ListElem msg (Calculator'evaluate'results msg) where
    newtype List msg (Calculator'evaluate'results msg) = List_Calculator'evaluate'results (U'.ListOf msg (U'.Struct msg))
    listFromPtr msg ptr = List_Calculator'evaluate'results <$> C'.fromPtr msg ptr
    toUntypedList (List_Calculator'evaluate'results l) = U'.ListStruct l
    length (List_Calculator'evaluate'results l) = U'.length l
    index i (List_Calculator'evaluate'results l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (Calculator'evaluate'results msg); go = C'.fromStruct} in go)
instance C'.FromPtr msg (Calculator'evaluate'results msg) where
    fromPtr msg ptr = Calculator'evaluate'results_newtype_ <$> C'.fromPtr msg ptr
instance C'.ToPtr s (Calculator'evaluate'results (M'.MutMsg s)) where
    toPtr msg (Calculator'evaluate'results_newtype_ struct) = C'.toPtr msg struct
instance B'.MutListElem s (Calculator'evaluate'results (M'.MutMsg s)) where
    setIndex (Calculator'evaluate'results_newtype_ elt) i (List_Calculator'evaluate'results l) = U'.setIndex elt i l
    newList msg len = List_Calculator'evaluate'results <$> U'.allocCompositeList msg 0 1 len
instance C'.Allocate s (Calculator'evaluate'results (M'.MutMsg s)) where
    new msg = Calculator'evaluate'results_newtype_ <$> U'.allocStruct msg 0 1
get_Calculator'evaluate'results'value :: U'.ReadCtx m msg => Calculator'evaluate'results msg -> m (Value msg)
get_Calculator'evaluate'results'value (Calculator'evaluate'results_newtype_ struct) =
    U'.getPtr 0 struct
    >>= C'.fromPtr (U'.message struct)
has_Calculator'evaluate'results'value :: U'.ReadCtx m msg => Calculator'evaluate'results msg -> m Bool
has_Calculator'evaluate'results'value(Calculator'evaluate'results_newtype_ struct) = Data.Maybe.isJust <$> U'.getPtr 0 struct
set_Calculator'evaluate'results'value :: U'.RWCtx m s => Calculator'evaluate'results (M'.MutMsg s) -> (Value (M'.MutMsg s)) -> m ()
set_Calculator'evaluate'results'value (Calculator'evaluate'results_newtype_ struct) value = do
    ptr <- C'.toPtr (U'.message struct) value
    U'.setPtr ptr 0 struct
newtype Calculator'getOperator'params msg = Calculator'getOperator'params_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Calculator'getOperator'params where
    tMsg f (Calculator'getOperator'params_newtype_ s) = Calculator'getOperator'params_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Calculator'getOperator'params msg) where
    fromStruct = pure . Calculator'getOperator'params_newtype_
instance C'.ToStruct msg (Calculator'getOperator'params msg) where
    toStruct (Calculator'getOperator'params_newtype_ struct) = struct
instance U'.HasMessage (Calculator'getOperator'params msg) where
    type InMessage (Calculator'getOperator'params msg) = msg
    message (Calculator'getOperator'params_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Calculator'getOperator'params msg) where
    messageDefault = Calculator'getOperator'params_newtype_ . U'.messageDefault
instance B'.ListElem msg (Calculator'getOperator'params msg) where
    newtype List msg (Calculator'getOperator'params msg) = List_Calculator'getOperator'params (U'.ListOf msg (U'.Struct msg))
    listFromPtr msg ptr = List_Calculator'getOperator'params <$> C'.fromPtr msg ptr
    toUntypedList (List_Calculator'getOperator'params l) = U'.ListStruct l
    length (List_Calculator'getOperator'params l) = U'.length l
    index i (List_Calculator'getOperator'params l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (Calculator'getOperator'params msg); go = C'.fromStruct} in go)
instance C'.FromPtr msg (Calculator'getOperator'params msg) where
    fromPtr msg ptr = Calculator'getOperator'params_newtype_ <$> C'.fromPtr msg ptr
instance C'.ToPtr s (Calculator'getOperator'params (M'.MutMsg s)) where
    toPtr msg (Calculator'getOperator'params_newtype_ struct) = C'.toPtr msg struct
instance B'.MutListElem s (Calculator'getOperator'params (M'.MutMsg s)) where
    setIndex (Calculator'getOperator'params_newtype_ elt) i (List_Calculator'getOperator'params l) = U'.setIndex elt i l
    newList msg len = List_Calculator'getOperator'params <$> U'.allocCompositeList msg 1 0 len
instance C'.Allocate s (Calculator'getOperator'params (M'.MutMsg s)) where
    new msg = Calculator'getOperator'params_newtype_ <$> U'.allocStruct msg 1 0
get_Calculator'getOperator'params'op :: U'.ReadCtx m msg => Calculator'getOperator'params msg -> m Operator
get_Calculator'getOperator'params'op (Calculator'getOperator'params_newtype_ struct) = H'.getWordField struct 0 0 0
set_Calculator'getOperator'params'op :: U'.RWCtx m s => Calculator'getOperator'params (M'.MutMsg s) -> Operator -> m ()
set_Calculator'getOperator'params'op (Calculator'getOperator'params_newtype_ struct) value = H'.setWordField struct (fromIntegral (C'.toWord value) :: Word16) 0 0 0
newtype Calculator'getOperator'results msg = Calculator'getOperator'results_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Calculator'getOperator'results where
    tMsg f (Calculator'getOperator'results_newtype_ s) = Calculator'getOperator'results_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Calculator'getOperator'results msg) where
    fromStruct = pure . Calculator'getOperator'results_newtype_
instance C'.ToStruct msg (Calculator'getOperator'results msg) where
    toStruct (Calculator'getOperator'results_newtype_ struct) = struct
instance U'.HasMessage (Calculator'getOperator'results msg) where
    type InMessage (Calculator'getOperator'results msg) = msg
    message (Calculator'getOperator'results_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Calculator'getOperator'results msg) where
    messageDefault = Calculator'getOperator'results_newtype_ . U'.messageDefault
instance B'.ListElem msg (Calculator'getOperator'results msg) where
    newtype List msg (Calculator'getOperator'results msg) = List_Calculator'getOperator'results (U'.ListOf msg (U'.Struct msg))
    listFromPtr msg ptr = List_Calculator'getOperator'results <$> C'.fromPtr msg ptr
    toUntypedList (List_Calculator'getOperator'results l) = U'.ListStruct l
    length (List_Calculator'getOperator'results l) = U'.length l
    index i (List_Calculator'getOperator'results l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (Calculator'getOperator'results msg); go = C'.fromStruct} in go)
instance C'.FromPtr msg (Calculator'getOperator'results msg) where
    fromPtr msg ptr = Calculator'getOperator'results_newtype_ <$> C'.fromPtr msg ptr
instance C'.ToPtr s (Calculator'getOperator'results (M'.MutMsg s)) where
    toPtr msg (Calculator'getOperator'results_newtype_ struct) = C'.toPtr msg struct
instance B'.MutListElem s (Calculator'getOperator'results (M'.MutMsg s)) where
    setIndex (Calculator'getOperator'results_newtype_ elt) i (List_Calculator'getOperator'results l) = U'.setIndex elt i l
    newList msg len = List_Calculator'getOperator'results <$> U'.allocCompositeList msg 0 1 len
instance C'.Allocate s (Calculator'getOperator'results (M'.MutMsg s)) where
    new msg = Calculator'getOperator'results_newtype_ <$> U'.allocStruct msg 0 1
get_Calculator'getOperator'results'func :: U'.ReadCtx m msg => Calculator'getOperator'results msg -> m (Function msg)
get_Calculator'getOperator'results'func (Calculator'getOperator'results_newtype_ struct) =
    U'.getPtr 0 struct
    >>= C'.fromPtr (U'.message struct)
has_Calculator'getOperator'results'func :: U'.ReadCtx m msg => Calculator'getOperator'results msg -> m Bool
has_Calculator'getOperator'results'func(Calculator'getOperator'results_newtype_ struct) = Data.Maybe.isJust <$> U'.getPtr 0 struct
set_Calculator'getOperator'results'func :: U'.RWCtx m s => Calculator'getOperator'results (M'.MutMsg s) -> (Function (M'.MutMsg s)) -> m ()
set_Calculator'getOperator'results'func (Calculator'getOperator'results_newtype_ struct) value = do
    ptr <- C'.toPtr (U'.message struct) value
    U'.setPtr ptr 0 struct
newtype Function'call'params msg = Function'call'params_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Function'call'params where
    tMsg f (Function'call'params_newtype_ s) = Function'call'params_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Function'call'params msg) where
    fromStruct = pure . Function'call'params_newtype_
instance C'.ToStruct msg (Function'call'params msg) where
    toStruct (Function'call'params_newtype_ struct) = struct
instance U'.HasMessage (Function'call'params msg) where
    type InMessage (Function'call'params msg) = msg
    message (Function'call'params_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Function'call'params msg) where
    messageDefault = Function'call'params_newtype_ . U'.messageDefault
instance B'.ListElem msg (Function'call'params msg) where
    newtype List msg (Function'call'params msg) = List_Function'call'params (U'.ListOf msg (U'.Struct msg))
    listFromPtr msg ptr = List_Function'call'params <$> C'.fromPtr msg ptr
    toUntypedList (List_Function'call'params l) = U'.ListStruct l
    length (List_Function'call'params l) = U'.length l
    index i (List_Function'call'params l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (Function'call'params msg); go = C'.fromStruct} in go)
instance C'.FromPtr msg (Function'call'params msg) where
    fromPtr msg ptr = Function'call'params_newtype_ <$> C'.fromPtr msg ptr
instance C'.ToPtr s (Function'call'params (M'.MutMsg s)) where
    toPtr msg (Function'call'params_newtype_ struct) = C'.toPtr msg struct
instance B'.MutListElem s (Function'call'params (M'.MutMsg s)) where
    setIndex (Function'call'params_newtype_ elt) i (List_Function'call'params l) = U'.setIndex elt i l
    newList msg len = List_Function'call'params <$> U'.allocCompositeList msg 0 1 len
instance C'.Allocate s (Function'call'params (M'.MutMsg s)) where
    new msg = Function'call'params_newtype_ <$> U'.allocStruct msg 0 1
get_Function'call'params'params :: U'.ReadCtx m msg => Function'call'params msg -> m (B'.List msg Double)
get_Function'call'params'params (Function'call'params_newtype_ struct) =
    U'.getPtr 0 struct
    >>= C'.fromPtr (U'.message struct)
has_Function'call'params'params :: U'.ReadCtx m msg => Function'call'params msg -> m Bool
has_Function'call'params'params(Function'call'params_newtype_ struct) = Data.Maybe.isJust <$> U'.getPtr 0 struct
set_Function'call'params'params :: U'.RWCtx m s => Function'call'params (M'.MutMsg s) -> (B'.List (M'.MutMsg s) Double) -> m ()
set_Function'call'params'params (Function'call'params_newtype_ struct) value = do
    ptr <- C'.toPtr (U'.message struct) value
    U'.setPtr ptr 0 struct
new_Function'call'params'params :: U'.RWCtx m s => Int -> Function'call'params (M'.MutMsg s) -> m ((B'.List (M'.MutMsg s) Double))
new_Function'call'params'params len struct = do
    result <- C'.newList (U'.message struct) len
    set_Function'call'params'params struct result
    pure result
newtype Function'call'results msg = Function'call'results_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Function'call'results where
    tMsg f (Function'call'results_newtype_ s) = Function'call'results_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Function'call'results msg) where
    fromStruct = pure . Function'call'results_newtype_
instance C'.ToStruct msg (Function'call'results msg) where
    toStruct (Function'call'results_newtype_ struct) = struct
instance U'.HasMessage (Function'call'results msg) where
    type InMessage (Function'call'results msg) = msg
    message (Function'call'results_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Function'call'results msg) where
    messageDefault = Function'call'results_newtype_ . U'.messageDefault
instance B'.ListElem msg (Function'call'results msg) where
    newtype List msg (Function'call'results msg) = List_Function'call'results (U'.ListOf msg (U'.Struct msg))
    listFromPtr msg ptr = List_Function'call'results <$> C'.fromPtr msg ptr
    toUntypedList (List_Function'call'results l) = U'.ListStruct l
    length (List_Function'call'results l) = U'.length l
    index i (List_Function'call'results l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (Function'call'results msg); go = C'.fromStruct} in go)
instance C'.FromPtr msg (Function'call'results msg) where
    fromPtr msg ptr = Function'call'results_newtype_ <$> C'.fromPtr msg ptr
instance C'.ToPtr s (Function'call'results (M'.MutMsg s)) where
    toPtr msg (Function'call'results_newtype_ struct) = C'.toPtr msg struct
instance B'.MutListElem s (Function'call'results (M'.MutMsg s)) where
    setIndex (Function'call'results_newtype_ elt) i (List_Function'call'results l) = U'.setIndex elt i l
    newList msg len = List_Function'call'results <$> U'.allocCompositeList msg 1 0 len
instance C'.Allocate s (Function'call'results (M'.MutMsg s)) where
    new msg = Function'call'results_newtype_ <$> U'.allocStruct msg 1 0
get_Function'call'results'value :: U'.ReadCtx m msg => Function'call'results msg -> m Double
get_Function'call'results'value (Function'call'results_newtype_ struct) = H'.getWordField struct 0 0 0
set_Function'call'results'value :: U'.RWCtx m s => Function'call'results (M'.MutMsg s) -> Double -> m ()
set_Function'call'results'value (Function'call'results_newtype_ struct) value = H'.setWordField struct (fromIntegral (C'.toWord value) :: Word64) 0 0 0
newtype Value'read'params msg = Value'read'params_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Value'read'params where
    tMsg f (Value'read'params_newtype_ s) = Value'read'params_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Value'read'params msg) where
    fromStruct = pure . Value'read'params_newtype_
instance C'.ToStruct msg (Value'read'params msg) where
    toStruct (Value'read'params_newtype_ struct) = struct
instance U'.HasMessage (Value'read'params msg) where
    type InMessage (Value'read'params msg) = msg
    message (Value'read'params_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Value'read'params msg) where
    messageDefault = Value'read'params_newtype_ . U'.messageDefault
instance B'.ListElem msg (Value'read'params msg) where
    newtype List msg (Value'read'params msg) = List_Value'read'params (U'.ListOf msg (U'.Struct msg))
    listFromPtr msg ptr = List_Value'read'params <$> C'.fromPtr msg ptr
    toUntypedList (List_Value'read'params l) = U'.ListStruct l
    length (List_Value'read'params l) = U'.length l
    index i (List_Value'read'params l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (Value'read'params msg); go = C'.fromStruct} in go)
instance C'.FromPtr msg (Value'read'params msg) where
    fromPtr msg ptr = Value'read'params_newtype_ <$> C'.fromPtr msg ptr
instance C'.ToPtr s (Value'read'params (M'.MutMsg s)) where
    toPtr msg (Value'read'params_newtype_ struct) = C'.toPtr msg struct
instance B'.MutListElem s (Value'read'params (M'.MutMsg s)) where
    setIndex (Value'read'params_newtype_ elt) i (List_Value'read'params l) = U'.setIndex elt i l
    newList msg len = List_Value'read'params <$> U'.allocCompositeList msg 0 0 len
instance C'.Allocate s (Value'read'params (M'.MutMsg s)) where
    new msg = Value'read'params_newtype_ <$> U'.allocStruct msg 0 0
newtype Value'read'results msg = Value'read'results_newtype_ (U'.Struct msg)
instance U'.TraverseMsg Value'read'results where
    tMsg f (Value'read'results_newtype_ s) = Value'read'results_newtype_ <$> U'.tMsg f s
instance C'.FromStruct msg (Value'read'results msg) where
    fromStruct = pure . Value'read'results_newtype_
instance C'.ToStruct msg (Value'read'results msg) where
    toStruct (Value'read'results_newtype_ struct) = struct
instance U'.HasMessage (Value'read'results msg) where
    type InMessage (Value'read'results msg) = msg
    message (Value'read'results_newtype_ struct) = U'.message struct
instance U'.MessageDefault (Value'read'results msg) where
    messageDefault = Value'read'results_newtype_ . U'.messageDefault
instance B'.ListElem msg (Value'read'results msg) where
    newtype List msg (Value'read'results msg) = List_Value'read'results (U'.ListOf msg (U'.Struct msg))
    listFromPtr msg ptr = List_Value'read'results <$> C'.fromPtr msg ptr
    toUntypedList (List_Value'read'results l) = U'.ListStruct l
    length (List_Value'read'results l) = U'.length l
    index i (List_Value'read'results l) = U'.index i l >>= (let {go :: U'.ReadCtx m msg => U'.Struct msg -> m (Value'read'results msg); go = C'.fromStruct} in go)
instance C'.FromPtr msg (Value'read'results msg) where
    fromPtr msg ptr = Value'read'results_newtype_ <$> C'.fromPtr msg ptr
instance C'.ToPtr s (Value'read'results (M'.MutMsg s)) where
    toPtr msg (Value'read'results_newtype_ struct) = C'.toPtr msg struct
instance B'.MutListElem s (Value'read'results (M'.MutMsg s)) where
    setIndex (Value'read'results_newtype_ elt) i (List_Value'read'results l) = U'.setIndex elt i l
    newList msg len = List_Value'read'results <$> U'.allocCompositeList msg 1 0 len
instance C'.Allocate s (Value'read'results (M'.MutMsg s)) where
    new msg = Value'read'results_newtype_ <$> U'.allocStruct msg 1 0
get_Value'read'results'value :: U'.ReadCtx m msg => Value'read'results msg -> m Double
get_Value'read'results'value (Value'read'results_newtype_ struct) = H'.getWordField struct 0 0 0
set_Value'read'results'value :: U'.RWCtx m s => Value'read'results (M'.MutMsg s) -> Double -> m ()
set_Value'read'results'value (Value'read'results_newtype_ struct) value = H'.setWordField struct (fromIntegral (C'.toWord value) :: Word64) 0 0 0