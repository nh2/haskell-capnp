{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}
{- |
Module: Capnp.Gen.Echo.Pure
Description: High-level generated module for echo.capnp
This module is the generated code for echo.capnp,
for the high-level api.
-}
module Capnp.Gen.Echo.Pure (Echo(..), Echo'server_(..),export_Echo, Echo'echo'params(..), Echo'echo'results(..)
) where
-- Code generated by capnpc-haskell. DO NOT EDIT.
-- Generated from schema file: echo.capnp
import Data.Int
import Data.Word
import Data.Default (Default(def))
import GHC.Generics (Generic)
import Capnp.Basics.Pure (Data, Text)
import Control.Monad.Catch (MonadThrow(throwM))
import Capnp.TraversalLimit (MonadLimit, evalLimitT)
import Control.Monad (forM_)
import qualified Capnp.Convert as Convert
import qualified Capnp.Message as M'
import qualified Capnp.Untyped as U'
import qualified Capnp.Untyped.Pure as PU'
import qualified Capnp.GenHelpers.Pure as PH'
import qualified Capnp.Classes as C'
import qualified Capnp.Rpc as Rpc
import qualified Capnp.Gen.Capnp.Rpc.Pure as Rpc
import qualified Capnp.GenHelpers.Rpc as RH'
import qualified Data.Vector as V
import qualified Data.ByteString as BS
import qualified Capnp.Gen.ById.Xd0a87f36fa0182f5
newtype Echo = Echo M'.Client
    deriving(Show, Eq, Read, Generic)
instance Rpc.IsClient Echo where
    fromClient = Echo
    toClient (Echo client) = client
instance C'.Decerialize Echo where
    type Cerial msg Echo = Capnp.Gen.ById.Xd0a87f36fa0182f5.Echo msg
    decerialize (Capnp.Gen.ById.Xd0a87f36fa0182f5.Echo Nothing) = pure $ Echo M'.nullClient
    decerialize (Capnp.Gen.ById.Xd0a87f36fa0182f5.Echo (Just cap)) = Echo <$> U'.getClient cap
instance C'.Cerialize s Echo where
    cerialize msg (Echo client) = Capnp.Gen.ById.Xd0a87f36fa0182f5.Echo . Just <$> U'.appendCap msg client
class Echo'server_ cap where
    {-# MINIMAL echo'echo #-}
    echo'echo :: Echo'echo'params -> cap -> Rpc.RpcT IO (Echo'echo'results)
    echo'echo _ _ = Rpc.throwMethodUnimplemented
export_Echo :: Echo'server_ a => a -> Rpc.RpcT IO Echo
export_Echo server_ = Echo <$> Rpc.export Rpc.Server
    { handleStop = pure () -- TODO
    , handleCall = \interfaceId methodId payload -> case interfaceId of
        16940812395455687611 -> case methodId of
            0 -> do
                RH'.handleMethod server_ echo'echo payload
            _ -> Rpc.throwMethodUnimplemented
        _ -> Rpc.throwMethodUnimplemented
    }
instance Echo'server_ Echo where
    echo'echo args (Echo client) = do
        args' <- PH'.createPure maxBound $ Convert.valueToMsg args >>= PH'.getRoot
        resultPromise <- Rpc.call 16940812395455687611 0 (Just (U'.PtrStruct args')) client
        result <- Rpc.waitIO resultPromise
        evalLimitT maxBound $ PH'.convertValue result
data Echo'echo'params
    = Echo'echo'params
        {query :: Text}
    deriving(Show,Read,Eq,Generic)
instance C'.Decerialize Echo'echo'params where
    type Cerial msg Echo'echo'params = Capnp.Gen.ById.Xd0a87f36fa0182f5.Echo'echo'params msg
    decerialize raw = do
        Echo'echo'params <$>
            (Capnp.Gen.ById.Xd0a87f36fa0182f5.get_Echo'echo'params'query raw >>= C'.decerialize)
instance C'.Marshal Echo'echo'params where
    marshalInto raw value = do
        case value of
            Echo'echo'params{..} -> do
                field_ <- C'.cerialize (U'.message raw) query
                Capnp.Gen.ById.Xd0a87f36fa0182f5.set_Echo'echo'params'query raw field_
instance C'.Cerialize s Echo'echo'params
instance C'.FromStruct M'.ConstMsg Echo'echo'params where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.Gen.ById.Xd0a87f36fa0182f5.Echo'echo'params M'.ConstMsg)
instance Default Echo'echo'params where
    def = PH'.defaultStruct
data Echo'echo'results
    = Echo'echo'results
        {reply :: Text}
    deriving(Show,Read,Eq,Generic)
instance C'.Decerialize Echo'echo'results where
    type Cerial msg Echo'echo'results = Capnp.Gen.ById.Xd0a87f36fa0182f5.Echo'echo'results msg
    decerialize raw = do
        Echo'echo'results <$>
            (Capnp.Gen.ById.Xd0a87f36fa0182f5.get_Echo'echo'results'reply raw >>= C'.decerialize)
instance C'.Marshal Echo'echo'results where
    marshalInto raw value = do
        case value of
            Echo'echo'results{..} -> do
                field_ <- C'.cerialize (U'.message raw) reply
                Capnp.Gen.ById.Xd0a87f36fa0182f5.set_Echo'echo'results'reply raw field_
instance C'.Cerialize s Echo'echo'results
instance C'.FromStruct M'.ConstMsg Echo'echo'results where
    fromStruct struct = do
        raw <- C'.fromStruct struct
        C'.decerialize (raw :: Capnp.Gen.ById.Xd0a87f36fa0182f5.Echo'echo'results M'.ConstMsg)
instance Default Echo'echo'results where
    def = PH'.defaultStruct