{-# LANGUAGE ScopedTypeVariables #-}
import Prelude hiding (length)

import Capnp.Addressbook
import Data.Capnp
    (ConstMsg, defaultLimit, evalLimitT, getValue, index, length, textBytes)

import Control.Monad             (forM_)
import Control.Monad.Trans.Class (lift)

import qualified Data.ByteString.Char8 as BS8

main = do
    addressbook :: AddressBook ConstMsg <- getValue defaultLimit
    evalLimitT defaultLimit $ do
        people <- get_AddressBook'people addressbook
        forM_ [0..length people - 1] $ \i -> do
            name <- index i people >>= get_Person'name >>= textBytes
            lift $ BS8.putStrLn name
