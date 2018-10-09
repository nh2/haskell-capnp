{-# LANGUAGE OverloadedLabels    #-}
{-# LANGUAGE ScopedTypeVariables #-}
import Prelude hiding (length)

import Capnp.Addressbook
import Data.Capnp
    ( ConstMsg
    , defaultLimit
    , evalLimitT
    , get
    , getValue
    , index
    , length
    , textBytes
    )

import Control.Monad             (forM_)
import Control.Monad.Trans.Class (lift)
import Data.Function             ((&))

import qualified Data.ByteString.Char8 as BS8

main = do
    addressbook :: AddressBook ConstMsg <- getValue defaultLimit
    evalLimitT defaultLimit $ do
        number <- addressbook
            & get #people >>= index 0 >>= get #phones >>= index 0 >>= get #number
            >>= textBytes
        lift $ print number
