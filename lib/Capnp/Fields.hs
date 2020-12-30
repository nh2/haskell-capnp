{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
module Capnp.Fields
    ( HasField
    , Field(..)
    , FieldLoc(..)
    , DataFieldLoc(..)
    ) where

import Data.Proxy           (Proxy)
import Data.Word
import GHC.OverloadedLabels (IsLabel)

import qualified Capnp.Repr as R

data FieldLoc (r :: R.Repr) where
    GroupField :: FieldLoc ('R.Ptr ('Just 'R.Struct))
    UnionField :: Word16 -> FieldLoc ('R.Ptr ('Just 'R.Struct))
    PtrField :: Word16 -> FieldLoc ('R.Ptr a)
    DataField :: DataFieldLoc a -> FieldLoc ('R.Data a)

data DataFieldLoc (sz :: R.DataSz) = DataFieldLoc
    { offset       :: Int
    , size         :: Proxy sz
    , defaultValue :: Word64
    }

data Field a b where
    Field :: R.HasRepr b r => FieldLoc r -> Field a b

class
    ( R.HasRepr a ('R.Ptr ('Just 'R.Struct))
    , IsLabel name (Field a b)
    ) => HasField name a b | a name -> b

