{-# LANGUAGE ConstraintKinds  #-}
{-# LANGUAGE DataKinds        #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}
module Capnp.Parsable
    ( Parsable(..)
    , ReadCtx
    , RWCtx
    ) where

import qualified Capnp.Message2       as M
import           Capnp.Mutability
import           Capnp.TraversalLimit (MonadLimit)
import           Control.Monad.Catch  (MonadThrow)

-- | Type (constraint) synonym for the constraints needed for most read
-- operations.
type ReadCtx m mut = (M.Message m mut, MonadThrow m, MonadLimit m)

-- | Synonym for ReadCtx + WriteCtx
type RWCtx m s = (ReadCtx m ('Mut s), M.WriteCtx m s)

class Parsable (f :: Mutability -> *) where
    data Parsed f

    decode :: ReadCtx m mut => f mut -> m (Parsed f)
    encode :: RWCtx m s => M.Msg ('Mut s) -> Parsed f -> m (f ('Mut s))

instance Parsable (Phantom a) where
    newtype Parsed (Phantom a) = Parsed a

    decode (Phantom x) = pure $ Parsed x
    encode _ (Parsed x) = pure $ Phantom x
