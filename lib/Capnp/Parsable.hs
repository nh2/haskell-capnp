{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds       #-}
{-# LANGUAGE TypeFamilies    #-}
module Capnp.Parsable
    ( Parsable(..)
    , ReadCtx
    ) where

import qualified Capnp.Message2       as M
import           Capnp.Mutability
import           Capnp.TraversalLimit (MonadLimit)
import           Control.Monad.Catch  (MonadThrow)

-- | Type (constraint) synonym for the constraints needed for most read
-- operations.
type ReadCtx m mut = (M.Message m mut, MonadThrow m, MonadLimit m)

class Parsable (f :: Mutability -> *) where
    data Parsed f

    decode :: ReadCtx m mut => f mut -> m (Parsed f)
    encode :: M.WriteCtx m s => M.Msg ('Mut s) -> Parsed f -> m (f ('Mut s))
