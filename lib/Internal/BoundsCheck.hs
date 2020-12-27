module Internal.BoundsCheck (checkIndex) where

import Control.Monad       (when)
import Control.Monad.Catch (MonadThrow (..))

import qualified Capnp.Errors as E

-- | @'checkIndex' index length@ checkes that 'index' is in the range
-- [0, length), throwing a 'BoundsError' if not.
checkIndex :: (Integral a, MonadThrow m) => a -> a -> m ()
{-# INLINE checkIndex #-}
checkIndex i len =
    when (i < 0 || i >= len) $
        throwM E.BoundsError
            { E.index = fromIntegral i
            , E.maxIndex = fromIntegral len
            }
