-- |
-- Module      : Crypto.PubKey.RSA.PSS
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : Good
--
module Crypto.PubKey.RSA.PSS
    ( PSSParams(..)
    , defaultPSSParams
    , defaultPSSParamsSHA1
    -- * Sign and verify functions
    , signWithSalt
    , sign
    , signSafer
    , verify
    ) where

import           Crypto.Random.Types
import           Crypto.PubKey.RSA.Types
import           Crypto.PubKey.RSA.Prim
import           Crypto.PubKey.RSA (generateBlinder)
import           Crypto.PubKey.MaskGenFunction
import           Crypto.Hash
import           Data.Bits (shiftR, (.&.))
import           Data.Word

import           Crypto.Internal.ByteArray (ByteArray, Bytes)
import qualified Crypto.Internal.ByteArray as B

-- | Parameters for PSS signature/verification.
data PSSParams hash seed output = PSSParams
    { pssHash         :: hash             -- ^ Hash function to use
    , pssMaskGenAlg   :: MaskGenAlgorithm seed output -- ^ Mask Gen algorithm to use
    , pssSaltLength   :: Int              -- ^ Length of salt. need to be <= to hLen.
    , pssTrailerField :: Word8            -- ^ Trailer field, usually 0xbc
    }

-- | Default Params with a specified hash function
defaultPSSParams :: (ByteArray seed, ByteArray output, HashAlgorithm hash)
                 => hash
                 -> PSSParams hash seed output
defaultPSSParams hashAlg =
    PSSParams { pssHash         = hashAlg
              , pssMaskGenAlg   = mgf1 hashAlg
              , pssSaltLength   = hashDigestSize hashAlg
              , pssTrailerField = 0xbc
              }

-- | Default Params using SHA1 algorithm.
defaultPSSParamsSHA1 :: (ByteArray seed, ByteArray output) => PSSParams SHA1 seed output
defaultPSSParamsSHA1 = defaultPSSParams SHA1

-- | Sign using the PSS parameters and the salt explicitely passed as parameters.
--
-- the function ignore SaltLength from the PSS Parameters
signWithSalt :: (ByteArray seed, ByteArray message, ByteArray output, HashAlgorithm hash)
             => seed                       -- ^ Salt to use
             -> Maybe Blinder              -- ^ optional blinder to use
             -> PSSParams hash seed output -- ^ PSS Parameters to use
             -> PrivateKey                 -- ^ RSA Private Key
             -> message                    -- ^ Message to sign
             -> Either Error output
signWithSalt salt blinder params pk m
    | k < hashLen + saltLen + 2 = Left InvalidParameters
    | otherwise                 = Right $ dp blinder pk em
    where mHash    = B.convert $ hashWith (pssHash params) m
          k        = private_size pk
          dbLen    = k - hashLen - 1
          saltLen  = B.length salt
          hashLen  = hashDigestSize (pssHash params)
          pubBits  = private_size pk * 8 -- to change if public_size is converted in bytes

          m'       = B.concat [B.replicate 8 0,mHash,salt] :: Bytes
          h        = B.convert $ hashWith (pssHash params) m'
          db       = B.concat [B.replicate (dbLen - saltLen - 1) 0,B.singleton 1,salt] :: Bytes
          dbmask   = (pssMaskGenAlg params) h dbLen
          maskedDB = normalizeToKeySize pubBits $ B.xor db dbmask
          em       = B.concat [maskedDB, h, B.singleton (pssTrailerField params)]

-- | Sign using the PSS Parameters
sign :: (ByteArray seed, ByteArray message, ByteArray output, HashAlgorithm hash, MonadRandom m)
     => Maybe Blinder              -- ^ optional blinder to use
     -> PSSParams hash seed output -- ^ PSS Parameters to use
     -> PrivateKey                 -- ^ RSA Private Key
     -> message                    -- ^ Message to sign
     -> m (Either Error output)
sign blinder params pk m = do
    salt <- getRandomBytes (pssSaltLength params)
    return (signWithSalt salt blinder params pk m)

-- | Sign using the PSS Parameters and an automatically generated blinder.
signSafer :: (ByteArray seed, ByteArray message, ByteArray output, HashAlgorithm hash, MonadRandom m)
          => PSSParams hash seed output -- ^ PSS Parameters to use
          -> PrivateKey                 -- ^ private key
          -> message                    -- ^ message to sign
          -> m (Either Error output)
signSafer params pk m = do
    blinder <- generateBlinder (private_n pk)
    sign (Just blinder) params pk m

-- | Verify a signature using the PSS Parameters
verify :: (ByteArray seed, ByteArray message, ByteArray sig, HashAlgorithm hash)
       => PSSParams hash seed sig
                     -- ^ PSS Parameters to use to verify,
                     --   this needs to be identical to the parameters when signing
       -> PublicKey  -- ^ RSA Public Key
       -> message    -- ^ Message to verify
       -> sig        -- ^ Signature
       -> Bool
verify params pk m s
    | public_size pk /= B.length s        = False
    | lastEm /= pssTrailerField params    = False
    | not (B.all (== 0) ps0)              = False
    | b1 /= B.singleton 1                 = False
    | otherwise                           = h == B.convert h'
        where -- parameters
              hashLen   = hashDigestSize (pssHash params)
              dbLen     = public_size pk - hashLen - 1
              pubBits   = public_size pk * 8 -- to change if public_size is converted in bytes
              -- unmarshall fields
              em        = ep pk s
              lastEm    = B.index em (B.length em - 1)
              maskedDB  = B.take (B.length em - hashLen - 1) em
              h         = B.convert $ B.take hashLen $ B.drop (B.length maskedDB) em
              dbmask    = (pssMaskGenAlg params) h dbLen
              db        = normalizeToKeySize pubBits $ B.xor maskedDB dbmask :: Bytes
              (ps0,z)   = B.span (/= 1) db
              (b1,salt) = B.splitAt 1 z
              mHash     = B.convert $ hashWith (pssHash params) m
              m'        = B.concat [B.replicate 8 0,mHash,salt] :: Bytes
              h'        = hashWith (pssHash params) m'


normalizeToKeySize :: ByteArray a => Int -> a -> a
normalizeToKeySize bits bs = B.pack (normalize (B.unpack bs))
  where
    normalize []     = [] -- very unlikely
    normalize (x:xs) = x .&. mask : xs
        where mask = if sh > 0 then 0xff `shiftR` (8-sh) else 0xff
              sh   = ((bits-1) .&. 0x7)
