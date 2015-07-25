-- |
-- Module      : Crypto.PubKey.RSA.OAEP
-- License     : BSD-style
-- Maintainer  : Vincent Hanquez <vincent@snarc.org>
-- Stability   : experimental
-- Portability : Good
--
-- RSA OAEP mode
-- <http://en.wikipedia.org/wiki/Optimal_asymmetric_encryption_padding>
--
module Crypto.PubKey.RSA.OAEP
    (
      OAEPParams(..)
    , defaultOAEPParams
    -- * OAEP encryption
    , encryptWithSeed
    , encrypt
    -- * OAEP decryption
    , decrypt
    , decryptSafer
    ) where

import           Crypto.Hash
import           Crypto.Random.Types
import           Crypto.PubKey.RSA.Types
import           Crypto.PubKey.MaskGenFunction
import           Crypto.PubKey.RSA.Prim
import           Crypto.PubKey.RSA (generateBlinder)
import           Crypto.PubKey.Internal (and')
import           Data.ByteString

import           Crypto.Internal.ByteArray (ByteArrayAccess, ByteArray, Bytes)
import qualified Crypto.Internal.ByteArray as B

-- | Parameters for OAEP encryption/decryption
data OAEPParams hash seed output = OAEPParams
    { oaepHash       :: hash                         -- ^ Hash function to use.
    , oaepMaskGenAlg :: MaskGenAlgorithm seed output -- ^ Mask Gen algorithm to use.
    , oaepLabel      :: Maybe ByteString             -- ^ Optional label prepended to message.
    }

-- | Default Params with a specified hash function
defaultOAEPParams :: (ByteArray seed, ByteArray output, HashAlgorithm hash)
                  => hash
                  -> OAEPParams hash seed output
defaultOAEPParams hashAlg =
    OAEPParams { oaepHash         = hashAlg
               , oaepMaskGenAlg   = mgf1 hashAlg
               , oaepLabel        = Nothing
               }

-- | Encrypt a message using OAEP with a predefined seed.
encryptWithSeed :: (ByteArray seed, ByteArray message, ByteArray output, HashAlgorithm hash)
                => seed            -- ^ Seed
                -> OAEPParams hash seed output -- ^ OAEP params to use for encryption
                -> PublicKey       -- ^ Public key.
                -> message         -- ^ Message to encrypt
                -> Either Error output
encryptWithSeed seed oaep pk msg
    | k < 2*hashLen+2          = Left InvalidParameters
    | B.length seed /= hashLen = Left InvalidParameters
    | mLen > k - 2*hashLen-2   = Left MessageTooLong
    | otherwise                = Right $ ep pk em
    where -- parameters
          k          = public_size pk
          mLen       = B.length msg
          mgf        = oaepMaskGenAlg oaep
          labelHash  = hashWith (oaepHash oaep) (maybe B.empty id $ oaepLabel oaep)
          hashLen    = hashDigestSize (oaepHash oaep)

          -- put fields
          ps         = B.replicate (k - mLen - 2*hashLen - 2) 0
          db         = B.concat [B.convert labelHash, ps, B.pack [0x1], msg] :: Bytes
          dbmask     = mgf seed (k - hashLen - 1)
          maskedDB   = B.xor db dbmask
          seedMask   = mgf maskedDB hashLen
          maskedSeed = B.xor seed seedMask
          em         = B.concat [B.singleton 0x0, maskedSeed, maskedDB]

-- | Encrypt a message using OAEP
encrypt :: (ByteArray seed, ByteArray message, ByteArray output, HashAlgorithm hash, MonadRandom m)
        => OAEPParams hash seed output -- ^ OAEP params to use for encryption.
        -> PublicKey       -- ^ Public key.
        -> message         -- ^ Message to encrypt
        -> m (Either Error output)
encrypt oaep pk msg = do
    seed <- getRandomBytes hashLen
    return (encryptWithSeed seed oaep pk msg)
  where
    hashLen    = hashDigestSize (oaepHash oaep)

-- | un-pad a OAEP encoded message.
--
-- It doesn't apply the RSA decryption primitive
unpad :: (ByteArray seed, ByteArray message, ByteArray output, HashAlgorithm hash)
      => OAEPParams hash seed output -- ^ OAEP params to use
      -> Int             -- ^ size of the key in bytes
      -> message         -- ^ encoded message (not encrypted)
      -> Either Error output
unpad oaep k em
    | paddingSuccess = Right msg
    | otherwise      = Left MessageNotRecognized
    where -- parameters
          mgf        = oaepMaskGenAlg oaep
          labelHash  = B.convert $ hashWith (oaepHash oaep) (maybe B.empty id $ oaepLabel oaep)
          hashLen    = hashDigestSize (oaepHash oaep)
          -- getting em's fields
          (pb, em0)  = B.splitAt 1 em
          (maskedSeed,maskedDB) = B.splitAt hashLen em0
          seedMask   = mgf (B.convert maskedDB) hashLen
          seed       = B.xor maskedSeed seedMask
          dbmask     = mgf seed (k - hashLen - 1)
          db         = B.xor maskedDB dbmask
          -- getting db's fields
          (labelHash',db1) = B.splitAt hashLen db
          (_,db2)    = B.span (== 0) db1
          (ps1,msg)  = B.splitAt 1 db2

          paddingSuccess = and' [ labelHash' == labelHash -- no need for constant eq
                                , ps1        == B.replicate 1 0x1
                                , pb         == B.replicate 1 0x0
                                ]

-- | Decrypt a ciphertext using OAEP
--
-- When the signature is not in a context where an attacker could gain
-- information from the timing of the operation, the blinder can be set to None.
--
-- If unsure always set a blinder or use decryptSafer
decrypt :: (ByteArray seed, ByteArray ciphertext, ByteArray output, HashAlgorithm hash)
        => Maybe Blinder   -- ^ Optional blinder
        -> OAEPParams hash seed output -- ^ OAEP params to use for decryption
        -> PrivateKey      -- ^ Private key
        -> ciphertext      -- ^ Cipher text
        -> Either Error output
decrypt blinder oaep pk cipher
    | B.length cipher /= k = Left MessageSizeIncorrect
    | k < 2*hashLen+2      = Left InvalidParameters
    | otherwise            = unpad oaep (private_size pk) $ dp blinder pk cipher
    where -- parameters
          k          = private_size pk
          hashLen    = hashDigestSize (oaepHash oaep)

-- | Decrypt a ciphertext using OAEP and by automatically generating a blinder.
decryptSafer :: (ByteArray seed, ByteArray ciphertext, ByteArray output, HashAlgorithm hash, MonadRandom m)
             => OAEPParams hash seed output -- ^ OAEP params to use for decryption
             -> PrivateKey -- ^ Private key
             -> ciphertext -- ^ Cipher text
             -> m (Either Error output)
decryptSafer oaep pk cipher = do
    blinder <- generateBlinder (private_n pk)
    return (decrypt (Just blinder) oaep pk cipher)
