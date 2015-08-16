{-# LANGUAGE OverloadedStrings #-}
module Main where

import Imports

import qualified Number
import qualified BCrypt
import qualified Hash
import qualified Poly1305
import qualified Salsa
import qualified ChaCha
import qualified ChaChaPoly1305
import qualified KAT_HMAC
import qualified KAT_PBKDF2
import qualified KAT_Curve25519
import qualified KAT_Ed25519
import qualified KAT_PubKey
import qualified KAT_Scrypt
-- symmetric cipher --------------------
import qualified KAT_AES
import qualified KAT_Blowfish
import qualified KAT_Camellia
import qualified KAT_DES
import qualified KAT_RC4
import qualified KAT_TripleDES
-- misc --------------------------------
import qualified KAT_AFIS

tests = testGroup "cryptonite"
    [ Number.tests
    , Hash.tests
    , testGroup "MAC"
        [ Poly1305.tests
        , KAT_HMAC.tests
        ]
    , KAT_Curve25519.tests
    , KAT_Ed25519.tests
    , KAT_PubKey.tests
    , testGroup "KDF"
        [ KAT_PBKDF2.tests
        , KAT_Scrypt.tests
        , BCrypt.tests
        ]
    , testGroup "block-cipher"
        [ KAT_AES.tests
        , KAT_Blowfish.tests
        , KAT_Camellia.tests
        , KAT_DES.tests
        , KAT_TripleDES.tests
        ]
    , testGroup "stream-cipher"
        [ KAT_RC4.tests
        , ChaCha.tests
        , ChaChaPoly1305.tests
        , Salsa.tests
        ]
    , KAT_AFIS.tests
    ]

main = defaultMain tests
