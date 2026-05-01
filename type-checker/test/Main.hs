module Main where

import Test.Hspec
import qualified TypeTest


main :: IO ()
main = hspec $ do
    TypeTest.spec



