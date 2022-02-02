{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.MemoTrie
import GHC.Generics (Generic)

data Color
  = RGB Int Int Int
  | NamedColor String
  deriving stock (Generic)
  deriving (HasTrie) via MemoTrieGenerics Color

runColor (RGB r g b) = r + g + b
runColor (NamedColor s) = length [1 .. 10e7]

runColorMemoized = memo runColor

main =
  do
    putStrLn "first call (should take a few seconds): "
    print $ runColorMemoized (NamedColor "")
    putStrLn "cached call (should be instantaneous): "
    print $ runColorMemoized (NamedColor "")
