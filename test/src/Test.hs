-- {-# OPTIONS_GHC -fplugin=late-cc-plugin #-}
{-# OPTIONS_GHC -fplugin=LateCCPlugin #-}
{-# OPTIONS_GHC -ddump-simpl -ddump-to-file -ddump-ds #-}
{-# language MagicHash #-}
module Test where

import GHC.Exts

foo = {-# SCC foo #-} ()

bar x = {-# SCC bar #-} tagToEnum# x :: Bool

