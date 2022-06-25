{-# OPTIONS --exact-split --type-in-type --rewriting --two-level --without-K #-}

module HOTT.Pi.Transport where

-- For some reason, the rewrites for tr→ and tr← make the compilation
-- of Ulift unfeasibly slow.  Because of Agda bug
-- https://github.com/agda/agda/issues/4343, this happens even if
-- Ulift doesn't import Tr as long as Tr was imported by some *other*
-- file before Ulift is compiled.  So we compile Ulift first.
open import HOTT.Pi.Transport.Utr public
open import HOTT.Pi.Transport.Ulift public

open import HOTT.Pi.Transport.Tr public
open import HOTT.Pi.Transport.Lift public
