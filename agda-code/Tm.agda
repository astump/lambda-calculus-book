open import lib
open import bool-relations
open import VarInterface

module Tm(vi : VI) where

open VI vi

data Tm : Set where
  var : (x : V) → Tm
  _·_ : (t : Tm) → (t' : Tm) → Tm
  ƛ : (x : V) → (t : Tm) → Tm

-- is the given variable free in the given term
freeIn : V → Tm → 𝔹
freeIn x (var y) = (x ≃ y)
freeIn x (t · t') = (freeIn x t) || (freeIn x t')
freeIn x (ƛ y t) with x ≃ y
freeIn x (ƛ y t) | tt = ff
freeIn x (ƛ y t) | ff = freeIn x t

