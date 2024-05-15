open import lib
open import bool-relations

module Tm(V : Set)
         (_≃_ : V → V → 𝔹)
         (≃-equivalence : equivalence _≃_) where

data Tm : Set where
  Var : V → Tm
  _·_ : Tm → Tm → Tm
  ƛ : V → Tm → Tm

-- is the given variable free in the given term
freeIn : V → Tm → 𝔹
freeIn x (Var y) = (x ≃ y)
freeIn x (t · t') = (freeIn x t) || (freeIn x t')
freeIn x (ƛ y t) with x ≃ y
freeIn x (ƛ y t) | tt = ff
freeIn x (ƛ y t) | ff = freeIn x t

