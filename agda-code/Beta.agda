open import lib
open import bool-relations

module Beta(V : Set)
           (_≃_ : V → V → 𝔹)
           (≃-equivalence : equivalence _≃_) where 

open import Tm V _≃_ ≃-equivalence
open import Subst V _≃_ ≃-equivalence

Beta : Tm → Tm → Set
Beta ((ƛ x t1) · t2) t' =
 let s = [ (x , t2) ] in
   substOk s t1 ≡ tt ∧
   t' ≡ subst s t1
Beta _ _ = ⊥