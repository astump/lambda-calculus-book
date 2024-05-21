open import lib
open import bool-relations as B

module Tau(V : Set)
          (_≃_ : V → V → 𝔹)
          (≃-equivalence : B.equivalence _≃_) where 

open import Tm V _≃_ ≃-equivalence

data τ(r : Rel Tm) : Rel Tm where
 τ-base : ∀ {t1 t2 : Tm} → r t1 t2 → τ r t1 t2
 τ-app1 : ∀ {t1 t1' t2 : Tm} → τ r t1 t1' → τ r (t1 · t2) (t1' · t2)
 τ-app2 : ∀ {t1 t2 t2' : Tm} → τ r t2 t2' → τ r (t1 · t2) (t1 · t2')
 τ-lam : ∀{v : V}{t t' : Tm} → τ r t t' → τ r (ƛ v t) (ƛ v t')
