open import lib
open import bool-relations

module Subst(V : Set)
            (_≃_ : V → V → 𝔹)
            (≃-equivalence : equivalence _≃_) where 

open import Tm V _≃_ ≃-equivalence

-- a single substitution, requesting replacement of one variable by one term
Subst1 : Set
Subst1 = (V × Tm)

Subst : Set
Subst = 𝕃 Subst1

-- would applying the given Subst1 to the given Tm avoid variable capture?
subst1ok : Subst1 → Tm → 𝔹
subst1ok (x , t) (Var _) = tt
subst1ok s (t1 · t2) = subst1ok s t1 && subst1ok s t2
subst1ok (x , t) (ƛ y t') = ~ freeIn y t && subst1ok (x , t) t'

substOk : Subst → Tm → 𝔹
substOk ss t = list-all (λ s → subst1ok s t) ss

-- find the first binding, if there is one, of the variable y in the substitution s
lookup : Subst → V → maybe Tm
lookup s y = maybe-map snd (find (λ p → _≃_ y (fst p)) s)

-- apply the given substitution simultaneously to the given term
subst : Subst → Tm → Tm
subst s (Var y) with lookup s y
subst s (Var y) | nothing = Var y
subst s (Var y) | just t = t
subst s (t1 · t2) = subst s t1 · subst s t2
subst s (ƛ x t) = ƛ x (subst (filter (λ p → ~ (fst p) ≃ x) s) t)

subst1 : Subst1 → Tm → Tm
subst1 s t = subst [ s ] t