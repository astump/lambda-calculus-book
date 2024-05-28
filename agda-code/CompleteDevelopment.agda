{- definition of complete development (as a relation).

   This definition is just a specialization of the definition of parallel reduction. -}
open import lib
open import relations
open import VarInterface

module CompleteDevelopment(vi : VI) where

open VI vi
open import Tm vi
open import Subst vi
open import Beta vi
open import Alpha vi 
open import Parallel vi 

data ⇒cd : Tm → Tm → Set where
  ⇒cd-var : ∀{v : V} →
            var v ⟨ ⇒cd ⟩ var v
  ⇒cd-app : ∀{t1 t1' t2 t2' c : Tm} → 
             t1 ⟨ ⇒cd ⟩ t1' →
             t2 ⟨ ⇒cd ⟩ t2' →
             (t1' · t2') ⟨ β ⟩ c →
             (t1 · t2) ⟨ ⇒cd ⟩ c
  ⇒cd-lam : ∀{x : V}{t1 t1' c : Tm} →
             t1 ⟨ ⇒cd ⟩ t1' →
             (ƛ x t1') ⟨ 1r ∪ α ⟩ c →
             (ƛ x t1) ⟨ ⇒cd ⟩ c

⇒cd-⇒ : ⇒cd ⊆ ⇒ 
⇒cd-⇒ ⇒cd-var = ⇒var
⇒cd-⇒ (⇒cd-app d d' b) = ⇒app (⇒cd-⇒ d) (⇒cd-⇒ d') (inj₂ b)
⇒cd-⇒ (⇒cd-lam d b) = ⇒lam (⇒cd-⇒ d) b