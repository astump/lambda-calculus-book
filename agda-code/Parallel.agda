{-# OPTIONS --allow-unsolved-metas #-}
{- definition of parallel reduction, for proof of confluence.

   The definition here builds in alpha-equivalence for the lambda case. -}
open import lib
open import relations
open import diamond
open import VarInterface

module Parallel(vi : VI) where

open VI vi
open import Tm vi
open import Subst vi
open import Beta vi
open import Alpha vi 
open import Tau vi 

data ⇒ : Tm → Tm → Set where
  ⇒var : ∀{v : V} →
          var v ⟨ ⇒ ⟩ var v
  ⇒app : ∀{t1 t1' t2 t2' c : Tm} → 
          t1 ⟨ ⇒ ⟩ t1' →
          t2 ⟨ ⇒ ⟩ t2' →
          (t1' · t2') ⟨ 1r ∪ β ⟩ c →
          (t1 · t2) ⟨ ⇒ ⟩ c
  ⇒lam : ∀{x : V}{t1 t1' : Tm} →
           t1 ⟨ ⇒ ⟩ t1' →
           (ƛ x t1) ⟨ ⇒ ⟩ (ƛ x t1')

-- parallel reduction is reflexive
⇒refl : reflexive ⇒ 
⇒refl {var x} = ⇒var
⇒refl {t · t₁} = ⇒app ⇒refl ⇒refl (inj₁ refl)
⇒refl {ƛ x t} = ⇒lam ⇒refl 

↝β-⇒ : ↝β ⊆ ⇒
↝β-⇒ {(ƛ x t1) · t2}{a'} (τ-base p) = ⇒app ⇒refl ⇒refl (inj₂ p)
↝β-⇒ (τ-app1 x) = ⇒app (↝β-⇒ x) ⇒refl (inj₁ refl)
↝β-⇒ (τ-app2 x) = ⇒app ⇒refl (↝β-⇒ x) (inj₁ refl)
↝β-⇒ (τ-lam x) = ⇒lam (↝β-⇒ x) 

